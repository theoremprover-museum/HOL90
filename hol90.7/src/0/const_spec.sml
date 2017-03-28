(* ===================================================================== *)
(* FILE          : const_spec.sml                                        *)
(* DESCRIPTION   : Implements the principle of constant specification.   *)
(*                 Translated from hol88.                                *)
(*                                                                       *)
(* AUTHOR        : (c) Mike Gordon, University of Cambridge              *)
(* TRANSLATOR    : Konrad Slind, University of Calgary                   *)
(* DATE          : September 11, 1991                                    *)
(* ===================================================================== *)


functor CONST_SPEC (structure Theory : Theory_sig
                    structure Dsyntax : Dsyntax_sig
                    structure Lexis : Lexis_sig
                    sharing
                      Dsyntax.Term = Theory.Thm.Term) : Const_spec_sig =
struct
structure Theory = Theory;

open Theory;
open Dsyntax;
open Thm.Term;


fun CONST_SPEC_ERR s = HOL_ERR{origin_structure = "Const_spec",
			       origin_function = "check_specification",
			       message = s};

(* Added on 25/11/1988 for HOL88:
  new_specification "flag" "name" "C" |- ?x. ... x ...
  declares C as a new constant and then does
  new_axiom("name", `... C ...`)  "flag" must be one of "constant",
  "infix" or "binder" and determines the syntactic status of C.
  To avoid Roger Jones type problems, it is required that there be
  no type variables in types of subterms of

     `... C ...`
  that do not occur in the type of C. This rules out, for example,
 
     new_specification(tok, "Wonk", |- ?b:bool. b = !x y:*. x=y)

  The specification above was amended on 8/2/89 to the following:

     new_specification
      name 
      ["flag1","C1"; ... ; "flagn,Cn"] 
      |- ?x1 ... xn. ... x1 ... xn ...
  declares C1, ... ,Cn as a new constants and then does
  new_axiom("name", `... C1 ... Cn ...`);  "flagi" must be one of "constant",
  "infix" or "binder" and determines the syntactic status of Ci.
  To avoid Roger Jones type problems, it is required that there be no 
  type variables in types of subterms of  `... C1 ... Cn ...` that do not 
  occ	ur in the types of any Ci (1 <= i <= n). This rules out, for example,
  
     new_specification
      ("Wonk_DEF", ["constant","Wonk"], |- ?b:bool. b = !x y:*. x=y)

  which would define a constant `Wonk` of type `:bool` by
  the inconsistent axiom:

     |- Wonk = !x y:*. x=y

(Actually, it doesn't do an "new_axiom", but a "store_definition" -KLS)
*)

fun is_infix_type ty =
   let val {Tyop = "fun",Args = [_,ty2]} = Type.dest_type ty
       val {Tyop = "fun", Args = [_,_]} = Type.dest_type ty2
   in
   true
   end
   handle _ => false;

fun is_binder_type ty =
   let val {Tyop = "fun", Args = [ty1,_]} = Type.dest_type ty
       val {Tyop = "fun", Args = [_,_]} = Type.dest_type ty1
   in
   true
   end
   handle _ => false;

(* Auxiliary function to strip off n quantifiers *)
fun n_strip_quant dest_fn 0 t = ([],t) |
    n_strip_quant dest_fn n t =
     let val {Bvar, Body} = dest_fn t
         val (l,t'') = n_strip_quant dest_fn (n-1) Body
     in
     (Bvar::l, t'')
     end;

(* Auxiliary function to check the arguments to new_specification;
  fails (with useful message) or returns 
  ([`x1`;...;`xn`], `... x1 ... xn ...`)

deleted "defname" from arguments, as it is not used -- KLS
*)
fun check_specification flag_name_prec_list th =
(if not(Theory.draft_mode())
 then raise(CONST_SPEC_ERR "not in draft mode")
 else
 if not(null(Thm.hyp th))
 then raise CONST_SPEC_ERR"no assumptions to theorem allowed in specifications"
 else 
 if not(null(Term.free_vars(Thm.concl th)))
 then raise(CONST_SPEC_ERR 
               (itlist (fn t => fn s => "\""^(#Name(dest_var t))^"\" "^s)
                       (Term.free_vars(Thm.concl th))
                       "is (are) unbound variable(s) in specification"))
 else map (fn {const_name,...} =>
             if (Theory.is_constant const_name)
             then raise CONST_SPEC_ERR 
                       ("attempt to specify an existing constant: "^const_name)
             else 
             if not(Lexis.allowed_term_constant const_name)
             then raise CONST_SPEC_ERR 
                             (const_name^ " is not an allowable constant name")
             else ())
          (flag_name_prec_list :{fixity:Term.fixity,const_name:string} list);

 let val (vars,body) = n_strip_quant dest_exists 
                                     (length flag_name_prec_list) 
                                     (Thm.concl th)
                       handle _ => 
                       raise CONST_SPEC_ERR
                                   "too few existentially quantified variables"
 in
 (map (fn var => 
         if not(null(set_diff (Term.type_vars_in_term body) 
                              (Term.type_vars_in_term var)))
         then raise(CONST_SPEC_ERR
                       (itlist (fn vty => fn s => 
                                 ((Term.Type.dest_vartype vty)^" "^s))
                              (set_diff (Term.type_vars_in_term body) 
                                        (Term.type_vars_in_term var))
                              ("should occur in the type of "^
                                (#Name(dest_var var)))))
         else ())
      vars;
  map2 (fn {fixity = Term.Infix _,...} => (fn var =>
             if (not(is_infix_type(Term.type_of var)))
             then raise CONST_SPEC_ERR (#Name(dest_var var)^
                                        " doesn't have infix type")
             else ())
         | {fixity = Term.Binder, ...} => (fn var =>
             if (not(is_binder_type(Term.type_of var)))
             then raise CONST_SPEC_ERR (#Name(dest_var var)^
                                        " doesn't have binder type")
             else ())
         | _ => fn _ => ())
       flag_name_prec_list vars;
  (vars,body)
 )
 end);


fun new_specification{name, consts, sat_thm} =
   let val (vars,body) = check_specification consts sat_thm
   in
   ( map2 (fn {fixity = Term.Prefix,const_name} => (fn var => 
                 Theory.new_constant{Name=const_name,Ty=Term.type_of var})
            | {fixity = Term.Infix prec,const_name} => (fn var =>
                 Theory.new_infix{Name=const_name,Ty = Term.type_of var,
                                  Prec= prec})
            | {fixity = Term.Binder,const_name,...} => (fn var => 
                 Theory.new_binder{Name=const_name,Ty=Term.type_of var}))
          consts vars;
     Theory.store_definition
        (name, Term.subst (map2 (fn{const_name,...} => fn var => 
                               (var |-> mk_const{Name = const_name,
                                                 Ty = Term.type_of var}))
                           consts vars)
                     body)
   )
   end;
end; (* CONST_SPEC *)
