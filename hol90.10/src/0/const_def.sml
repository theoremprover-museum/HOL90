(* ===================================================================== *)
(* FILE          : const_def.sml                                         *)
(* DESCRIPTION   : Three variants on the principle of definition. The    *)
(*                 third argument to new_infix_definition is the         *)
(*                 precedence. Translated from hol88, except for the     *)
(*                 precedence stuff.                                     *)
(*                                                                       *)
(* AUTHOR        : (c) Mike Gordon, University of Cambridge              *)
(* TRANSLATOR    : Konrad Slind, University of Calgary                   *)
(* DATE          : September 11, 1991                                    *)
(* ===================================================================== *)


functor CONST_DEF ((* structure Lib : Lib_sig *)
		   structure Theory : Theory_sig
                   structure Dsyntax : Dsyntax_sig
                   structure Lexis : Lexis_sig
                   structure Const_spec : Const_spec_sig
                   sharing
                     Dsyntax.Term = Theory.Thm.Term
                   and
                     Const_spec.Theory = Theory) : Const_def_sig =
struct
structure Theory = Theory
open Theory;
open Thm.Term;
open Dsyntax;
open Lib;

fun CONST_DEF_ERR{function,message} = 
    Exception.HOL_ERR{origin_structure = "Const_def",
		      origin_function = function,
		      message = message}

infix 3 -->
fun (X --> Y) = Type.mk_type{Tyop = "fun", Args = [X,Y]};

local
fun check_varstruct tm =
   if (is_var tm)
   then [tm]
   else let val {fst,snd} = dest_pair tm
            val l1 = check_varstruct fst
            and l2 = check_varstruct snd
        in if (null_intersection l1 l2)
           then (l1@l2)
           else raise CONST_DEF_ERR{function = "check_varstruct",
                                    message = "bad varstruct"}
        end handle _ => raise CONST_DEF_ERR{function = "check_varstruct",
                                            message = "bad varstruct"}
in
fun check_lhs tm =
   if (is_var tm)
   then [tm]
   else if (is_const tm)
        then raise CONST_DEF_ERR{function = "check_lhs",
                                 message = "attempt to redefine constant"}
        else if (is_comb tm)
             then let val {Rator,Rand} = dest_comb tm
                      val l1 = check_lhs Rator
                      and l2 = check_varstruct Rand
                  in if (null_intersection l1 l2)
                     then (l1@l2)
                     else raise CONST_DEF_ERR{function = "check_lhs",
                                              message = "bad lhs in def"}
                  end
             else raise CONST_DEF_ERR{function = "check_lhs",
                                      message = "bad lhs in def"}
end;



(******************************************************************
 * if `C ... = (...:ty)` then  (get_type `C ...` ty) gives the
 *  type of C.
 *
 ******************************************************************)
fun get_type tm rightty = 
   if (is_var tm)
   then rightty
   else if (is_comb tm)
        then let val {Rator,Rand} = dest_comb tm
             in get_type Rator (type_of Rand --> rightty)
             end
        else raise CONST_DEF_ERR{function="get_type",message="bad lhs in def"};


(* The derived rule
 *
 *   DEF_EXISTS_RULE : term -> thm 
 *
 * proves that a function defined by a definitional equation exists.
 * The implementation below uses mk_thm, but this will be changed eventually.
 *****************************************************************************)
fun DEF_EXISTS_RULE tm =
 let val (vars,body) = strip_forall tm
     val (eq as {lhs,rhs}) = dest_eq body handle _ => 
                   raise CONST_DEF_ERR{function = "DEF_EXISTS_RULE",
                                    message = "definition is not an equation"}
     val lhsvars  = check_lhs lhs
     and ty       = get_type lhs (Term.type_of rhs)
     and rhsvars  = Term.free_vars rhs
 in
 if not(set_eq (intersect lhsvars rhsvars) rhsvars)
 then raise(CONST_DEF_ERR{function = "DEF_EXISTS_RULE",
			  message = "unbound var in rhs"})
 else if (mem (Portable.List.hd lhsvars) rhsvars)
      then raise(CONST_DEF_ERR{function = "DEF_EXISTS_RULE",
                               message = "recursive definitions not allowed"})
      else let val name = #Name(dest_var(Portable.List.hd lhsvars))
               and v    = Portable.List.hd lhsvars
           in
           if not(Portable.List.null(set_diff (Term.type_vars_in_term rhs) 
                                              (Term.type_vars_in_term v)))
           then raise CONST_DEF_ERR{function = "DEF_EXISTS_RULE",
                message = (Type.dest_vartype
                              (Portable.List.hd
                                  (set_diff(type_vars_in_term rhs)
                                           (type_vars_in_term v)))
                          ^" an unbound type variable in definition")}
           else if not(Lexis.allowed_term_constant name)
                then raise CONST_DEF_ERR{function = "DEF_EXISTS_RULE",
                    message=(concat name " is not allowed as a constant name")}
                else let val thm = Thm.mk_drule_thm([],mk_exists{Bvar = v,
                        Body=list_mk_forall
                                (union vars (Portable.List.tl lhsvars),
				 mk_eq eq)})
                     in
                     Thm.note (Thm.STEP{Name="DEFEXISTSRULE", Thm=thm,
					Just=[Thm.JA_TERM tm]}, thm)
                     end
           end
 end;

local
fun new_gen_definition{name,def,fixity} =
   let val def_thm = DEF_EXISTS_RULE def
       val cname = (#Name o dest_var o #Bvar o dest_exists o Thm.concl) def_thm
   in Const_spec.new_specification
                 {name = name,
                  consts = [{fixity = fixity, const_name = cname}],
                  sat_thm = def_thm}
   end
in
fun new_definition(name,def) = 
    new_gen_definition{name = name, fixity = Prefix, def = def}
fun new_infix_definition(name,def,prec) = 
    new_gen_definition{name = name, fixity = Infix prec, def = def}
fun new_binder_definition(name,def) = 
    new_gen_definition{name = name, fixity = Binder, def = def}
end;

end; (* CONST_DEF *)
