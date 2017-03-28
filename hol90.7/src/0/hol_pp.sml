(* ===================================================================== *)
(* FILE          : hol_pp.sml                                            *)
(* DESCRIPTION   : Implements prettyprinters (pratty prodders) for HOL   *)
(*                 terms and types. Varstructs are particularly horrible.*)
(*                                                                       *)
(* AUTHOR        : Konrad Slind, University of Calgary                   *)
(* DATE          : August 26, 1991                                       *)
(* REVISED       : To accomodate ppstreams, November 12, 1992            *)
(* ===================================================================== *)


functor HOL_PP(structure Lexis : Lexis_sig
               structure Symtab  : Symtab_sig
               structure Dsyntax : Dsyntax_sig
               structure Globals : Globals_sig
               sharing
                 Symtab.Term = Dsyntax.Term) : Hol_pp_sig =
struct
structure Term = Symtab.Term;
open Term;
open Term.Type;

val INCONSISTENT = PP.INCONSISTENT
val CONSISTENT = PP.CONSISTENT
val with_ppstream = PP.with_ppstream;

fun HOL_PP_ERR{function,message} = HOL_ERR{origin_structure = "Hol_pp",
					   origin_function = function,
					   message = message}
val space = " "
val comma = ","
val dollar = "$";


(* Support for minimizing the number of brackets *)
datatype gravity = INFINITY | GRAPP | DELIM | NADA | PREC of int
fun gravity_geq INFINITY _ = true
  | gravity_geq _ INFINITY = false
  | gravity_geq GRAPP _ = true
  | gravity_geq _ GRAPP = false
  | gravity_geq (PREC n) (PREC m) = (n >= m)
  | gravity_geq (PREC _) _ = true
  | gravity_geq _ (PREC _) = false
  | gravity_geq DELIM _ = true
  | gravity_geq _ DELIM = false
  | gravity_geq _ NADA = true

fun add_lparen ppstrm grav1 grav2 =
   if (gravity_geq grav1 grav2)
   then PP.add_string ppstrm "("
   else ()
fun add_rparen ppstrm grav1 grav2 =
   if (gravity_geq grav1 grav2)
   then PP.add_string ppstrm ")"
   else ()

(* Print a list of items.
 *
 *     pfun = print_function
 *     dfun = delim_function
 *     bfun = break_function
 ****)
fun pr_list_to_ppstream ppstrm pfun dfun bfun L =
   let fun pr [] = ()
         | pr [i] = pfun ppstrm i
         | pr (i::rst) = ( pfun ppstrm i; dfun ppstrm ; bfun ppstrm ; pr rst )
   in
   pr L
   end;

fun pr_list pfun dfun bfun L =
   let fun pr [] = ()
         | pr [i] = pfun i
         | pr (i::rst) = ( pfun i; dfun() ; bfun() ; pr rst )
   in
   pr L
   end;


(*********  Type Pretty Printer *********)

fun ty_prec "fun" = PREC 0
  | ty_prec "sum" = PREC 1
  | ty_prec "prod"  = PREC 2
  | ty_prec _ = raise HOL_PP_ERR{function = "ty_prec",message = "bogus infix"};

fun is_infix_tyop "fun" = true
  | is_infix_tyop "sum" = true
  | is_infix_tyop "prod" = true
  | is_infix_tyop _ = false;

fun infix_to_string "fun" = "->"
  | infix_to_string "sum" = "+"
  | infix_to_string "prod" = "#"
  | infix_to_string _ = raise HOL_PP_ERR{function = "infix_to_string",
					 message = "bogus infix"};

fun strip_infix_ty str (ty as Tyapp{Tyop,Args = [ty1,ty2]}) L =
      if (str = Tyop)
      then strip_infix_ty str ty2 (ty1::L)
      else rev(ty::L)
  | strip_infix_ty str ty L = rev (ty::L);


(* Returns a list of strings and a type *)
fun strip_singleton_ty (Tyapp{Tyop,Args = [ty]}) L =
                      strip_singleton_ty ty (Tyop::L)
  | strip_singleton_ty ty L = (ty,L)

fun pr_type ppstrm =
   let val {add_string,add_break,begin_block,end_block,...} = 
              with_ppstream ppstrm
       val add_lparen = add_lparen ppstrm
       val add_rparen = add_rparen ppstrm
       fun pr_ty _ _ 0 = add_string "..."
         | pr_ty(Utv x) _ _ = add_string x
         | pr_ty(Stv i) _ _ = add_string("?"^Lib.int_to_string i)
         | pr_ty(Tyc str) _ _ = add_string str 
         | pr_ty(Link(ref ty)) grav n = pr_ty ty grav n
         | pr_ty(ty as Tyapp{Tyop,Args}) grav n = 
             ( begin_block INCONSISTENT 0;
               if (is_infix_tyop Tyop)
               then let val prec = ty_prec Tyop
                    in
                    ( add_lparen grav prec;
                      pr_list
		          (fn ty => pr_ty ty prec (n-1))
                          (fn () => 
                             if (!(#infix_at_front(Globals.pp_flags)))
                             then add_break(1,0)
                             else add_string (space^infix_to_string Tyop))
			  (fn () => 
                             if (!(#infix_at_front(Globals.pp_flags)))
                             then add_string (infix_to_string Tyop^space)
                             else add_break(1,0))
			  (strip_infix_ty Tyop ty []);
                      add_rparen grav prec
                    )
                    end
               else if (length Args = 1)
                    then let val (ty,L) = strip_singleton_ty ty []
                         in
                         ( add_lparen grav GRAPP;
                           pr_ty ty GRAPP (n-1);
                           add_break(1,0);
                           pr_list
                                (fn s => add_string s) 
				(fn () => ())
				(fn () => add_break(1,0))
				L;
                           add_rparen grav GRAPP
                         )
                         end
                    else ( add_lparen grav GRAPP;
                           add_string "(";
                           pr_list 
                              (fn ty => pr_ty ty NADA (n-1)) 
			      (fn () => add_string ",")
			      (fn () => add_break(0,0))
                              Args;
                           add_string ")";
                           add_string Tyop;
                           add_rparen grav GRAPP
                         );
               end_block()
             )
   in  pr_ty
   end;
       
       
fun pp_type ppstrm ty n = pr_type ppstrm ty NADA n
       


(************ Term Pretty Printer ************************************)

(* alphanumeric binders have a space between them and the variable:
 * otherwise we get the following buggy prettyprint reported by Paul 
 * Curzon (LOCAL is a binder)
 *
 *     LOCALx. <body>
 ********)
fun pad_binder s = if (Lexis.ok_symbolic s) then s else s^space;

(* Breaking terms down *)

local
fun strip tm n = 
   if (Dsyntax.is_neg tm) 
   then strip (Dsyntax.dest_neg tm) (n+1)
   else (n,tm)
in
fun strip_neg tm = strip tm 0
end;

local 
fun dest (tm as Comb{Rator = Const{Name,...}, Rand = Abs{Bvar,Body}}) s L =
        if (Name = s)
        then dest Body s (Bvar::L)
        else (rev L,tm)
  | dest tm _ L = (rev L,tm)
in
fun strip_binder_vars (tm as Comb{Rator=Const{Name,...},Rand=Abs{Bvar,Body}}) =
         if (Symtab.is_binder Name)
         then dest Body Name [Bvar]
         else ([],tm)
  | strip_binder_vars tm = ([],tm)
end;


fun is_infixed_comb (Comb{Rator=Comb{Rator=Const{Name,...},...},...}) = 
           Symtab.is_infix Name
  | is_infixed_comb _ = false;

local 
fun dest (tm as Comb{Rator = Comb{Rator = Const{Name,...}, Rand = t1},
                     Rand = t2}) s L =
        if (Name = s)
        then dest t2 s (t1::L)
        else rev (tm::L)
  | dest tm _ L = rev (tm::L)
in
fun strip_infix (tm as Comb{Rator = Comb{Rator = Const{Name,...},Rand = t1},
                            Rand = t2}) =
         if (Symtab.is_infix Name)
         then dest t2 Name [t1]
         else [tm]
  | strip_infix tm = [tm]
end;


fun strip_list (Comb{Rator = Comb{Rator = Const{Name = "CONS",...}, Rand = t1},
                     Rand = t2}) L = strip_list t2 (t1::L)
  | strip_list tm L = (tm::L);


fun strip_set(Comb{Rator = Comb{Rator = Const{Name = "INSERT",...}, Rand = t1},
                   Rand = t2}) L = strip_set t2 (t1::L)
  | strip_set tm L = (tm::L);


(* first clause corresponds to GSPEC (\v. (M,N)) ;
 *  second to GSPEC (\(v1,...,vn).(M,N))
 ***)
exception NOT_SET_ABS;
fun strip_set_abs(tm as Abs _) =
    let val {Bvar,Body} = dest_abs tm
    in case Body 
         of (Comb{Rator=Comb{Rator=Const{Name=",",...},Rand=tm1},Rand=tm2}) =>
              if ([Bvar] = intersect (Term.free_vars tm1) (Term.free_vars tm2))
              then ([Bvar],tm1,tm2)
              else raise NOT_SET_ABS
          | _ => raise HOL_PP_ERR{function="strip_set_abs",
                                  message = "badly formed set abstraction"}
    end
  | strip_set_abs tm = 
      let val {varstruct, body} = Dsyntax.dest_pabs tm
          val L = Dsyntax.strip_pair varstruct
          val {fst,snd} = Dsyntax.dest_pair body
      in
      if (set_eq L (intersect (Term.free_vars fst) (Term.free_vars snd)))
      then (L,fst,snd)
      else raise NOT_SET_ABS
      end
      handle _ => raise NOT_SET_ABS;




(* Printing functions for variables. Bound variables need to be looked up in
 *  the environment E to get their info (name and type).
 ***)
local
fun lookup 0 (Fv x::_) = x
  | lookup n (_::rst) = lookup (n-1) rst
  | lookup _ _ = raise HOL_PP_ERR{function = "pr_var", message = "lookup"}
in
fun pr_var ppstrm =
   let val add_string = PP.add_string ppstrm
       fun pr_atom 0 _ _ = add_string " ... "
	 | pr_atom n {Name,Ty} showtype = 
             if (showtype)
             then ( add_string ("("^Name^" :");
                    pp_type ppstrm Ty (n-1);
                    add_string ")"
                  )
             else add_string Name
       fun pr_v 0 _ _ = add_string " ... "
         | pr_v n _ (Fv v) = pr_atom n v (!Globals.show_types)
	 | pr_v n E (Bv i) = 
              if (!Globals.show_dB)
              then add_string ("("^Lib.int_to_string i^")")
              else pr_atom n (lookup i E) false
	 | pr_v _ _ _ = raise HOL_PP_ERR{function = "pr_var", 
					 message = "not a var"}
   in   pr_v
   end
fun pr_var_list ppstrm n = 
   pr_list_to_ppstream ppstrm (fn ppstrm => pr_var ppstrm n [])
                              (fn _ => ())
		              (fn ppstrm => PP.add_break ppstrm (1,0))
end;



(* Varstructs are odious. I found that the easiest way to handle them 
 * is to map them to (perhaps partial) s-expressions.
 ****)
datatype sexp = premature_end
              | atom of term
              | unc of (sexp*sexp);

(* Map to <sexp,term,env> triple. Takes a term and returns the first
 * varstruct (mapped to an sexp), the rest of the term, and the env arising
 * from the first varstruct.
 ****)
fun dest_uncurry (Abs{Bvar,Body}) = (atom Bvar, Body,[Bvar])
  | dest_uncurry (Comb{Rator = Const{Name = "UNCURRY",...},Rand}) =
         let val (s,M,e0) = dest_uncurry Rand
             val (t,N,e1) = dest_uncurry M
         in
         (unc(s,t), N, (e1@e0))
         end
  | dest_uncurry M = (premature_end,M,[]);


(* Get top level tuple from sexp *)
fun get_backbone (unc(M,N)) = M::(get_backbone N)
  | get_backbone x = [x];


(* Takes an sexp and prints it. Therefore, this will print one element from
 * a varstruct list.
 ***)
fun pr_varstruct ppstrm =
   let val {add_string,add_break,begin_block,end_block,...} = 
              with_ppstream ppstrm
       val pr_var = pr_var ppstrm
       fun pr_infix_unc L n = 
           ( begin_block INCONSISTENT 2;
             add_string "(";
             pr_list (pr_vstruct n)
                     (fn () => add_string ",")
                     (fn () => add_break(0,0))
                     L;
             add_string ")";
             end_block())
       and
           pr_vstruct n (S as unc _) = pr_infix_unc (get_backbone S) n
         | pr_vstruct n (atom (v as Fv _)) = pr_var n [] v
         | pr_vstruct _ premature_end = raise HOL_PP_ERR{function="pr_vstruct",
                                                       message="premature end"}
         | pr_vstruct _ (atom _) = raise HOL_PP_ERR{function = "pr_vstruct",
                                              message="badly formed varstruct"}
   in   pr_vstruct
   end;

(* Strips a term of parse form "\<varstruct_list>.M" into a triple:
 * <funcs,term,env>. Each member f in funcs has type (unit -> unit).
 * Each f either prints out a list of variables (using pr_var_list)
 * or a single, complete varstruct (using pr_varstruct).
 ******)
fun strip_varstruct ppstrm =
   let
   val pvstruct = pr_varstruct ppstrm
   val pvlist = pr_var_list ppstrm
   fun strip (tm as Comb{Rator = Const{Name = "UNCURRY",...},...}) =
        let val (s,M,e0) = dest_uncurry tm
        in if (hd(rev(get_backbone s)) = premature_end)
           then ([],tm,[])
           else let val (L,M',e1) = strip M
                in ((fn n => pvstruct n s)::L, M', e1@e0)
                end
        end
     | strip (tm as Abs _) =
        let val (V,M) = Dsyntax.de_abs tm
            val (L,M',e) = strip M
        in ((fn n => pvlist n V)::L, M', (e@rev V))
        end
     | strip tm = ([],tm,[])
   in 
   strip
   end;

(* "bump" is used in stripping restricted quantifiers. It increments the
 * index of any bound variables inside a restriction. This is used in the case
 *
 *     RQ <pred1> (\x. RQ <pred2> (\y. M))
 *
 * where RQ is a restricted quantifier constant. If pred1 and pred2 are the 
 * same, then we want to print 
 *
 *     RQ x y ::<pred1>. M
 *
 * but if not then we print
 * 
 *     RQ x::<pred1>. RQ y::pred2. M
 *
 * The problem comes with testing that pred1 and pred2 are the same. We
 * test up to alpha-convertibility, but we can't just check the dB structure,
 * since pred2 is one binder "past" pred1. 
 *
 * Example.
 *
 *     - %`!x y. !a::($> x). !b::($> y). (x > y) ==> (a > b)`;
 *     val it = (--`!x y. !a b ::($> x). x > y ==> a > b`--) : term
 * 
 * Showing the dB structure and the restricted quantifiers, this is
 *
 *     - %`!x y. !a::($> x). !b::($> y). (x > y) ==> (a > b)`;
 *     val it =
 *     `!x y. RES_FORALL ($> (1))
 *            (\a. RES_FORALL ($> (1)) (\b. (3) > (2) ==> (1) > (0)))`
 *
 * Notice that the "x" in "($> x)" is one away from its binder, as is the 
 * "y" in "($> y)". Hence, just testing with aconv will not be correct. 
 *
 *************)

fun bump (Bv i) = Bv (i+1)
  | bump (Comb{Rator,Rand}) = Comb{Rator=bump Rator, Rand=bump Rand}
  | bump (Abs{Bvar,Body}) = Abs{Bvar=Bvar,Body=bump Body}
  | bump x = x;
      
fun strip_restr_quant ppstrm {binder,restr,rest} =
   let val pvstruct = pr_varstruct ppstrm
       val pvar = pr_var ppstrm
       fun strip R (tm as Comb{Rator = Const{Name = "UNCURRY",...},...}) =
             let val (s,M,e0) = dest_uncurry tm
             in if (hd(rev(get_backbone s)) = premature_end)
                then ([],tm,[])
                else let val (L,M',e1) = strip_next (bump R) M
                     in ((fn n => pvstruct n s)::L, M', e1@e0)
                     end
             end
         | strip R (Abs{Bvar,Body}) =
             let val (L,Body',e) = strip_next (bump R) Body
             in ((fn n => pvar n [] Bvar)::L, Body', (e@[Bvar]))
             end
         | strip _ tm = ([],tm,[])
       and strip_next R (tm as Comb{Rator=Comb{Rator=Const{Name,...},
                                               Rand=rstn}, Rand}) =
             if (Name=binder andalso (aconv rstn R))
             then strip R Rand
             else ([],tm,[])
         | strip_next _ tm = ([],tm,[])
   in
   strip restr rest
   end;

fun strip_let ppstrm =
   let fun strip(Comb{Rator=Comb{Rator=Const{Name="LET",...},
                                 Rand=Abs{Bvar,Body}},
                      Rand=tm}) =
         ([((fn n => pr_var ppstrm n [] Bvar),tm)],Body,[Bvar])
     | strip(M as Comb
          {Rator=Comb{Rator = Const{Name = "LET", ...},
    		      Rand=tm1 as Comb{Rator=Const{Name="UNCURRY",...},...}},
           Rand = N}) =
         let val (s,tm2,e) = dest_uncurry tm1
         in
         if (hd(rev(get_backbone s)) = premature_end)
         then ([],M,[])
         else ([((fn n => pr_varstruct ppstrm n s),N)],tm2,e)
         end
     | strip(M as Comb{Rator = Comb{Rator = Const{Name = "LET",...}, 
                                    Rand = tm1},
                       Rand = tm2}) =
         ( case (strip tm1)
             of (L,Abs{Bvar,Body},e) => 
                      (((fn n => pr_var ppstrm n [] Bvar),tm2)::L, 
                       Body, Bvar::e)
              | (L, tm as Comb{Rator = Const{Name = "UNCURRY",...},...},e0) =>
                   let val (s,tm3,e1) = dest_uncurry tm
                   in
                   if (hd(rev(get_backbone s)) = premature_end)
                   then (L,tm,e0)
                   else (((fn n=> pr_varstruct ppstrm n s),tm2)::L,tm3,(e1@e0))
                   end 
              | _ => ([],M,[])
         )
     | strip M = ([],M,[])
   in strip
   end;


(* The term pretty printer *)
fun pp_tm ppstrm =
   let val {add_string,add_break,begin_block,end_block,...} = 
              with_ppstream ppstrm
       val pr_var = pr_var ppstrm
       val pr_var_list = pr_var_list ppstrm
       val pr_varstruct = pr_varstruct ppstrm
       val strip_varstruct = strip_varstruct ppstrm  
       val add_lparen = add_lparen ppstrm
       val add_rparen = add_rparen ppstrm
       val pp_type = pp_type ppstrm
       fun pr_const {Name,Ty} n =
          let val ptype = !Globals.show_types
          in if ptype
             then add_string "("
             else ()
             ;
             (* special syntax for empty lists and sets *)
             add_string
                (if (Name = "NIL")
                 then "[]" 
                 else if ((Name="EMPTY") andalso not(is_vartype Ty)
                          andalso (#Tyop(dest_type Ty)="set"))
                      then "{}"
                      else case (Symtab.fixity_of_term Name)
                             of Term.Binder => dollar^Name
                              | (Term.Infix _) => dollar^Name
                              | _ => Name)
             ;
             if ptype
             (* maybe (add_break(1,0);BB;add_string":";pp_type;EB  ... *)
             then (add_string " :"; pp_type Ty (n-1); add_string ")")
             else () 
          end

fun pr_comb rator rand grav E n =
   (begin_block (if (!(#stack_infixes(Globals.pp_flags)))
                 then CONSISTENT
                 else INCONSISTENT) 2;
     add_lparen grav GRAPP;
     if (is_infixed_comb rator)  (* to print `(f o g) x` properly *)
     then pr_term rator GRAPP E (n-1)
     else pr_term rator DELIM E (n-1);
     add_break(1,0);
     pr_term rand GRAPP E (n-1);
     add_rparen grav GRAPP;
     end_block ()
   )
and
(*********
 * The pattern match for pr_term goes like this (c stands for a Const):
 *
 *     Fv       (* free variable *)
 *     Bv       (* bound variable *)
 *     Const    (* constant *)
 *     Abs      (* lambda abstraction *)
 *     c P Q R  (* c = COND *)
 *     c P Q    (* c = {CONS, INSERT, LET, <infix>, <restricted binder>} *)
 *     c P      (* c = {~, GSPEC, UNCURRY, <binder>, <binder> <vstruct>} *)
 *     P Q      (* fall through case for Combs *)
 *     ty_antiq (* injection of hol_type into term, so have to cater for it. *)
 *
 ********)
    pr_term _ _ _ 0 = add_string " ... "
  | pr_term (v as Fv _) grav E n = pr_var n E v
  | pr_term (v as Bv _) grav E n = pr_var n E v
  | pr_term (Const r) _ _ n = pr_const r n
  | pr_term (tm as Abs _) grav E n =         (* simple abstractions *)
           let val (F,body,e) = strip_varstruct tm
           in
           ( begin_block CONSISTENT 2;
             add_lparen grav DELIM;
             add_string "\\";
               begin_block INCONSISTENT 1;
               pr_list (fn f => f n)
                       (fn () => ())
                       (fn () => add_break(1,0))
                       F;
               end_block();
             add_string ".";
             add_break(1,0);
               begin_block INCONSISTENT 2;
               pr_term body NADA (e@E) (n-1);
               end_block();
             add_rparen grav DELIM;
             end_block() )
           end

    (* conditionals, the only 3 argument built in constant recognized by 
     * pr_term
     ****)
  | pr_term (Comb{Rator = Comb{Rator = Comb{Rator = Const{Name = "COND",...},
                                            Rand = b},
                               Rand = larm},
                  Rand = rarm}) grav E n =
           ( add_lparen grav DELIM;
             begin_block CONSISTENT 0;
             pr_term b INFINITY E (n-1);
             add_break(1,0);
             add_string "=> ";
             pr_term larm INFINITY E (n-1);
             add_break(1,0);
             add_string "| ";
             pr_term rarm INFINITY E (n-1);
             end_block();
             add_rparen grav DELIM
           )

    (* 2 argument built in constants: CONS, INSERT, LET, all infixes, and
     * restricted quantifiers.
     ***)

    (* lists *)
  | pr_term (tm as Comb{Rator = f as Comb{Rator = Const{Name="CONS",...},...},
                        Rand}) grav E n =
           let val l = strip_list tm []
           in
           case (hd l) 
             of (Const{Name = "NIL",...}) =>
                    ( begin_block INCONSISTENT 1;
                      add_string "[";
                      pr_list (fn trm => pr_term trm NADA E (n-1))
                              (fn () => add_string ";")
                              (fn () => add_break(1,0))
                              (rev (tl l));
                      add_string "]";
                      end_block() )
              | _ => pr_comb f Rand grav E n
           end
    (* enumerated set *)
  | pr_term (tm as Comb{Rator=Comb{Rator=Const{Name="INSERT",...},...},...})
            grav E n = 
           let val L = strip_set tm []
               val p = PREC(Symtab.prec_of_term "INSERT")
           in
           case (hd L) 
             of (Const{Name = "EMPTY",...}) =>
                    ( begin_block INCONSISTENT 1;
                      add_string "{";
                      pr_list (fn trm => pr_term trm NADA E (n-1))
                              (fn () => add_string ";")
                              (fn () => add_break(1,0))
                              (rev (tl L));
                      add_string "}";
                      end_block() )
              | _ => ( begin_block CONSISTENT 0;
                       add_lparen grav p;
                       pr_list (fn trm => pr_term trm p E (n-1))
                               (fn () => add_string " INSERT")
                               (fn () => add_break(1,0))
                               (rev L);
                       add_rparen grav p;
                       end_block ()
                     )
           end
    (* let statements *)
  | pr_term (tm as Comb{Rator as Comb{Rator = Const{Name = "LET",...},...},
                        Rand})
            grav E n =
     (case (strip_let ppstrm tm)
        of ([],_,[]) => pr_comb Rator Rand grav E n
        | ([],_,_) => raise HOL_PP_ERR{function="pr_term",message="let clause"}
        | (L,m,e) =>
           ( add_lparen grav DELIM;
             begin_block CONSISTENT 0;
             add_string "let ";
             pr_list 
               (fn (f,arg) => 
                  let val (F,body,e') = strip_varstruct arg
                  in
                    begin_block INCONSISTENT 2;
                    f n;  (* print let-bound name *) 
                    if (null F)  (* args *)
                    then () 
                    else add_string " ";
                    pr_list (fn f => f n) (fn () => ())
                            (fn () => add_break(1,0))
                            F;
                    add_string " =";
                    add_break(1,2);
                    end_block();
                    pr_term body DELIM (e'@E) (n-1);
                    add_break(1,0)
                  end)
               (fn () => add_string "and")
               (fn () => add_break(1,0))
               (rev L);

             add_string "in";
             add_break(1,0);
             pr_term m NADA (e@E) (n-1);  (* pp the body *)
             end_block();
             add_rparen grav DELIM
           )
     )

    (* "infix" case and restricted quantifier case *)
  | pr_term (tm as Comb{Rator as Comb{Rator = c as Const{Name,...}, Rand = t1},
                        Rand}) grav E n =
          (case (Symtab.fixity_of_term Name)
           of (Term.Infix prec) 
           => let val L = strip_infix tm
                  val p = PREC(prec)
              in add_lparen grav p;
                 begin_block (if (!(#stack_infixes(Globals.pp_flags)))
                              then CONSISTENT
                              else INCONSISTENT) 0;
                 (* if infix_at_front and we're printing A /\ B, we have the
                  * following stream: A <BR> "/\ " B
                  * otherwise: A " /\" <BR> B
                  ******)
                 pr_list 
                   (fn trm => pr_term trm p E (n-1))
                   (fn () => 
                      if (!(#infix_at_front(Globals.pp_flags)))
                      then add_break(if(Name<>comma) then 1 else 0,0)
                      else add_string((if(Name<>comma)then space else"")^Name))
                   (fn () => 
                      if (!(#infix_at_front(Globals.pp_flags)))
                      then add_string(Name^space)
                      else add_break(if (Name<>comma) then 1 else 0,0))
                   L;
                 end_block();
                 add_rparen grav p
              end
          | _ (* decide if name is that of a restricted binder *)
          => if not(!Globals.show_restrict)
             then pr_comb Rator Rand grav E n
             else
             (case (Lib.assoc2 Name (Dsyntax.binder_restrictions()))
              of NONE   (* not a restricted quantifier *)
              => pr_comb Rator Rand grav E n
              | (SOME (binder,_)) 
                => (case (strip_restr_quant ppstrm 
                                            {binder=Name,restr=t1,rest=Rand})
                    of ([],_,_) => pr_comb Rator Rand grav E n
                     | (F,body,e)
                       => ( begin_block CONSISTENT 2;
                            add_lparen grav DELIM;
                            add_string (pad_binder binder);
                            begin_block INCONSISTENT 1;
                              pr_list (fn f => f n) (fn () => ())
                                      (fn () => add_break(1,0))
                                      F;
                              add_break (1,0);
                              add_string "::";
                              add_break (0,0);
                              pr_term t1 GRAPP E (n-1);
                            end_block();
                            add_string ".";
                            add_break(1,0);
                            begin_block INCONSISTENT 2;
                            pr_term body NADA (e@E) (n-1);
                            end_block();
                            add_rparen grav DELIM;
                            end_block()))))

    (* Built in constants taking one argument : negation ("~"), GSPEC, 
     * UNCURRY, <binder>, <binder> <vstruct>
     ***)
    (* negations *)
  | pr_term (tm as Comb{Rator = Const{Name = "~", ...}, ...}) grav E d =
           let val (n,m) = strip_neg tm
           in
             add_lparen grav GRAPP;
             Lib.for_se 0 (n-1) (fn _ => add_string "~");
             pr_term m GRAPP E (d-1);
             add_rparen grav GRAPP
           end
    (* set abstractions *)
  | pr_term (Comb{Rator as Const{Name = "GSPEC",...}, Rand}) grav E n =
         ( let val (e,tm1,tm2) = strip_set_abs Rand
               val e' = e@E
           in
             begin_block CONSISTENT 2;
             add_string "{";
             pr_term tm1 NADA e' (n-1);
             add_string " |";
             add_break (1,0);
             pr_term tm2 NADA e' (n-1);
             add_string "}";
             end_block()
           end
           handle NOT_SET_ABS => pr_comb Rator Rand grav E n
         )
    (* lambda varstructs:  \(x,y).M  *)
  | pr_term (tm as Comb{Rator as Const{Name = "UNCURRY",...},Rand}) grav E n =
          (case (strip_varstruct tm)
             of ([],_,_) => pr_comb Rator Rand grav E n
              | (F,body,e) => 
                 ( begin_block CONSISTENT 2;
                   add_lparen grav DELIM;
                   add_string "\\";
                   begin_block INCONSISTENT 1;
                   pr_list (fn f => f (n-1))
                           (fn () => ())
                           (fn () => add_break(1,0))
                           F;
                   end_block();
                   add_string ".";
                   add_break(1,0);
                   begin_block INCONSISTENT 2;
                   pr_term body NADA (e@E) (n-1);
                   end_block();
                   add_rparen grav DELIM;
                   end_block()
                 ))

    (* binder applied to varstruct: e.g.,  !(x,y,z). M   *)
  | pr_term (Comb{Rator as Const{Name = cstr,Ty},
                  Rand as Comb{Rator = Const{Name = "UNCURRY",...},...}})
              grav E n = 
           if (Symtab.fixity_of_term cstr <> Term.Binder) 
           then pr_comb Rator Rand grav E n
           else
           (case (strip_varstruct Rand)
              of ([],_,_) => pr_comb Rator Rand grav E n
               | (F,body,e)
                 => ( begin_block CONSISTENT 2;
                      add_lparen grav DELIM;
                      add_string (pad_binder cstr);
                      begin_block INCONSISTENT 1;
                      pr_list (fn f => f (n-1))
                              (fn () => ())
                              (fn () => add_break(1,0))
                              F;
                      end_block();
                      add_string ".";
                      add_break(1,0);
                      begin_block INCONSISTENT 2;
                      pr_term body NADA (e@E) (n-1);
                      end_block();
                      add_rparen grav DELIM;
                      end_block()
                    ))

    (* "binder" case: e.g. !x y z. M. *)
  | pr_term (trm as Comb{Rator=c as Const{Name,...},Rand=tm as Abs _})
            grav E n =
           if (Symtab.fixity_of_term Name <> Term.Binder) 
           then pr_comb c tm grav E n
           else let val (V,body) = strip_binder_vars trm
                in
                  begin_block INCONSISTENT 2;
                  add_lparen grav DELIM;
                    begin_block INCONSISTENT 1;
                     add_string (pad_binder Name);
                     pr_var_list (n-1) V;
                    end_block();
                  add_string ".";
                  add_break(1,0);
                    pr_term body NADA (rev V@E) (n-1);
                  add_rparen grav DELIM;
                  end_block()
                end

  (* fall through case for combs *)
  | pr_term (Comb{Rator, Rand}) grav E n = pr_comb Rator Rand grav E n
           
  | pr_term (ty_antiq ty) grav E n = 
           ( begin_block CONSISTENT 0;
             add_string ("(ty_antiq("^(!Globals.type_pp_prefix)^"`:");
             pp_type ty (n-1);
             add_string ("`"^(!Globals.type_pp_suffix)^"))");
             end_block())

in  pr_term
end;

fun pp_self_parsing_type ppstrm ty = 
   ( PP.begin_block ppstrm CONSISTENT 0;
     PP.add_string ppstrm ((!Globals.type_pp_prefix)^"`:"); 
     pp_type ppstrm ty  (!Globals.max_print_depth); 
     PP.add_string ppstrm ("`"^(!Globals.type_pp_suffix)); 
     PP.end_block ppstrm
   ) handle e => (Lib.say "\nError in attempting to print an HOL type!\n";
                  raise e);

fun pp_term ppstrm tm = 
   if (!Globals.max_print_depth = 0)
   then PP.add_string ppstrm " ... "
   else pp_tm ppstrm tm NADA [] (!Globals.max_print_depth);

fun pp_self_parsing_term ppstrm tm = 
  ( PP.begin_block ppstrm CONSISTENT 0;
    PP.add_string ppstrm ((!Globals.term_pp_prefix)^"`"); 
    pp_term ppstrm tm; 
    PP.add_string ppstrm ("`"^(!Globals.term_pp_suffix));
    PP.end_block ppstrm
  ) handle e => (Lib.say "\nError in attempting to print an HOL term!\n";
                 raise e);
  
fun P f x y z = f y z x;

fun type_to_string ty =
   PP.pp_to_string (!Globals.linewidth) 
                   (P pp_type (!Globals.max_print_depth))
                   ty;

fun term_to_string tm = PP.pp_to_string (!Globals.linewidth) pp_term tm

fun print_type ty = output(std_out,type_to_string ty);
fun print_term tm = output(std_out,term_to_string tm);

end; (* HOL_PP *)
