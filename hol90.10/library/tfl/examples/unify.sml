(*---------------------------------------------------------------------------
 * A simple unification algorithm. This is unfinished! The main interest 
 * I had in attempting this file was to check 1) that the congruence rule 
 * for the "subst" datatype is correctly proved and deployed; and 2) that 
 * extraction works properly for a reasonably complicated function. Hopefully
 * one day, someone will finish the job.  The hard part is not defining the
 * functions (except for unification), but rather all the background theory 
 * having to do with substitutions, mgus, and idempotent mgus. Another point 
 * is that HOL should provide special syntax for case-statements, as the 
 * current syntax, where the "cased" object comes last, is hopeless.
 *---------------------------------------------------------------------------*)
new_theory"term" handle _ => ();
new_parent"set";

(*---------------------------------------------------------------------------
 * Define the datatypes of simple terms and substitutions for them. We
 * mix in the notion of success/failure with substitutions: probably
 * it would be better just to use a standard "option" type, so that 
 * Unify would interact nicely with a standard success/failure monad. 
 * On the other hand, the approach taken here allows "Unify" to read
 * nicely.
 *---------------------------------------------------------------------------*)
local open Hol_datatype
in
val term_ty_def = 
     hol_datatype `term = Var of 'a
                        | Const of 'a
                        | App of term => term`

val subst_ty_def =
     hol_datatype  `subst = Fail | Subst of ('a#'a term) list`
end;


(*---------------------------------------------------------------------------
 * Immediate subterm. No termination relation given.
 *---------------------------------------------------------------------------*)
val IST_def =
   function`(IST (x:'a term, Var y) = F) /\
            (IST (x, Const y) = F)       /\
            (IST (x, App M N) = (x=M) \/ (x=N))`;

val PST_def = 
Q.new_definition
      ("PST_def",
          `PST:'a term->'a term -> bool = TC (CURRY IST)`);


(*---------------------------------------------------------------------------
 *  Variables in a term.
 *---------------------------------------------------------------------------*)

val Vars_def = 
define Prefix
        `(Vars (Var x) = {x:'a}) /\
         (Vars (Const y) = {})   /\
         (Vars (App M N) = (Vars M) UNION (Vars N))`;


val point_to_prod_def = 
   define (Infix 400)   `## (f:'a->'b) (g:'a->'c) x = (f x, g x)`;


(*---------------------------------------------------------------------------
 * Composing substitutions; just declared, not defined.
 *---------------------------------------------------------------------------*)
val compose = 
  new_constant{Name = "compose", 
               Ty = Type`:('a#'a term) list 
                          -> ('a#'a term) list 
                            -> ('a#'a term) list`};

(*---------------------------------------------------------------------------
 * The field of a substitution; just declared, not defined.
 *---------------------------------------------------------------------------*)
val svars = 
  new_constant{Name = "SVars", 
               Ty = Type`:('a#'a term) list -> 'a set`};


(*---------------------------------------------------------------------------
 * Applying a substitution to a term; just declared, not defined.
 *---------------------------------------------------------------------------*)
val subst = 
  new_constant{Name = "subst", 
               Ty = Type`:('a#'a term) list -> 'a term -> 'a term`};



(*---------------------------------------------------------------------------
 * A reason why the following unification algorithm terminates.
 *---------------------------------------------------------------------------*)
val TR_def = Q.new_definition("TR_def", 
  `TR = inv_image ($PSUBSET X RPROD PST PST)
                  ((\(x:'a term,y). Vars(x) UNION Vars(y))##I)`);


(*---------------------------------------------------------------------------
 * The unification algorithm. 
 *---------------------------------------------------------------------------*)
fun Rdefine thml = 
  rfunction (Prim.postprocess
                 {WFtac = WF_TAC[],
             terminator = terminator, 
             simplifier = tc_simplifier thml})   RW_RULE;


val unify_def = 
 Rdefine[point_to_prod_def] 
`TR`
`(Unify(Const m, Const n) = ((m=n) => Subst[] | Fail)) /\
 (Unify(Const m, App M N) = Fail) /\
 (Unify(Const m, Var v)   = Subst[(v:'a,Const m)]) /\
 (Unify(Var v, M)         = (PST(Var v) M => Fail | Subst[(v,M)])) /\
 (Unify(App M N, Const x) = Fail) /\
 (Unify(App M N,Var v)    = (PST(Var v)(App M N) => Fail | Subst[(v,App M N)]))
 /\                         (* or Unify (Var v, App M N) *)
 (Unify(App M1 N1, App M2 N2) = 
      subst_case Fail (\theta. 
          subst_case Fail (\sigma. Subst (compose theta sigma)) 
                    (Unify (subst theta N1, subst theta N2))) (Unify(M1,M2)))`;

val subst_nchotomy = #nchotomy (#2 subst_ty_def);
