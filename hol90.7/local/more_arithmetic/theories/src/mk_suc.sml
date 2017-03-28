
(*===========================================================================*)
(*                                                                           *)
(*   FILE:         mk_suc.sml                                                *)
(*   EDITOR:       Paul Curzon                                               *)
(*   DATE:         July 1991                                                 *)
(*   DESCRIPTION   : Theorems about SUC                   		     *)
(*                                                                           *)
(*===========================================================================*)


(*=================================  HISTORY ================================*)
(*									     *)
(*   This file is based on the theories of 				     *)
(*                                                                           *)
(*   Richard J.Boulton							     *)
(*   Rachel Cardell-Oliver						     *)
(*   Paul Curzon							     *)
(*   Jeff Joyce 							     *)
(*   Philippe Leveilley							     *)
(*   Wim Ploegaerts							     *)
(*                                                                           *)
(*   HOL90 Version April 1993 by PC                                          *)
(*                                                                           *)
(*===========================================================================*)

(*===========================================================================*)
(*                                                                           *)
(*  DEPENDANCIES :                                                           *)
(*                                                                           *)
(*===========================================================================*)

(*
val path = 
   (!Globals.HOLdir)^"library/more_arithmetic/theories/"^Globals.theory_file_type^"/"
*)

val path = 
   "../"^Globals.theory_file_type^"/"

val _ = theory_path := path::(!theory_path);


local
fun delete_theory name = 
    System.system("/bin/rm -f "^name^".thms "^name^".holsig")
in
  val _ = delete_theory (path^"suc")
end;


new_theory "suc";

(*===========================================================================*)
val NOT_SUC_LESS_EQ_0 = theorem "arithmetic" "NOT_SUC_LESS_EQ_0";
val GREATER_EQ = theorem "arithmetic" "GREATER_EQ";
val LESS_EQ_ANTISYM = theorem "arithmetic" "LESS_EQ_ANTISYM";
val LESS_0 = theorem "prim_rec" "LESS_0";
val LESS_EQ_MONO = theorem "arithmetic" "LESS_EQ_MONO";
val LESS_SUC_REFL  = theorem "prim_rec" "LESS_SUC_REFL";
val LESS_SUC  = theorem "prim_rec" "LESS_SUC";
val LESS_OR_EQ  = definition "arithmetic" "LESS_OR_EQ";
val LESS_THM  = theorem "prim_rec" "LESS_THM";
val LESS_EQ_SUC_REFL  = theorem "arithmetic" "LESS_EQ_SUC_REFL";
val NOT_LESS = theorem "arithmetic" "NOT_LESS";
val SUC_ID = theorem "prim_rec" "SUC_ID";
val LESS_EQ_SUC_REFL = theorem "arithmetic" "LESS_EQ_SUC_REFL";
val LESS_EQ = theorem "arithmetic" "LESS_EQ";
val ADD_CLAUSES = theorem "arithmetic" "ADD_CLAUSES";
val ADD1 = theorem "arithmetic" "ADD1";
val SUC_NOT = theorem "arithmetic" "SUC_NOT";
(*===========================================================================*)

(*<PL>*)
val NOT_FORALL_SUC_LESS_EQ =
    save_thm ("NOT_FORALL_SUC_LESS_EQ",
	      NOT_INTRO
	       (DISCH_ALL
		 (REWRITE_RULE [NOT_SUC_LESS_EQ_0]
	                       (SPEC (--`0`--)
                                 (ASSUME (--`(!n m. (SUC m) <= n)`--))))));
	 

(*===========================================================================*)
(* NOT_0_GREATER_EQ_SUC |- ~0 >= (SUC n)*)

val NOT_0_GREATER_EQ_SUC = save_thm("NOT_0_GREATER_EQ_SUC",
  GEN_ALL
   (REWRITE_RULE[LESS_0,GSYM GREATER_EQ]
     (SPEC (--`SUC n`--) (SPEC (--`0`--) LESS_EQ_ANTISYM))));



(*===========================================================================*)
(*                                                                           *)
(*   AUTHOR:       Paul Curzon                                               *)
(*   DATE:         June 1991                                                 *)
(*                                                                           *)
(*===========================================================================*)

(*SUC_GREATER_EQ_SUC = |- !m n. (SUC m) >= (SUC n) = m >= n *)

val  SUC_GREATER_EQ_SUC = save_thm ("SUC_GREATER_EQ_SUC",
       REWRITE_RULE[GSYM GREATER_EQ] LESS_EQ_MONO);



(*===========================================================================*)
(*                                                                           *)
(* AUTHOR        : R.J.Boulton                                               *)
(* DATE          : 1990                                                      *)
(*                                                                           *)
(*===========================================================================*)

(*---------------------------------------------------------------------------*)
(* LESS_EQ_LESS_SUC = |- !m n. m <= n = m < (SUC n)                          *)
(*---------------------------------------------------------------------------*)

val LESS_EQ_LESS_SUC =
 store_thm
  ("LESS_EQ_LESS_SUC",
   (--`!m n. (m <= n) = (m < (SUC n))`--),
   REWRITE_TAC [LESS_OR_EQ] THEN
   REPEAT GEN_TAC THEN
   EQ_TAC THENL
   [STRIP_TAC THENL
    [IMP_RES_TAC LESS_SUC,
     ASM_REWRITE_TAC [LESS_SUC_REFL]],
    REWRITE_TAC [LESS_THM] THEN
    STRIP_TAC THEN
    ASM_REWRITE_TAC []]);
(*---------------------------------------------------------------------------*)
val SUC_LESS_EQ =  store_thm("SUC_LESS_EQ",
  (--`!m n. ((m <= n) /\ ~(m = n)) ==> (SUC m) <= n`--),
   REPEAT STRIP_TAC THEN
   UNDISCH_TAC (--`m <= n`--) THEN
   SUBST_TAC [SPEC_ALL LESS_OR_EQ] THEN
   ASM_REWRITE_TAC [LESS_EQ]);
(*---------------------------------------------------------------------------*)

val NOT_SUC_LESS_EQ_SELF = store_thm("NOT_SUC_LESS_EQ_SELF",
  (--`!n. ~((SUC n) <= n)`--),
   GEN_TAC THEN
   REWRITE_TAC [LESS_OR_EQ,DE_MORGAN_THM] THEN
   REWRITE_TAC [SUC_ID,NOT_LESS,LESS_EQ_SUC_REFL]);
(*---------------------------------------------------------------------------*)


(*===========================================================================*)
(*                                                                           *)
(* AUTHOR        : Rachel Cardell-Oliver                                     *)
(* DATE          : 1990                                                      *)
(*                                                                           *)
(*===========================================================================*)


val SUC_0 = store_thm("SUC_0",
 (--`1 = (SUC 0)`--),
 ASM_REWRITE_TAC[ADD1,ADD_CLAUSES]);



val SUC_NOT_0 = save_thm("SUC_NOT_0", GSYM SUC_NOT);

export_theory();
close_theory();
