
(*===========================================================================*)
(*                                                                           *)
(*   FILE:         mk_mult.sml                                               *)
(*   EDITOR:       Paul Curzon                                               *)
(*   DATE:         July 1991                                                 *)
(*   DESCRIPTION : Theorems about MULT and EXP		     		     *)
(*                                                                           *)
(*===========================================================================*)


(*=================================  HISTORY  ===============================*)
(*									     *)
(*   This file is based on the theories of 				     *)
(*                                                                           *)
(*   Richard Boulton							     *)
(*   Philippe Leveilley							     *)
(*   Wim Ploegaerts							     *)
(*   Wai Wong                                                                *)
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
  val _ = delete_theory (path^"mult")
end;


new_theory "mult";

val MULT_SYM = theorem "arithmetic" "MULT_SYM";
val LESS_MONO_MULT = theorem "arithmetic" "LESS_MONO_MULT";
val ADD_ASSOC = theorem "arithmetic" "ADD_ASSOC";
val ADD_CLAUSES = theorem "arithmetic" "ADD_CLAUSES";
val LESS_EQ_LESS_EQ_MONO = theorem "arithmetic" "LESS_EQ_LESS_EQ_MONO";
val LESS_OR = theorem "arithmetic" "LESS_OR";
val LESS_EQ_REFL = theorem "arithmetic" "LESS_EQ_REFL";
val MULT_CLAUSES = theorem "arithmetic" "MULT_CLAUSES";
val INDUCTION = theorem "num" "INDUCTION";
val LESS_EQ_ADD = theorem "arithmetic" "LESS_EQ_ADD";
val TIMES2 = theorem "arithmetic" "TIMES2";
val EXP = definition "arithmetic" "EXP";
val LESS_SUC_REFL = theorem "prim_rec" "LESS_SUC_REFL";
val LESS_LESS_EQ_TRANS = theorem "arithmetic" "LESS_LESS_EQ_TRANS";
val LESS_OR_EQ = definition "arithmetic" "LESS_OR_EQ";
val ZERO_LESS_EXP = theorem "arithmetic" "ZERO_LESS_EXP";
val LESS_0 = theorem "prim_rec" "LESS_0";
val NOT_LESS_0 = theorem "prim_rec" "NOT_LESS_0";

(*--------------------------------------------------------------------------*)

(*<PL>*)
val LESS_MONO_MULT1 =
    save_thm ("LESS_MONO_MULT1",
	      GEN_ALL
		(SUBS [SPECL [(--`m:num`--),(--`p:num`--)] MULT_SYM,
		       SPECL [(--`n:num`--),(--`p:num`--)] MULT_SYM]
		      (SPEC_ALL LESS_MONO_MULT)));

(*===========================================================================*)
(*									     *)
(* 		       Inequalities and multiplication			     *)
(*									     *)
(*===========================================================================*)

(*WP 4-9-90*)

val LESS_MULT_PLUS_DIFF = store_thm (
  "LESS_MULT_PLUS_DIFF",
   (--`!n k l . (k < l) ==> (((k * n) + n) <= (l * n))`--),
  INDUCT_THEN INDUCTION MP_TAC THEN
  REWRITE_TAC [MULT_CLAUSES,ADD_CLAUSES,LESS_EQ_REFL] THEN
  DISCH_THEN (fn t => 
    REPEAT GEN_TAC THEN
    DISCH_THEN (fn t' =>
         ACCEPT_TAC 
         (REWRITE_RULE [ADD_CLAUSES,ADD_ASSOC]
           (MATCH_MP LESS_EQ_LESS_EQ_MONO
             (CONJ (MATCH_MP LESS_OR t') (MATCH_MP t t')))) ))
);

(*----------------------------------------------------------------------------*)
(* ONE_LESS_TWO_EXP_SUC = |- !n. 1 < (2 EXP (SUC n))                          *)
(*----------------------------------------------------------------------------*)
(*<RJB>*)
val ONE_LESS_TWO_EXP_SUC =
 store_thm
  ("ONE_LESS_TWO_EXP_SUC",
   (--`!n. 1 < (2 EXP (SUC n))`--),
   INDUCT_TAC THENL
   [REWRITE_TAC [EXP] THEN
    REWRITE_TAC [num_CONV (--`2`--),MULT_CLAUSES] THEN
    REWRITE_TAC [LESS_SUC_REFL],
    PURE_ONCE_REWRITE_TAC [EXP] THEN
    REWRITE_TAC [TIMES2] THEN
    ASSUME_TAC (SPEC (--`2 EXP (SUC n)`--)
        (SPEC (--`2 EXP (SUC n)`--) LESS_EQ_ADD)) THEN
    IMP_RES_TAC LESS_LESS_EQ_TRANS]);

(*===========================================================================*)
(*                                                                           *)
(* AUTHOR        : Wai Wong                                                  *)
(* DATE          : April 1993                                                *)
(*                                                                           *)
(*===========================================================================*)

val NOT_MULT_LESS_0 = store_thm("NOT_MULT_LESS_0",
    (--`!m n. (0 < m) /\ (0 < n) ==> 0 < (m * n)`--),
    REPEAT INDUCT_TAC THEN REWRITE_TAC[NOT_LESS_0]
    THEN STRIP_TAC THEN REWRITE_TAC[MULT_CLAUSES,ADD_CLAUSES,LESS_0]);

val EXP1 = store_thm("EXP1", (--`!n. n EXP 1 = n`--),
    CONV_TAC (ONCE_DEPTH_CONV num_CONV)
    THEN REWRITE_TAC[EXP,MULT_CLAUSES]);

val ZERO_LESS_TWO_EXP = save_thm("ZERO_LESS_TWO_EXP",
    (* |- !n. 0 < (2 EXP n) *)
    GEN_ALL (SUBS[SYM (num_CONV (--`2`--))](SPECL [(--`n:num`--), (--`1`--)] ZERO_LESS_EXP)));

val ONE_LESS_EQ_TWO_EXP = store_thm("ONE_LESS_EQ_TWO_EXP",
    (--`!n. 1 <= (2 EXP n)`--),
    INDUCT_TAC THENL[
     REWRITE_TAC[EXP,LESS_EQ_REFL],
     REWRITE_TAC[LESS_OR_EQ] THEN DISJ1_TAC
     THEN MATCH_ACCEPT_TAC ONE_LESS_TWO_EXP_SUC]);

export_theory();
close_theory();
