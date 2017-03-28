
(*===========================================================================*)
(*                                                                           *)
(*   FILE:         mk_zero_ineq.sml                                          *)
(*   EDITOR:       Paul Curzon                                               *)
(*   DATE:         July 1991                                                 *)
(*   DESCRIPTION:  Inequalities about 0		     		     	     *)
(*                                                                           *)
(*===========================================================================*)


(*============================  HISTORY  ====================================*)
(*									     *)
(*   This file is based on the theories of 				     *)
(*                                                                           *)
(*   Rachel Cardell-Oliver						     *)
(*   Paul Curzon							     *)
(*   Wim Ploegaerts							     *)
(*                                                                           *)
(*   HOL90 Version April 1993 by PC                                          *)
(*                                                                           *)
(*===========================================================================*)
(*===========================================================================*)
(*                                                                           *)
(*  DEPENDANCIES :                                                           *)
(*                                                                           *)
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
  val _ = delete_theory (path^"zero_ineq")
end;


new_theory "zero_ineq";

val ZERO_LESS_EQ = theorem "arithmetic" "ZERO_LESS_EQ";
val LESS_EQ_LESS_TRANS  = theorem "arithmetic" "LESS_EQ_LESS_TRANS";
val NOT_LESS_0 = theorem "prim_rec" "NOT_LESS_0";
val LESS_LEMMA1 = theorem "prim_rec" "LESS_LEMMA1";
val LESS_SUC_REFL = theorem "prim_rec" "LESS_SUC_REFL";
val GREATER_EQ = theorem "arithmetic" "GREATER_EQ";
val ADD1 = theorem "arithmetic" "ADD1";
val LESS_EQ_REFL = theorem "arithmetic" "LESS_EQ_REFL";
val ADD_SYM = theorem "arithmetic" "ADD_SYM";
val LESS_EQ_ADD = theorem "arithmetic" "LESS_EQ_ADD";
val NOT_LESS_EQUAL = theorem "arithmetic" "NOT_LESS_EQUAL";
val LESS_0_CASES = theorem "arithmetic" "LESS_0_CASES";
val LESS_OR_EQ = definition "arithmetic" "LESS_OR_EQ";
val LESS_REFL = theorem "prim_rec" "LESS_REFL";

(*===========================================================================*)
(*                                                                           *)
(*   AUTHOR:       Wim Ploegaerts                                            *)
(*                                                                           *)
(*===========================================================================*)


(*WP 4-9-90*)

val M_LESS_0_LESS = store_thm  (
  "M_LESS_0_LESS",
  (--`! m n . (m < n) ==> (0 < n)`--),
  REPEAT GEN_TAC THEN
  DISCH_THEN (fn thm => ASSUME_TAC
               (MATCH_MP (LESS_EQ_LESS_TRANS)
                         (CONJ (SPEC (--`m:num`--) ZERO_LESS_EQ) thm))) THEN
  FIRST_ASSUM ACCEPT_TAC
);
 
(*===========================================================================*)


(*===========================================================================*)
(*                                                                           *)
(*   AUTHOR:       Paul Curzon                                               *)
(*   DATE:         June 1991                                                 *)
(*                                                                           *)
(*===========================================================================*)

val LESS1EQ0 = store_thm ("LESS1EQ0",
       (--`!m . (m < 1) = (m = 0)`--),

 GEN_TAC THEN
 EQ_TAC THENL[

 (CONV_TAC (DEPTH_CONV num_CONV)) THEN
 (REPEAT STRIP_TAC) THEN
 (REWRITE_TAC[REWRITE_RULE
                      [ASSUME (--`m < (SUC 0)`--), NOT_LESS_0]
                      (SPECL [(--`m:num`--),(--`0`--)] LESS_LEMMA1)]),

 DISCH_TAC THEN
 (REWRITE_TAC[ASSUME (--`(m = 0)`--)]) THEN
 (CONV_TAC (DEPTH_CONV num_CONV)) THEN
 (REWRITE_TAC[LESS_SUC_REFL])]);

(*===========================================================================*)
val NOT_EQ_0 = store_thm("NOT_EQ_0",
   (--`! m . ~ ( m = 0)  ==> (m >= 1)`--),
 INDUCT_TAC THENL
 [
 (REWRITE_TAC[]),

 (REPEAT STRIP_TAC) THEN
 (ASM_CASES_TAC (--`m = 0`--)) THENL
   [
    REWRITE_TAC[ASSUME (--`(m = 0)`--)] THEN
    (CONV_TAC (ONCE_DEPTH_CONV num_CONV)) THEN
    (REWRITE_TAC[LESS_EQ_REFL,GREATER_EQ]),

    (REWRITE_TAC[GREATER_EQ,ADD1]) THEN
    (ONCE_REWRITE_TAC[ADD_SYM]) THEN
    (REWRITE_TAC[LESS_EQ_ADD])
   ]
 ]
);

(*===========================================================================*)
val LESS_EQ_0_EQ = store_thm("LESS_EQ_0_EQ",
(--`!m. m <= 0 ==> (m = 0)`--),
 (REPEAT STRIP_TAC) THEN
 (REWRITE_TAC [LESS_OR_EQ,
              (REWRITE_RULE[ASSUME (--`m <= 0`--)]
                           (SPEC_ALL 
                             (REWRITE_RULE[GSYM NOT_LESS_EQUAL]
                                          LESS_0_CASES)) )]));


(*--------------------------------------------------------------------------*)

(*===========================================================================*)
(*                                                                           *)
(*   AUTHOR:       Paul Curzon                                               *)
(*                                                                           *)
(*===========================================================================*)
(*===========================================================================*)
(*                                                                           *)
(*       If a number is greater than zero then it's not zero.                *)
(*                                                                           *)
(*       GREATER_NOT_ZERO = |- !x. 0 < x ==> ~(x = 0)                        *)
(*                                                                           *)
(*===========================================================================*)

val GREATER_NOT_ZERO = store_thm ("GREATER_NOT_ZERO",
(--`! x. (0 < x) ==> ~(x = 0)`--),
 (REPEAT STRIP_TAC) THEN
 UNDISCH_TAC (--`0<x`--) THEN
 ASM_REWRITE_TAC[LESS_REFL]);


(*===========================================================================*)
(*                                                                           *)
(* AUTHOR        : Rachel Cardell-Oliver                                     *)
(* DATE          : 1990                                                      *)
(*                                                                           *)
(*===========================================================================*)


val NOT_0_AND_MORE =store_thm("NOT_0_AND_MORE",
 (--`!x. ~( (x=0) /\ (0<x) )`--),
  REPEAT STRIP_TAC THEN
  UNDISCH_TAC (--`0<x`--) THEN
  ASM_REWRITE_TAC[LESS_REFL]);


export_theory();
close_theory ();
