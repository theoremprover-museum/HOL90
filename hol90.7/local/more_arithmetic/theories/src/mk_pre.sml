
(*===========================================================================*)
(*                                                                           *)
(*   FILE:         mk_pre.sml                                                *)
(*   EDITOR:       Paul Curzon                                               *)
(*   DATE:         July 1991                                                 *)
(*   DESCRIPTION   : Theorems about PRE		     		             *)
(*                                                                           *)
(*===========================================================================*)


(*==================================  HISTORY  ==============================*)
(*									     *)
(*   This file is based on the theories of 				     *)
(*                                                                           *)
(*   Rachel Cardell-Oliver						     *)
(*   Wim Ploegaerts							     *)
(*   Wai Wong                                                                *)
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
  val _ = delete_theory (path^"pre")
end;



new_theory "pre";

val INDUCTION = theorem "num" "INDUCTION";

val PRE_SUC_EQ = theorem "arithmetic" "PRE_SUC_EQ";
val LESS_0 = theorem "prim_rec" "LESS_0";
val NOT_LESS_0 = theorem "prim_rec" "NOT_LESS_0";
val PRE = theorem "prim_rec" "PRE";
val LESS_MONO = theorem "prim_rec" "LESS_MONO";
val LESS_MONO_EQ = theorem "arithmetic" "LESS_MONO_EQ";
val ZERO_LESS_EQ = theorem "arithmetic" "ZERO_LESS_EQ";
val LESS_OR_EQ = definition "arithmetic" "LESS_OR_EQ";
val LESS_SUC_REFL = theorem "prim_rec" "LESS_SUC_REFL";
val ADD_CLAUSES = theorem "arithmetic" "ADD_CLAUSES";
val LESS_REFL = theorem "prim_rec" "LESS_REFL";
val NOT_LESS_EQUAL = theorem "arithmetic" "NOT_LESS_EQUAL";
val LESS_EQ_MONO_ADD_EQ = theorem "arithmetic" "LESS_EQ_MONO_ADD_EQ";
val NOT_LESS = theorem "arithmetic" "NOT_LESS";
val SUB_EQ_0 = theorem "arithmetic" "SUB_EQ_0";
val SUB_ADD = theorem "arithmetic" "SUB_ADD";
val NOT_LESS = theorem "arithmetic" "NOT_LESS";
val LESS_IMP_LESS_OR_EQ = theorem "arithmetic" "LESS_IMP_LESS_OR_EQ";
val LESS_EQ_ADD = theorem "arithmetic" "LESS_EQ_ADD";
val PRE_SUB1 = theorem "arithmetic" "PRE_SUB1";
val LESS_EQ_LESS_TRANS = theorem "arithmetic" "LESS_EQ_LESS_TRANS";
val LESS_EQ = theorem "arithmetic" "LESS_EQ";


(*===========================================================================*)
(*									     *)
(* 			  Theorems dealing with PRE			     *)
(*									     *)
(*===========================================================================*)

(*<PC>*)
val SUC_PRE = store_thm (
  "SUC_PRE",
  (--`!n . (0 < n) ==> ((SUC (PRE n)) = n)`--),
  REPEAT STRIP_TAC THEN
  (ACCEPT_TAC
       (REWRITE_RULE[]
          (MATCH_MP (SPEC (--`PRE n`--) PRE_SUC_EQ)
                 (ASSUME (--`0 < n`--)) )))
);

(*--------------------------------------------------------------------------*)

(*<WP>*)
val PRE_MONO = store_thm  (
  "PRE_MONO",
  (--`! m n . (PRE m < PRE n) ==> (m < n)`--),
  INDUCT_TAC THEN
  INDUCT_TAC  THEN
  REWRITE_TAC [PRE,NOT_LESS_0,LESS_0,LESS_MONO]
);

(*--------------------------------------------------------------------------*)

(*<WP>*)
val PRE_MONO_LESS_EQ = store_thm (
 "PRE_MONO_LESS_EQ",
 (--`! m n . (m < n) ==> (PRE m <= PRE n)`--),
  INDUCT_TAC THEN INDUCT_TAC THEN
  REWRITE_TAC [NOT_LESS_0,PRE,LESS_MONO_EQ,ZERO_LESS_EQ] THEN
  DISCH_THEN (fn thm => REWRITE_TAC [LESS_OR_EQ,thm])
);

(*--------------------------------------------------------------------------*)

(*<WP>*)
(*< PRE_LESS_EQ = |- !n. (PRE n) <= n >*)

val PRE_LESS_EQ =  save_thm (
          "PRE_LESS_EQ", 
          GEN_ALL (REWRITE_RULE [PRE]
                     (MATCH_MP PRE_MONO_LESS_EQ (SPEC (--`n:num`--)
                       LESS_SUC_REFL)))
);

(*--------------------------------------------------------------------------*)

(*<WP>*)
val PRE_ADD = store_thm  (
  "PRE_ADD",
  (--`!n m . (0 < n) ==> (PRE ( n + m ) = (PRE n) + m)`--),
  INDUCT_TAC THEN
  REWRITE_TAC [NOT_LESS_0,PRE,ADD_CLAUSES]
);


(*===========================================================================*)
(*									     *)
(* 			     relation SUC / PRE				     *)
(*									     *)
(*===========================================================================*)




(*<WP>*)
val SUC_LESS_PRE = store_thm (
  "SUC_LESS_PRE",
  (--`! m n . (SUC m < n) ==> (m < PRE n)`--),
  GEN_TAC THEN 
  INDUCT_TAC THEN
  REWRITE_TAC [NOT_LESS_0,PRE,LESS_MONO_EQ]
);

(*--------------------------------------------------------------------------*)

(*<WP>*)
val SUC_LESS_EQ_PRE = store_thm  (
  "SUC_LESS_EQ_PRE",
  (--`! m n . (0 < n) ==> (SUC m <= n) ==> (m <= PRE n)`--),
  REPEAT GEN_TAC THEN
  DISCH_THEN (fn thm => REWRITE_TAC [LESS_OR_EQ,MATCH_MP PRE_SUC_EQ thm]) THEN
  STRIP_TAC THEN
  IMP_RES_TAC SUC_LESS_PRE THEN
  ASM_REWRITE_TAC []
);

(*--------------------------------------------------------------------------*)

(*<WP>*)
val PRE_K_K = store_thm (
  "PRE_K_K",
  (--`!k . (0<k) ==> (PRE k < k)`--),
  INDUCT_THEN INDUCTION MP_TAC THEN
  REWRITE_TAC [LESS_REFL,LESS_0,PRE,LESS_SUC_REFL] 
);

(*===========================================================================*)
(*                                                                           *)
(* AUTHOR        : Rachel Cardell-Oliver                                     *)
(* DATE          : 1990                                                      *)
(*                                                                           *)
(*===========================================================================*)

val NOT_LESS_SUB = prove
  ((--`!m n. ~( m < (m-n) )`--)  ,
   REPEAT GEN_TAC THEN
   ASM_CASES_TAC (--`m<=n`--) THENL
   [ POP_ASSUM(fn thm =>
        REWRITE_TAC[REWRITE_RULE[GSYM SUB_EQ_0]thm,NOT_LESS_0]),
     POP_ASSUM(ASSUME_TAC o REWRITE_RULE[NOT_LESS_EQUAL]) THEN
     IMP_RES_TAC LESS_IMP_LESS_OR_EQ THEN
     IMP_RES_TAC SUB_ADD THEN
     REWRITE_TAC[NOT_LESS] THEN
     ONCE_REWRITE_TAC[GSYM(SPECL[(--`m-n`--),(--`m:num`--),(--`n:num`--)]
                     LESS_EQ_MONO_ADD_EQ)]
     THEN ASM_REWRITE_TAC[LESS_EQ_ADD] ] );




val PRE_LESS = store_thm("PRE_LESS",
  (--`!b:num. ( (0<b) /\ (b<a) ==> ((PRE b) < a))`--),
  REPEAT STRIP_TAC THEN
  ASSUME_TAC (REWRITE_RULE [NOT_LESS]
     (SPECL [(--`b:num`--),(--`1`--)] NOT_LESS_SUB)) THEN
  IMP_RES_TAC LESS_EQ_LESS_TRANS THEN
  ASM_REWRITE_TAC[PRE_SUB1] );


(*===========================================================================*)
(*                                                                           *)
(* AUTHOR        : Wai Wong                                                  *)
(* DATE          : April 1993                                                *)
(*                                                                           *)
(*===========================================================================*)

val LESS_IMP_LESS_EQ_PRE = store_thm("LESS_IMP_LESS_EQ_PRE",
    (--`!m n. 0 < n ==> ((m < n) = (m <= (PRE n)))`--),
    REPEAT INDUCT_TAC THEN REWRITE_TAC[NOT_LESS_0] THENL[
     DISCH_TAC THEN REWRITE_TAC[PRE,ZERO_LESS_EQ,LESS_0],
     REWRITE_TAC[PRE,LESS_MONO_EQ] THEN STRIP_TAC
     THEN MATCH_ACCEPT_TAC LESS_EQ]);


export_theory();
close_theory();
