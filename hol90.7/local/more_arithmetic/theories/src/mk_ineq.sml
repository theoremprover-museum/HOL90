
(*===========================================================================*)
(*                                                                           *)
(*   FILE:         mk_ineq.sml                                               *)
(*   EDITOR:       Paul Curzon                                               *)
(*   DATE:         July 1991                                                 *)
(*   DESCRIPTION   : Arithmetic theorems about inequalities		     *)
(*                                                                           *)
(*===========================================================================*)


(*===============================HISTORY=====================================*)
(*									     *)
(*   This file is based on the theories of 				     *)
(*                                                                           *)
(*   Rachel Cardell-Oliver						     *)
(*   Paul Curzon							     *)
(*   Elsa L Gunter							     *)
(*   Philippe Leveilley							     *)
(*   Wim Ploegaerts							     *)
(*                                                                           *)
(*   HOL90 Version April 1993 by PC                                          *)
(*        GEN_INDUCTION has been moved to theory arithmetic                  *)
(*                                                                           *)
(*===========================================================================*)

(*===========================================================================*)
(*                                                                           *)
(*  DEPENDANCIES :                                                           *)
(*      Library taut                        for PTAUT_PROVE                  *)
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
  val _ = delete_theory (path^"ineq")
end;

new_theory "ineq";


load_library_in_place taut_lib;


(* The theorems below need some tautologies which we prove first *)

val NOT_EQ =  Taut.PTAUT_PROVE (--`!t1 t2. (t1 = t2) = (~t1 = ~t2)`--);

val EQ_LESS_EQ = theorem "arithmetic" "EQ_LESS_EQ";
val NOT_LESS = theorem "arithmetic" "NOT_LESS";
val LESS_THM =  theorem "prim_rec" "LESS_THM";
val NOT_LESS_0 = theorem "prim_rec" "NOT_LESS_0";
val LESS_SUC_REFL = theorem "prim_rec" "LESS_SUC_REFL";
val LESS_CASES_IMP = theorem "arithmetic" "LESS_CASES_IMP";
val LESS_NOT_EQ = theorem "prim_rec" "LESS_NOT_EQ";
val LESS_ANTISYM  = theorem "arithmetic" "LESS_ANTISYM";
val LESS_OR_EQ  = definition "arithmetic" "LESS_OR_EQ";
val GREATER_EQ = theorem "arithmetic" "GREATER_EQ";
val LESS_EQ_ANTISYM = theorem "arithmetic" "LESS_EQ_ANTISYM";
val LESS_EQUAL_ANTISYM = theorem "arithmetic" "LESS_EQUAL_ANTISYM";
val LESS_EQ_REFL = theorem "arithmetic" "LESS_EQ_REFL";
val LESS_SUC =  theorem "prim_rec" "LESS_SUC";

(*<PL>*)
val NOT_EQ_LESS_EQ =
    store_thm
         ( "NOT_EQ_LESS_EQ",
           (--`! a b : num . ~(a = b) = ((a < b) \/ (b < a))`--),
	     REPEAT STRIP_TAC THEN
	     REWRITE_TAC
              [INST
                [{residue=(--`~((a:num) = b)`--),redex=(--`t1:bool`--)},
	      	 {residue=(--`((a < b) \/ (b < a))`--),redex=(--`t2:bool`--)}]
				 (SPEC_ALL NOT_EQ),
				 DE_MORGAN_THM,
			    NOT_LESS] THEN
	     SUBST_TAC [SPECL [(--`b <= a`--),(--`a <= b`--)] CONJ_SYM] THEN
	     REWRITE_TAC [EQ_LESS_EQ]);


(*===========================================================================*)
(*									     *)
(* 			     less and less or eq			     *)
(*									     *)
(*===========================================================================*)

(*<WP>*)
val LESS_IS_NOT_LESS_OR_EQ = store_thm ( 
  "LESS_IS_NOT_LESS_OR_EQ",
  (--`! x y . (x < y) = ~(y <= x)`--),
  REPEAT GEN_TAC THEN 
  REWRITE_TAC [LESS_OR_EQ,DE_MORGAN_THM] THEN
  EQ_TAC  THENL
 [
  DISJ_CASES_THEN
    (fn  t => REWRITE_TAC [t]) (SPECL [(--`x:num`--),(--`y:num`--)]
        (REWRITE_RULE [DE_MORGAN_THM] LESS_ANTISYM)) THEN
  CONV_TAC (ONCE_DEPTH_CONV SYM_CONV) THEN
  MATCH_ACCEPT_TAC LESS_NOT_EQ
 ,
  DISCH_THEN (fn t => ACCEPT_TAC (MATCH_MP LESS_CASES_IMP t))
 ]
);


(*===========================================================================*)
(*                                                                           *)
(*   AUTHOR:       Paul Curzon                                               *)
(*   DATE:         June 1991                                                 *)
(*                                                                           *)
(*===========================================================================*)

val GREATER_EQ_ANTISYM = store_thm("GREATER_EQ_ANTISYM",
       (--`!n m . ~( n >= m /\ n < m)`--),
  (REWRITE_TAC [GREATER_EQ]) THEN
  (REPEAT STRIP_TAC) THEN
  (IMP_RES_TAC LESS_EQ_ANTISYM));



(* ========================================================================= *)
(* A theorem by Paul Loewenstein *)


val LESS_EQ_LESS_EQ_EQ = store_thm("LESS_EQ_LESS_EQ_EQ",
  (--`!m n. m <= n /\ n <= m = (m = n)`--),
 REPEAT GEN_TAC THEN
 EQ_TAC THEN
 STRIP_TAC THENL
 [
  IMP_RES_TAC LESS_EQUAL_ANTISYM ,
  ASM_REWRITE_TAC [LESS_EQ_REFL]
 ]);


(*===========================================================================*)
(*                                                                           *)
(* AUTHOR        : Rachel Cardell-Oliver                                     *)
(* DATE          : 1990                                                      *)
(*                                                                           *)
(*===========================================================================*)


val NOT_LESS_AND_GREATER = 
store_thm(
  "NOT_LESS_AND_GREATER",
  (--`!n m. n<m ==> ~(m<n)`--),
GEN_TAC THEN 
INDUCT_TAC THENL
[ ASM_REWRITE_TAC[NOT_LESS_0] ,
  ASM_REWRITE_TAC[LESS_THM] THEN
  STRIP_TAC THENL
   [ ASM_REWRITE_TAC[NOT_LESS,LESS_OR_EQ,LESS_SUC_REFL] ,
     IMP_RES_TAC LESS_SUC THEN
      ASM_REWRITE_TAC[NOT_LESS,LESS_OR_EQ] ] ]);


(*===========================================================================*)

export_theory();
close_theory();
