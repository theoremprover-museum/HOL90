
(*===========================================================================*)
(*                                                                           *)
(*   FILE:         mk_odd_even.sml                                           *)
(*   EDITOR:       Paul Curzon                                               *)
(*   DATE:         July 1991                                                 *)
(*   DESCRIPTION : Odd and Even 	   	 	   	             *)
(*                                                                           *)
(*===========================================================================*)
(*=================================  HISTORY  ===============================*)
(*									     *)
(*									     *)
(* Author:       Wim Ploegaerts  (ploegaer@imec.be)			     *)
(*									     *)
(* Date:         Fri Feb  8 1991					     *)
(*									     *)
(* Organization: Imec vzw.						     *)
(*               Kapeldreef 75						     *)
(*               3001 Leuven - Belgium					     *)
(*									     *)
(*   HOL90 Version April 1993 by PC                                          *)
(*									     *)
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
  val _ = delete_theory (path^"odd_even")
end;


new_theory "odd_even";

val EVEN = definition "arithmetic" "EVEN";
val ODD = definition "arithmetic" "ODD";
val EVEN_ODD = theorem "arithmetic" "EVEN_ODD";
val ODD_EVEN = theorem "arithmetic" "ODD_EVEN";
val EVEN_ADD = theorem "arithmetic" "EVEN_ADD";
val ODD_ADD = theorem "arithmetic" "ODD_ADD";
val EVEN_MULT = theorem "arithmetic" "EVEN_MULT";
val ODD_MULT = theorem "arithmetic" "ODD_MULT";

(*---------------------------------------------------------------------------*)
val EVEN_ODD_0 = store_thm (
 "EVEN_ODD_0",
  (--`(EVEN 0) /\ ~(ODD 0)`--),
   REWRITE_TAC [ODD,EVEN]
);

(*---------------------------------------------------------------------------*)

(*
|- !n. (~EVEN(SUC n) = EVEN n) /\ (~ODD(SUC n) = ODD n)
*)


val NOT_EVEN_ODD_SUC_EVEN_ODD = store_thm (
 "NOT_EVEN_ODD_SUC_EVEN_ODD",
  (--`!n. (~EVEN(SUC n) = EVEN n) /\ (~ODD(SUC n) = ODD n)`--),
   REWRITE_TAC [ODD,EVEN]
);

(*---------------------------------------------------------------------------*)

val EVEN_ODD_SUC = store_thm (
 "EVEN_ODD_SUC",
  (--`!n. (EVEN(SUC n) = ODD n) /\ (ODD(SUC n) = EVEN n)`--),
   REWRITE_TAC [ODD,EVEN,GSYM ODD_EVEN,GSYM EVEN_ODD]
);

(*---------------------------------------------------------------------------*)

val EVEN_ODD_PLUS_CASES = store_thm (
  "EVEN_ODD_PLUS_CASES",
  (--`!n m . (((ODD n) /\ (ODD m)) ==> (EVEN (n + m))) /\
          (((ODD n) /\ (EVEN m)) ==> (ODD (n + m))) /\
          (((EVEN n) /\ (EVEN m)) ==> (EVEN (n + m)))`--),
  REPEAT STRIP_TAC THEN
  REWRITE_TAC [EVEN_ADD,ODD_ADD] THEN
  ASM_REWRITE_TAC [GSYM EVEN_ODD] THEN
  ASM_REWRITE_TAC [EVEN_ODD]
);

(*---------------------------------------------------------------------------*)

val EVEN_IMPL_MULT = store_thm (
  "EVEN_IMPL_MULT",
  (--`! n m . (EVEN n) \/ (EVEN m) ==> (EVEN (n * m))`--),
  REWRITE_TAC [EVEN_MULT]
);

(*---------------------------------------------------------------------------*)

val ODD_IMPL_MULT = store_thm (
  "ODD_IMPL_MULT",
  (--`! n m . (ODD n) /\ (ODD m) ==> (ODD (n * m))`--),
  REWRITE_TAC [ODD_MULT]
);

(*---------------------------------------------------------------------------*)

(*
MULT_ODD = |- !n m. ODD(n * m) ==> ODD n /\ ODD m 
*)


val MULT_ODD = store_thm (
   "MULT_ODD",
   (--`!n m. ODD(n * m) ==> ODD n /\ ODD m`--),
    REWRITE_TAC [ODD_MULT]);

(*---------------------------------------------------------------------------*)

(*
MULT_EVEN = 
|- !n m. EVEN(n * m) ==> EVEN n \/ EVEN m
*)

val MULT_EVEN = store_thm (
   "MULT_EVEN",
   (--`!n m. EVEN(n * m) ==> EVEN n \/ EVEN m`--),
    REWRITE_TAC [EVEN_MULT]);


export_theory();
close_theory();
