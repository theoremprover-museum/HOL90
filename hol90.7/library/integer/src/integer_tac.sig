(*======================================================================*)
(* FILE         : integer_tactics.ml                                    *)
(* DESCRIPTION  : gives the signature for IntegerTactics                *)
(*                                                                      *)
(* AUTHOR       : E. L. Gunter                                          *)
(* DATE         : 92.11.19                                              *)
(*                                                                      *)
(*======================================================================*)

(* Copyright 1992 by AT&T Bell Laboratories *)

signature IntegerTactics_sig =
    sig
	val INT_CASES_RULE : {int_case_thm:thm, neg_int_case_thm:thm} -> thm

(*
  A1 |- !n1:num. P(INT n1)   A2 |- !n2:num. P(neg(INT n2))
------------------------------------------------------------
                  A1 u A2 |- !M:integer. P M
*)


	val INT_CASES_TAC : tactic

(*
                   [A] !n:integer. P n
============================================================================
 [A] !n1:num. P (INT n1)   [A,!n1:num. P (INT n1)] !n2:num. P (neg(INT n2))

  INT_CASES_TAC allows a reduction of a problem about all integers to
  two problems about natural numbers.  After making this reduction one
  can proceed by induction on the natural numbers.
*)


(****************************************************************************)

(*
  SIMPLE_INT_CASES_RULE and SIMPLE_INT_CASES_TAC allow a reduction of a
  problem about all integers to the three cases where the integer is
  positive, where it is negative, and where it is zero.
*)

	val SIMPLE_INT_CASES_RULE : {pos_case_thm:thm,
				     neg_case_thm:thm,
				     zero_case_thm:thm} -> thm

(*
      A1 |- !N:integer. POS N ==> P N
      A2 |- !N:integer. NEG N ==> P N
              A3 |- P (INT 0)
     ---------------------------------
      A1 u A2 u A3 |- !N:integer. P N
*)


	val SIMPLE_INT_CASES_TAC : tactic

(*
                   [A] !N:integer. P N
==============================================================================
 [A] !N. POS N ==> P N  [A, !N. POS N ==> P N] !N. NEG N ==> P N  [A] P(INT 0)
*)


(****************************************************************************)

(*
  INT_MIN_RULE, INT_MAX_RULE, INT_MIN_TAC, and INT_MAX_TAC are for
  showing that minimum and maximun elements for bounded subsets of
  the integers exist.
*)

	val INT_MIN_RULE : {non_empty_thm:thm, bnd_below_thm:thm} -> thm

(*
  A1 |- ?M:integer. S1 M    A2 |- ?K1. !N. N below K1 ==> ~S1 N
  -------------------------------------------------------------
     A1 u A2 |- ?MIN. S1 MIN /\ (!N1. N1 below MIN ==> ~S1 N1)
*)


	val INT_MIN_TAC : term -> tactic

(* term = S1

                   [A] Goal
   =============================================
     [A, S1 MIN, !N. N below MIN ==> ~S1 N] Goal
     [A] ?M:integer. S1 M
     [A, S1 M] ?LB. !N. N below LB ==> ~S1 N
*)


	val INT_MAX_RULE : {non_empty_thm:thm, bnd_above_thm:thm} -> thm

(*  A1 |- ?M:integer. S1 M    A2 |- ?K1. !N. K1 below N ==> ~S1 N
  -------------------------------------------------------------
     A1 u A2 |- ?MAX. S1 MAX /\ (!N1. MAX below N1 ==> ~S1 N1)
*)


	val INT_MAX_TAC : term -> tactic

(* term = S1
                   [A] Goal
   =============================================
     [A, S1 MAX. !N. MAX below N ==> ~S1 N] Goal
     [A] ?M:integer. S1 M
     [A, S1 M] ?UB. !N. UB below N ==> ~S1 N
*)


(***************************************************************************)

	val INT_RIGHT_ASSOC_TAC : term -> tactic

(* term = (a plus b) plus c

   A |-  t((a plus b) plus c)
---------------------------------
   A |-  t(a plus (b plus c))
*)


	val INT_LEFT_ASSOC_TAC : term -> tactic

(* term = a plus (b plus c)

   A |-  t(a plus (b plus c))
---------------------------------
   A |-  t((a plus b) plus c)
*)

    end (* signature IntegerTactics_sig *)
