(* ===================================================================== *)
(* FILE          : taut_thms.sig                                         *)
(* DESCRIPTION   : Signature for a collection of tautologies. These are  *)
(*                 collected in one place and proved uniformly for the   *)
(*                 first time in hol90. Some are proved much more        *)
(*                 elegantly in the comments (hol88 code).               *)
(*                                                                       *)
(* AUTHORS       : (c) Tom Melham, University of Cambridge, for hol88    *)
(*                     Konrad Slind, University of Calgary               *)
(* DATE          : September 11, 1991                                    *)
(* ADDITIONS     : by RJB, Dec 21, 1992, proved by a uniform tactic now  *)
(*                 (Konrad Slind)                                        *)
(* ===================================================================== *)


signature Taut_thms_sig =
sig
structure Thm : Thm_sig
val OR_IMP_THM : Thm.thm
val NOT_IMP : Thm.thm
val DISJ_ASSOC  : Thm.thm
val DISJ_SYM : Thm.thm
val DE_MORGAN_THM : Thm.thm
val LEFT_AND_OVER_OR : Thm.thm
val RIGHT_AND_OVER_OR : Thm.thm
val LEFT_OR_OVER_AND : Thm.thm
val RIGHT_OR_OVER_AND : Thm.thm
val IMP_DISJ_THM : Thm.thm
val IMP_F_EQ_F :Thm.thm
val AND_IMP_INTRO :Thm.thm
val EQ_IMP_THM :Thm.thm
val EQ_EXPAND :Thm.thm
val COND_RATOR :Thm.thm
val COND_RAND :Thm.thm
val COND_ABS :Thm.thm
val COND_EXPAND :Thm.thm
end;
