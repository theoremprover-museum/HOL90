(* ===================================================================== *)
(* FILE          : mk_bool.sig                                           *)
(* DESCRIPTION   : Signature for the logical constants and axioms.       *)
(*                 Translated from hol88.                                *)
(*                                                                       *)
(* AUTHOR        : (c) Mike Gordon, University of Cambridge              *)
(* TRANSLATOR    : Konrad Slind, University of Calgary                   *)
(* DATE          : September 11, 1991                                    *)
(* ===================================================================== *)


signature Mk_bool_sig =
sig
type thm
val T_DEF : thm
val FORALL_DEF : thm
val AND_DEF : thm
val OR_DEF : thm
val F_DEF : thm
val NOT_DEF : thm
val EXISTS_UNIQUE_DEF : thm
val LET_DEF : thm
val COND_DEF : thm
val ONE_ONE_DEF : thm
val ONTO_DEF : thm
val TYPE_DEFINITION : thm

val BOOL_CASES_AX : thm
val IMP_ANTISYM_AX : thm
val ETA_AX : thm
val SELECT_AX : thm
val INFINITY_AX : thm
end;
