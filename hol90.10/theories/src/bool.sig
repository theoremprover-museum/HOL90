(* ===================================================================== *)
(* FILE          : mk_bool.sig                                           *)
(* DESCRIPTION   : Signature for the logical constants and axioms.       *)
(*                 Translated from hol88.                                *)
(*                                                                       *)
(* AUTHOR        : (c) Mike Gordon, University of Cambridge              *)
(* TRANSLATOR    : Konrad Slind, University of Calgary                   *)
(* DATE          : September 11, 1991                                    *)
(* ===================================================================== *)

signature boolThrySig =
sig
   structure Min : Min_sig
   val T_DEF : CoreHol.Thm.thm
   val FORALL_DEF : CoreHol.Thm.thm
   val AND_DEF : CoreHol.Thm.thm
   val OR_DEF : CoreHol.Thm.thm
   val F_DEF : CoreHol.Thm.thm
   val NOT_DEF : CoreHol.Thm.thm
   val EXISTS_UNIQUE_DEF : CoreHol.Thm.thm
   val LET_DEF : CoreHol.Thm.thm
   val COND_DEF : CoreHol.Thm.thm
   val ONE_ONE_DEF : CoreHol.Thm.thm
   val ONTO_DEF : CoreHol.Thm.thm
   val TYPE_DEFINITION : CoreHol.Thm.thm
   
   val BOOL_CASES_AX : CoreHol.Thm.thm
   val IMP_ANTISYM_AX : CoreHol.Thm.thm
   val ETA_AX : CoreHol.Thm.thm
   val SELECT_AX : CoreHol.Thm.thm
   val INFINITY_AX : CoreHol.Thm.thm
end;
