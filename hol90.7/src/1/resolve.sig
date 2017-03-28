(* ===================================================================== *)
(* FILE          : resolve.sig                                           *)
(* DESCRIPTION   : Signature for HOL-style resolution (MP + pattern      *)
(*                 matching). Translated from hol88.                     *)
(*                                                                       *)
(* AUTHOR        : (c) Tom Melham, University of Cambridge               *)
(* TRANSLATOR    : Konrad Slind, University of Calgary                   *)
(* DATE          : September 11, 1991                                    *)
(* ===================================================================== *)


signature Resolve_sig =
sig
structure Thm : Thm_sig
val MATCH_ACCEPT_TAC : thm_tactic
val ANTE_RES_THEN : thm_tactical
val RES_CANON : Thm.thm -> Thm.thm list
val IMP_RES_THEN : thm_tactic -> Thm.thm -> tactic
val RES_THEN : thm_tactic -> tactic
val IMP_RES_TAC : thm_tactic
val RES_TAC : tactic
val MATCH_MP_TAC : thm_tactic
end;
