(* ===================================================================== *)
(* FILE          : ac_resolve.sig                                        *)
(* DESCRIPTION   : Signature for HOL-style resolution (MP + pattern      *)
(*                 matching). Translated from hol88.                     *)
(*                                                                       *)
(* AUTHOR        : (c) Tom Melham, University of Cambridge               *)
(* TRANSLATOR    : Konrad Slind, University of Calgary                   *)
(* DATE          : September 11, 1991                                    *)
(* ===================================================================== *)

signature AC_Resolve_sig =
sig
val ANTE_RES_THEN : ac_eqns -> thm_tactical
val IMP_RES_THEN : ac_eqns -> thm_tactic -> Thm.thm -> tactic
val RES_THEN : ac_eqns -> thm_tactic -> tactic
val IMP_RES_TAC : ac_eqns -> thm_tactic
val RES_TAC : ac_eqns -> tactic
end;
