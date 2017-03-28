(* ===================================================================== *)
(* FILE          : induct_then.sig                                       *)
(* DESCRIPTION   : Signature for a generalized induction tactic.         *)
(*                 Translated from hol88.                                *)
(*                                                                       *)
(* AUTHOR        : (c) Tom Melham, University of Cambridge               *)
(* TRANSLATOR    : Konrad Slind, University of Calgary                   *)
(* DATE          : September 11, 1991                                    *)
(* ===================================================================== *)


signature Induct_then_sig =
sig
structure Thm : Thm_sig
val INDUCT_THEN : Thm.thm -> Abbrev.thm_tactic -> Abbrev.tactic
end;
