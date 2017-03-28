(* ===================================================================== *)
(* FILE          : tactical.sig                                          *)
(* DESCRIPTION   : Signature for functions that glue tactics together.   *)
(*                 From LCF, and added to through the years. Translated  *)
(*                 from hol88.                                           *)
(*                                                                       *)
(* AUTHORS       : (c) University of Edinburgh and                       *)
(*                     University of Cambridge, for hol88                *)
(* TRANSLATOR    : Konrad Slind, University of Calgary                   *)
(* DATE          : September 11, 1991                                    *)
(* ===================================================================== *)


signature Tactical_sig =
sig
structure Thm : Thm_sig

  val TAC_PROOF : Abbrev.goal * Abbrev.tactic -> Thm.thm
  val prove : Thm.Term.term * Abbrev.tactic -> Thm.thm
  val store_thm : string * Thm.Term.term * Abbrev.tactic -> Thm.thm
  val ASSUM_LIST : (Thm.thm list -> Abbrev.tactic) -> Abbrev.tactic
  val POP_ASSUM : Abbrev.thm_tactic -> Abbrev.tactic
  val POP_ASSUM_LIST : (Thm.thm list -> Abbrev.tactic) -> Abbrev.tactic
  val THEN : Abbrev.tactic * Abbrev.tactic -> Abbrev.tactic
  val THENL : Abbrev.tactic * Abbrev.tactic list -> Abbrev.tactic
  val ORELSE : Abbrev.tactic * Abbrev.tactic -> Abbrev.tactic
  val FAIL_TAC : string -> Abbrev.goal -> 'a
  val NO_TAC : Abbrev.goal -> 'a
  val ALL_TAC : Abbrev.tactic
  val TRY : Abbrev.tactic -> Abbrev.tactic
  val REPEAT : Abbrev.tactic -> Abbrev.tactic
  val VALID : Abbrev.tactic -> Abbrev.tactic
  val EVERY : Abbrev.tactic list -> Abbrev.tactic
  val FIRST : Abbrev.tactic list -> Abbrev.tactic
  val MAP_EVERY : ('a -> Abbrev.tactic) -> 'a list -> Abbrev.tactic
  val MAP_FIRST : ('a -> Abbrev.tactic) -> 'a list -> Abbrev.tactic
  val EVERY_ASSUM : Abbrev.thm_tactic -> Abbrev.tactic
  val FIRST_ASSUM : Abbrev.thm_tactic -> Abbrev.tactic
  val SUBGOAL_THEN : Thm.Term.term -> Abbrev.thm_tactic -> Abbrev.tactic
  val CHANGED_TAC : Abbrev.tactic -> Abbrev.tactic
end;
