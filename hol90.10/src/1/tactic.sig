(* ===================================================================== *)
(* FILE          : tactic.sig                                            *)
(* DESCRIPTION   : Signature for tactics, an idea of Robin Milner.       *)
(*                 Translated from hol88.                                *)
(*                                                                       *)
(* AUTHORS       : (c) University of Edinburgh and                       *)
(*                     University of Cambridge, for hol88                *)
(* TRANSLATOR    : Konrad Slind, University of Calgary                   *)
(* DATE          : September 11, 1991                                    *)
(* ===================================================================== *)


signature Tactic_sig =
sig
structure Thm : Thm_sig
val ACCEPT_TAC : Abbrev.thm_tactic
val DISCARD_TAC : Thm.thm -> Abbrev.tactic
val CONTR_TAC  : Abbrev.thm_tactic
val CCONTR_TAC : Abbrev.tactic
val ASSUME_TAC : Abbrev.thm_tactic
val FREEZE_THEN : Abbrev.thm_tactical
val CONJ_TAC  : Abbrev.tactic
val DISJ1_TAC : Abbrev.tactic
val DISJ2_TAC : Abbrev.tactic
val MP_TAC : Abbrev.thm_tactic
val EQ_TAC : Abbrev.tactic
val X_GEN_TAC : Thm.Term.term -> Abbrev.tactic
val GEN_TAC : Abbrev.tactic
val SPEC_TAC : Thm.Term.term * Thm.Term.term -> Abbrev.tactic
val EXISTS_TAC : Thm.Term.term -> Abbrev.tactic
val GSUBST_TAC : (Thm.Term.term Lib.subst -> Thm.Term.term -> Thm.Term.term) -> 
                 Thm.thm list -> Abbrev.tactic
val SUBST_TAC : Thm.thm list -> Abbrev.tactic
val SUBST_OCCS_TAC : (int list * Thm.thm) list -> Abbrev.tactic
val SUBST1_TAC : Thm.thm -> Abbrev.tactic
val RULE_ASSUM_TAC : (Thm.thm -> Thm.thm) -> Abbrev.tactic
val SUBST_ALL_TAC : Thm.thm -> Abbrev.tactic
val CHECK_ASSUME_TAC : Abbrev.thm_tactic
val STRIP_ASSUME_TAC : Abbrev.thm_tactic
val STRUCT_CASES_TAC : Abbrev.thm_tactic
val COND_CASES_TAC : Abbrev.tactic
val BOOL_CASES_TAC : Thm.Term.term -> Abbrev.tactic
val STRIP_GOAL_THEN : Abbrev.thm_tactic -> Abbrev.tactic
val FILTER_GEN_TAC : Thm.Term.term -> Abbrev.tactic
val FILTER_DISCH_THEN : Abbrev.thm_tactic -> Thm.Term.term -> Abbrev.tactic
val FILTER_STRIP_THEN : Abbrev.thm_tactic -> Thm.Term.term -> Abbrev.tactic
val DISCH_TAC : Abbrev.tactic
val DISJ_CASES_TAC : Abbrev.thm_tactic
val CHOOSE_TAC : Abbrev.thm_tactic
val X_CHOOSE_TAC : Thm.Term.term -> Abbrev.thm_tactic
val STRIP_TAC : Abbrev.tactic
val FILTER_DISCH_TAC : Thm.Term.term -> Abbrev.tactic
val FILTER_STRIP_TAC : Thm.Term.term -> Abbrev.tactic
val ASM_CASES_TAC : Thm.Term.term -> Abbrev.tactic
val REFL_TAC : Abbrev.tactic
val UNDISCH_TAC : Thm.Term.term -> Abbrev.tactic
val AP_TERM_TAC : Abbrev.tactic
val AP_THM_TAC : Abbrev.tactic
end;
