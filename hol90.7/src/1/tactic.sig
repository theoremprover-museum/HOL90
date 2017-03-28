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
val ACCEPT_TAC : thm_tactic
val DISCARD_TAC : Thm.thm -> tactic
val CONTR_TAC  :thm_tactic
val CCONTR_TAC :tactic
val ASSUME_TAC :thm_tactic
val FREEZE_THEN :thm_tactical
val CONJ_TAC  :tactic
val DISJ1_TAC :tactic
val DISJ2_TAC :tactic
val MP_TAC : thm_tactic
val EQ_TAC : tactic
val X_GEN_TAC : Thm.Term.term -> tactic
val GEN_TAC : tactic
val SPEC_TAC : Thm.Term.term * Thm.Term.term -> tactic
val EXISTS_TAC : Thm.Term.term -> tactic
val GSUBST_TAC : (Thm.Term.term subst -> Thm.Term.term -> Thm.Term.term) -> 
                 Thm.thm list -> tactic
val SUBST_TAC : Thm.thm list -> tactic
val SUBST_OCCS_TAC : (int list * Thm.thm) list -> tactic
val SUBST1_TAC : Thm.thm -> tactic
val RULE_ASSUM_TAC : (Thm.thm -> Thm.thm) -> tactic
val SUBST_ALL_TAC : Thm.thm -> tactic
val CHECK_ASSUME_TAC : thm_tactic
val STRIP_ASSUME_TAC : thm_tactic
val STRUCT_CASES_TAC : thm_tactic
val COND_CASES_TAC : tactic
val BOOL_CASES_TAC : Thm.Term.term -> tactic
val STRIP_GOAL_THEN : thm_tactic -> tactic
val FILTER_GEN_TAC : Thm.Term.term -> tactic
val FILTER_DISCH_THEN : thm_tactic -> Thm.Term.term -> tactic
val FILTER_STRIP_THEN : thm_tactic -> Thm.Term.term -> tactic
val DISCH_TAC : tactic
val DISJ_CASES_TAC : thm_tactic
val CHOOSE_TAC : thm_tactic
val X_CHOOSE_TAC : Thm.Term.term -> thm_tactic
val STRIP_TAC : tactic
val FILTER_DISCH_TAC : Thm.Term.term -> tactic
val FILTER_STRIP_TAC : Thm.Term.term -> tactic
val ASM_CASES_TAC : Thm.Term.term -> tactic
val REFL_TAC : tactic
val UNDISCH_TAC : Thm.Term.term -> tactic
val AP_TERM_TAC : tactic
val AP_THM_TAC : tactic
end;
