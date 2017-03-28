signature Qsig =
  sig
    val ptm_with_ty : term frag list -> hol_type -> term
    val REFL : term frag list -> thm
    val ABS : term frag list -> thm -> thm
    val AC_CONV : thm * thm -> term frag list -> thm
    val AP_TERM : term frag list -> thm -> thm
    val AP_THM : thm -> term frag list -> thm
    val ASM_CASES_TAC : term frag list -> tactic
    val ASSUME : term frag list -> thm
    val BETA_CONV : term frag list -> thm
    val DISJ1 : thm -> term frag list -> thm
    val DISJ2 : term frag list -> thm -> thm
    val EXISTS : (term frag list * term frag list) -> thm -> thm
    val EXISTS_TAC : term frag list -> tactic
    val ID_EX_TAC : tactic
    val GEN : term frag list -> thm -> thm
    val SPEC : term frag list -> thm -> thm
    val ID_SPEC : thm -> thm
    val SPECL : term frag list list -> thm -> thm
    val ISPECL : term frag list list -> thm -> thm
    val SPEC_TAC : term frag list * term frag list -> tactic
    val ID_SPEC_TAC : term frag list -> tactic
    val SUBGOAL_THEN : term frag list -> thm_tactic -> tactic
    val TAUT_CONV : term frag list -> thm
    val DISCH : term frag list -> thm -> thm
    val UNDISCH_TAC : term frag list -> tactic
    val X_CHOOSE_TAC : term frag list -> thm_tactic
    val X_CHOOSE_THEN : term frag list -> thm_tactic -> thm_tactic
    val X_GEN_TAC : term frag list -> tactic
    val X_FUN_EQ_CONV : term frag list -> conv
    val INST : term frag list subst -> thm -> thm
    val INST_TYPE : term frag list subst -> thm -> thm
    val new_definition : string * term frag list -> thm
    val new_infix_definition : string * term frag list * int -> thm
    val num_CONV : term frag list -> thm
    val store_thm : string * term frag list * tactic -> thm
    val prove : term frag list -> tactic -> thm
  end 
