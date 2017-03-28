signature AC_Rewrite_sig =
sig
  val AC_REWRITES_CONV : ac_eqns -> thm list -> term -> thm
  val GEN_AC_REWRITE_CONV : (conv -> conv) 
                            -> thm list ref -> ac_eqns -> thm list -> conv
  val PURE_AC_REWRITE_CONV : ac_eqns -> thm list -> conv
  val AC_REWRITE_CONV : ac_eqns -> thm list -> conv
  val PURE_ONCE_AC_REWRITE_CONV : ac_eqns -> thm list -> conv
  val ONCE_AC_REWRITE_CONV : ac_eqns -> thm list -> conv
  val GEN_AC_REWRITE_RULE : (conv -> conv) 
                            -> thm list ref 
                            -> ac_eqns -> thm list -> thm -> thm
  val PURE_AC_REWRITE_RULE : ac_eqns -> thm list -> thm -> thm
  val AC_REWRITE_RULE : ac_eqns -> thm list -> thm -> thm
  val PURE_ONCE_AC_REWRITE_RULE : ac_eqns -> thm list -> thm -> thm
  val ONCE_AC_REWRITE_RULE : ac_eqns -> thm list -> thm -> thm
  val PURE_ASM_AC_REWRITE_RULE : ac_eqns -> thm list -> thm -> thm
  val ASM_AC_REWRITE_RULE : ac_eqns -> thm list -> thm -> thm
  val PURE_ONCE_ASM_AC_REWRITE_RULE : ac_eqns -> thm list -> thm -> thm
  val ONCE_ASM_AC_REWRITE_RULE : ac_eqns -> thm list -> thm -> thm
  val GEN_AC_REWRITE_TAC : (conv -> conv) 
                           -> thm list ref -> ac_eqns -> thm list -> tactic
  val PURE_AC_REWRITE_TAC : ac_eqns -> thm list -> tactic
  val AC_REWRITE_TAC : ac_eqns -> thm list -> tactic
  val PURE_ONCE_AC_REWRITE_TAC : ac_eqns -> thm list -> tactic
  val ONCE_AC_REWRITE_TAC : ac_eqns -> thm list -> tactic
  val PURE_ASM_AC_REWRITE_TAC : ac_eqns -> thm list -> tactic
  val ASM_AC_REWRITE_TAC : ac_eqns -> thm list -> tactic
  val PURE_ONCE_ASM_AC_REWRITE_TAC : ac_eqns -> thm list -> tactic
  val ONCE_ASM_AC_REWRITE_TAC : ac_eqns -> thm list -> tactic
  val FILTER_PURE_ASM_AC_REWRITE_RULE : (term -> bool) 
                                        -> ac_eqns -> thm list -> thm -> thm
  val FILTER_ASM_AC_REWRITE_RULE : (term -> bool) 
                                   -> ac_eqns -> thm list -> thm -> thm
  val FILTER_PURE_ONCE_ASM_AC_REWRITE_RULE : (term -> bool) 
                                             -> ac_eqns 
                                             -> thm list -> thm -> thm
  val FILTER_ONCE_ASM_AC_REWRITE_RULE : (term -> bool) 
                                        -> ac_eqns -> thm list -> thm -> thm
  val FILTER_PURE_ASM_AC_REWRITE_TAC : (term -> bool) 
                                       -> ac_eqns -> thm list -> tactic
  val FILTER_ASM_AC_REWRITE_TAC : (term -> bool) 
                                  -> ac_eqns -> thm list -> tactic
  val FILTER_PURE_ONCE_ASM_AC_REWRITE_TAC : (term -> bool) 
                                            -> ac_eqns -> thm list -> tactic
  val FILTER_ONCE_ASM_AC_REWRITE_TAC : (term -> bool) 
                                       -> ac_eqns -> thm list -> tactic
end;
