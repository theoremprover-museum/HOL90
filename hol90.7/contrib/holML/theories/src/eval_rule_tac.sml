(* File: rule_tac.sml *)

val _ = load_library_in_place (find_library "utils");

open ExtraGeneralFunctions;
fun EVAL_RULE_TAC defs =
    PURE_REWRITE_TAC defs THEN
    REPEAT STRIP_TAC THEN
    ((FIRST_ASSUM (ACCEPT_TAC o SPEC_ALL)) ORELSE
     (FIRST_ASSUM (fn th => (MP_IMP_TAC (SPEC_ALL th) THEN
       REPEAT CONJ_TAC THEN
      (FIRST_ASSUM ACCEPT_TAC ORELSE
       (FIRST_ASSUM (MP_IMP_TAC o SPEC_ALL) THEN 
       REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC))))));


