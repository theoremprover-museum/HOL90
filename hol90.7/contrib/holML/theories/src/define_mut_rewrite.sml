(* File: define_mut_rewrite.sml *)

fun define_mut_rewrite_TAC defs =
REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
REWRITE_TAC defs THEN
BETA_TAC THEN REWRITE_TAC [];
