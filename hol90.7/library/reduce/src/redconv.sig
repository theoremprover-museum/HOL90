signature Redconv_sig =
sig
    val RED_CONV : conv
    val REDUCE_CONV : conv
    val REDUCE_RULE : thm -> thm
    val REDUCE_TAC : tactic
end
