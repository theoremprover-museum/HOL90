signature Redconv_sig =
sig
(*   type thm sharing type thm = Thm.thm
   type tactic sharing type tactic = Abbrev.tactic
   type conv sharing type conv = Abbrev.conv
*)

    val RED_CONV : Abbrev.conv
    val REDUCE_CONV : Abbrev.conv
    val REDUCE_RULE : CoreHol.Thm.thm -> CoreHol.Thm.thm
    val REDUCE_TAC : Abbrev.tactic
end
