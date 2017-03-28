signature Convs_sig =
sig
   (* type conv *)
   val RULE_OF_CONV : Abbrev.conv -> (CoreHol.Term.term -> CoreHol.Thm.thm)
   val ALL_CONV : Abbrev.conv
   val THENC : (Abbrev.conv * Abbrev.conv) -> Abbrev.conv
   val ORELSEC : (Abbrev.conv * Abbrev.conv) -> Abbrev.conv
   val REPEATC : Abbrev.conv -> Abbrev.conv
   val CHANGED_CONV : Abbrev.conv -> Abbrev.conv
   val TRY_CONV : Abbrev.conv -> Abbrev.conv
   val CONV_RULE : Abbrev.conv -> CoreHol.Thm.thm -> CoreHol.Thm.thm
   val RAND_CONV : Abbrev.conv -> Abbrev.conv
   val RATOR_CONV : Abbrev.conv -> Abbrev.conv
   val ABS_CONV : Abbrev.conv -> Abbrev.conv
   val ARGS_CONV : Abbrev.conv -> Abbrev.conv
end
