signature Norm_bool_sig =
sig
(*   type term sharing type term = CoreHol.Term.term
   type conv sharing type conv = Abbrev.conv
*)
   type term
   type conv

   val EQ_IMP_ELIM_CONV : (term -> bool) -> conv
   val MOVE_NOT_DOWN_CONV : (term -> bool) -> conv -> conv
   val DISJ_LINEAR_CONV : conv
   val DISJ_NORM_FORM_CONV : conv
end
