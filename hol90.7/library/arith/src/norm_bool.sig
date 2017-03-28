signature Norm_bool_sig =
sig
   val EQ_IMP_ELIM_CONV : (term -> bool) -> conv
   val MOVE_NOT_DOWN_CONV : (term -> bool) -> conv -> conv
   val DISJ_LINEAR_CONV : conv
   val DISJ_NORM_FORM_CONV : conv
end
