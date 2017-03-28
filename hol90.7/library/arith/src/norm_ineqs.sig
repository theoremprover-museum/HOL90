signature Norm_ineqs_sig =
sig
   val ADD_TERM_TO_LEQ_CONV : term -> conv
   val ADD_COEFFS_TO_LEQ_CONV : (int * (string * int) list) -> conv
   val LESS_OR_EQ_GATHER_CONV : conv
   val ARITH_FORM_NORM_CONV : conv
end
