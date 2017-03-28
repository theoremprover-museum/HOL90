signature Gen_arith_sig =
sig
   val non_presburger_subterms : term -> term list
   val is_presburger : term -> bool
   val ARITH_CONV : conv
end
