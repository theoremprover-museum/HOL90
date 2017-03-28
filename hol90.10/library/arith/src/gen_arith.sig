signature Gen_arith_sig =
sig
(*   type term sharing type term = CoreHol.Term.term
   type conv sharing type conv = Abbrev.conv
*)

   type term
   type conv

   val non_presburger_subterms : term -> term list
   val is_presburger : term -> bool
   val ARITH_CONV : conv
end
