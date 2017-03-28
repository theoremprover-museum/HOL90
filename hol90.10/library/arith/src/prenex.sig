signature Prenex_sig =
sig
(*   type term sharing type term = CoreHol.Term.term
   type conv sharing type conv = Abbrev.conv
*)
   type term
   type conv

   val is_prenex : term -> bool
   val PRENEX_CONV : conv
end
