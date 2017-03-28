signature Instance_sig =
sig
(*   type term sharing type term = CoreHol.Term.term
   type conv sharing type conv = Abbrev.conv
*)
   type term
   type conv

   val INSTANCE_T_CONV : (term -> term list) -> conv -> conv
end
