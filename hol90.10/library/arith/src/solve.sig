signature Solve_sig =
sig
(*   type term sharing type term = CoreHol.Term.term
   type conv sharing type conv = Abbrev.conv
*)
   type term 
   type conv

   val INEQS_FALSE_CONV : conv
   val DISJ_INEQS_FALSE_CONV : conv
   val NOT_NOT_INTRO_CONV : conv
   val is_T : term -> bool
   val is_F : term -> bool
   val NEGATE_CONV : conv -> conv
   val DEPTH_FORALL_CONV : conv -> conv 
   val FORALL_ARITH_CONV : conv
end
