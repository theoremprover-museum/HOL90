(* =====================================================================*)
(* FILE          : ineq_conv.sig                                        *)
(* DESCRIPTION:  : Signature fo conversions for rewriting equalities    *)
(*                 and inequalities of naturals                         *)
(* AUTHOR	 : P Curzon 					        *)
(* DATE		 : April 1993						*)
(*                                                                      *)
(* =====================================================================*)

signature Ineq_conv_sig =
sig
val NUM_LESS_EQ_PLUS_CONV : (term -> conv)
val NUM_EQ_PLUS_CONV : (term -> conv)
val NUM_LESS_PLUS_CONV : (term -> conv)
end;
