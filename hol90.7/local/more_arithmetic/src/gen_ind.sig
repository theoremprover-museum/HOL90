(* =====================================================================*)
(* FILE          : gen_ind.sig                                          *)
(* DESCRIPTION   : Signature for general induction rules and tactics    *)
(* AUTHOR	 :  P Curzon 					        *)
(* DATE		 : April 1993						*)
(*                                                                      *)
(* =====================================================================*)

signature Gen_induction_sig =
sig
val GEN_INDUCT_RULE : thm -> thm -> thm
val GEN_INDUCT_TAC : tactic
end;
