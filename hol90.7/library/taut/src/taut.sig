(* ===================================================================== *)
(* FILE          : taut.sig                                              *)
(* DESCRIPTION   : Signature for the tautology library. Translated from  *)
(*                 hol88.                                                *)
(* ===================================================================== *)

signature Taut_sig =
sig
val PTAUT_CONV : conv
val PTAUT_TAC : tactic
val PTAUT_PROVE : conv
val TAUT_CONV : conv
val TAUT_TAC : tactic
val TAUT_PROVE : conv
end;
