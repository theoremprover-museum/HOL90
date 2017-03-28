(* ===================================================================== *)
(* FILE          : tautLib.sig                                           *)
(* DESCRIPTION   : Signature for the tautology library. Translated from  *)
(*                 hol88.                                                *)
(* ===================================================================== *)

signature tautLib_sig =
sig
   type tactic
   type conv 

  val PTAUT_CONV : conv
  val PTAUT_TAC : tactic
  val PTAUT_PROVE : conv
  val TAUT_CONV : conv
  val TAUT_TAC : tactic
  val TAUT_PROVE : conv
end;
