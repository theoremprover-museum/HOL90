(* =====================================================================*)
(* FILE          : set_ind.sig                                          *)
(* DESCRIPTION   : Signature for an implementation of induction for     *)
(*                 sets. Translated from hol88.                         *)
(*                                                                      *)
(* =====================================================================*)

signature Set_ind_sig =
sig
val SET_INDUCT_TAC : tactic
end;
