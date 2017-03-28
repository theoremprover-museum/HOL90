(* ===================================================================== *)
(* FILE          : let_conv.sig                                          *)
(* DESCRIPTION   : Signature for paired beta conversion and "let" terms. *)
(*                 Translated from hol88.                                *)
(*                                                                       *)
(* AUTHOR        : (c) Tom Melham, University of Cambridge               *)
(* TRANSLATOR    : Konrad Slind, University of Calgary                   *)
(* DATE          : September 15, 1991                                    *)
(* ===================================================================== *)


signature Let_conv_sig =
sig
val PAIRED_BETA_CONV : conv
val let_CONV : conv
val PAIRED_ETA_CONV : conv
val GEN_BETA_CONV : conv
end;
