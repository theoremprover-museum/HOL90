(* ===================================================================== *)
(* FILE          : num_conv.sig                                          *)
(* DESCRIPTION   : Signature for the alogical hack relating number       *)
(*                 constants to their predecessors. Translated from      *)
(*                 hol88.                                                *)
(*                                                                       *)
(* AUTHOR        : Tom Melham                                            *)
(* TRANSLATOR    : Konrad Slind, University of Calgary                   *)
(* DATE          : September 11, 1991                                    *)
(* ===================================================================== *)


signature Num_conv_sig =
sig
   structure Thm : Thm_sig;
   val num_CONV : Thm.Term.term -> Thm.thm
end;
