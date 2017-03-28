(* ===================================================================== *)
(* FILE          : help.sig                                              *)
(* DESCRIPTION   : Signature for the online help facility.               *)
(*                                                                       *)
(* AUTHOR        : (c) Konrad Slind, University of Calgary               *)
(* DATE          : December 13, 1991                                     *)
(* ===================================================================== *)

signature Help_sig =
sig
val helper : string list -> string -> unit
val help : string -> unit
val help1 : string -> unit
end;
