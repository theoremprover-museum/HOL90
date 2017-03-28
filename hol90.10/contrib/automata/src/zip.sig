(* ===================================================================== *)
(* FILE          : zip_lib.sig                                           *)
(* DESCRIPTION   : Signature for useful proof support for :zip.          *)
(*                                                                       *)
(* ===================================================================== *)


signature Zip_lib_sig = 
sig
val PAIR_FORALL_CONV : term * term -> conv
val PAIR_EXISTS_CONV : term * term -> conv
val EXISTS_ZIP_CONV : term * term -> conv
val FORALL_ZIP_CONV : term * term -> conv
end;
