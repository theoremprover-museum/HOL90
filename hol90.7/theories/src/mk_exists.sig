(* ===================================================================== *)
(* FILE          : mk_exists.sig                                         *)
(* DESCRIPTION   : Signature for the definition of the existential       *)
(*                 quantifier. Translated from hol88.                    *)
(*                                                                       *)
(* AUTHOR        : (c) Mike Gordon, University of Cambridge              *)
(* TRANSLATOR    : Konrad Slind, University of Calgary                   *)
(* DATE          : September 11, 1991                                    *)
(* ===================================================================== *)


signature Mk_exists_sig =
sig
type thm
val EXISTS_DEF : thm
end;
