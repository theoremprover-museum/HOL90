(* ===================================================================== *)
(* FILE          : mk_exists.sig                                         *)
(* DESCRIPTION   : Signature for the definition of the existential       *)
(*                 quantifier. Translated from hol88.                    *)
(*                                                                       *)
(* AUTHOR        : (c) Mike Gordon, University of Cambridge              *)
(* TRANSLATOR    : Konrad Slind, University of Calgary                   *)
(* DATE          : September 11, 1991                                    *)
(* ===================================================================== *)


signature Exists_sig =
sig
   val EXISTS_DEF : CoreHol.Thm.thm
end;
