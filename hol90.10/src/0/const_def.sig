(* ===================================================================== *)
(* FILE          : const_def.sig                                         *)
(* DESCRIPTION   : Signature for three variants on the principle of      *)
(*                 definition. Translated from hol88.                    *)
(*                                                                       *)
(* AUTHOR        : (c) Mike Gordon, University of Cambridge              *)
(* TRANSLATOR    : Konrad Slind, University of Calgary                   *)
(* DATE          : September 11, 1991                                    *)
(* ===================================================================== *)


signature Const_def_sig =
sig
structure Theory : Theory_sig
val new_definition : (string * Theory.Thm.Term.term) -> Theory.Thm.thm
val new_infix_definition :(string * Theory.Thm.Term.term * int) -> 
                           Theory.Thm.thm
val new_binder_definition : (string *  Theory.Thm.Term.term) -> Theory.Thm.thm
end
