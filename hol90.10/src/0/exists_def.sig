(* ===================================================================== *)
(* FILE          : exists_def.sig                                        *)
(* DESCRIPTION   : Signature for the principle of definition for the     *)
(*                 existential quantifier.                               *)
(*                                                                       *)
(* AUTHORS       : (c) Mike Gordon, University of Cambridge, for hol88   *)
(*                     Konrad Slind, University of Calgary               *)
(* DATE          : September 11, 1991                                    *)
(* ===================================================================== *)


signature Exists_def_sig =
sig
structure Theory : Theory_sig
val new_binder_definition : (string * Theory.Thm.Term.term) -> Theory.Thm.thm
end;
