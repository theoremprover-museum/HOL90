(* ===================================================================== *)
(* FILE          : const_spec.sig                                        *)
(* DESCRIPTION   : Signature for the principle of constant specification.*)
(*                 Translated from hol88.                                *)
(*                                                                       *)
(* AUTHOR        : (c) Mike Gordon, University of Cambridge              *)
(* TRANSLATOR    : Konrad Slind, University of Calgary                   *)
(* DATE          : September 11, 1991                                    *)
(* ===================================================================== *)


signature Const_spec_sig =
sig
structure Theory : Theory_sig
val new_specification : {name :string,
                         consts : {fixity : Theory.Thm.Term.fixity,
                                   const_name : string} list,
                         sat_thm : Theory.Thm.thm} -> Theory.Thm.thm
end;
