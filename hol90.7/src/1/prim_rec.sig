(* ===================================================================== *)
(* FILE          : prim_rec.sig                                          *)
(* DESCRIPTION   : Signature for primitive recursive definitions over    *)
(*                 recursive types. Translated from hol88.               *)
(*                                                                       *)
(* AUTHOR        : (c) Tom Melham, University of Cambridge 1987          *)
(* TRANSLATOR    : Konrad Slind, University of Calgary                   *)
(* DATE          : September 11, 1991                                    *)
(* ===================================================================== *)


signature Prim_rec_sig =
sig
structure Thm : Thm_sig
val prove_rec_fn_exists : Thm.thm -> Thm.Term.term -> Thm.thm
val new_recursive_definition : {name : string, 
                                fixity : Thm.Term.fixity,
                                rec_axiom : Thm.thm,
                                def : Thm.Term.term} -> Thm.thm
end;
