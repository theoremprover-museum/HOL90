(* ===================================================================== *)
(* FILE          : rec_type_support.sig                                  *)
(* DESCRIPTION   : Signature for proof support for types constructed by  *)
(*                 define_type. Translated from hol88.                   *)
(*                                                                       *)
(* AUTHOR        : (c) Tom Melham, University of Cambridge               *)
(* TRANSLATOR    : Konrad Slind, University of Calgary                   *)
(* DATE          : September 15, 1991                                    *)
(* ===================================================================== *)


signature Rec_type_support_sig =
sig
val prove_induction_thm : thm -> thm
val prove_cases_thm : thm -> thm
val prove_constructors_one_one : thm -> thm
val prove_constructors_distinct : thm -> thm
end;
