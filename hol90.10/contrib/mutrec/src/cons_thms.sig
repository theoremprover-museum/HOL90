(* =====================================================================*)
(* FILE          : cons_thms.sig                                        *)
(* DESCRIPTION   : signature for proving mutually recursive data        *)
(*                 constructors one-to-one, onto and distinct           *)
(*                                                                      *)
(* DATE          : 93.12.17                                             *)
(*                                                                      *)
(* =====================================================================*)

signature ConsThms_sig =
sig
val mutual_constructors_distinct : thm
val mutual_constructors_one_one : thm
val mutual_cases : thm
val argument_extraction_definitions : (string * thm) list
end
