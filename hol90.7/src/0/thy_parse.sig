(* ===================================================================== *)
(* FILE          : thy_parse.sig                                         *)
(* DESCRIPTION   : Signature for the simple lambda calculus parser. Used *)
(*                 to parse theories.                                    *)
(*                                                                       *)
(* AUTHOR        : Konrad Slind                                          *)
(* DATE          : November 10, 1992                                     *)
(* ===================================================================== *)

signature Thy_parse_sig =
sig
  structure Term : Term_sig
  val theory_term_parser : string -> Term.term
end;
