(* ===================================================================== *)
(* FILE          : hol_pp.sig                                            *)
(* DESCRIPTION   : Signature for the prettyprinting of HOL terms and     *)
(*                 types.                                                *)
(*                                                                       *)
(* AUTHOR        : Konrad Slind, University of Calgary                   *)
(* DATE          : August 26, 1991                                       *)
(* ===================================================================== *)


signature Hol_pp_sig =
sig
structure Term : Public_term_sig
val pp_type : PP.ppstream -> Term.Type.hol_type -> int -> unit
val pp_term : PP.ppstream -> Term.term -> unit
val pp_self_parsing_type : PP.ppstream -> Term.Type.hol_type -> unit
val pp_self_parsing_term : PP.ppstream -> Term.term -> unit
val type_to_string : Term.Type.hol_type -> string
val term_to_string : Term.term -> string
val print_type : Term.Type.hol_type -> unit
val print_term : Term.term -> unit
end;
