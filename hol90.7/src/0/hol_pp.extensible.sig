(* ===================================================================== *)
(* FILE          : hol_pp.sig                                            *)
(* DESCRIPTION   : Signature for the prettyprinting of HOL terms and     *)
(*                 types.                                                *)
(*                                                                       *)
(* AUTHOR        : Konrad Slind, University of Calgary                   *)
(* DATE          : August 26, 1991                                       *)
(* EXTENDED      : Richard Boulton, March 2, 1994                        *)
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
  
  structure Extend_hol_pp :
  sig
    datatype gravity = TOP | APPL | INFIX of int | WEAK | BOTTOM
    val gravity_geq : gravity -> gravity -> bool
    val extend_pp_type :
       (({depth:int, gravity:gravity} ->
         Term.Type.hol_type -> PP.ppstream -> unit) ->
        ({depth:int, gravity:gravity} ->
         Term.Type.hol_type -> PP.ppstream -> unit)) -> unit
    val extend_pp_term :
       (({boundvars:Term.term list, depth:int, gravity:gravity} ->
         Term.term -> PP.ppstream -> unit) ->
        ({boundvars:Term.term list, depth:int, gravity:gravity} ->
         Term.term -> PP.ppstream -> unit)) -> unit
    val reset_pp_type : unit -> unit
    val reset_pp_term : unit -> unit
  end
end;
