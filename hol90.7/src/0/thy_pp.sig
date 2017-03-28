signature Thy_pp_sig =
sig
  structure Term : Public_term_sig
  val pp_type_rep : PP.ppstream -> Term.Type.hol_type -> unit
  val pp_term : PP.ppstream -> Term.term -> unit
end;
