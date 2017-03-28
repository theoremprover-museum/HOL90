(* ========================================================================= 
 * FOL <---> HOL
 * ========================================================================= *)

signature FOL_HOL_sig =
sig
    type term

    val reset_vars : unit -> unit
    val fol_of_var : term -> int
    val hol_of_var : int -> term

    val reset_consts : unit -> unit
    val fol_of_const : term -> int
    val hol_of_const : int -> term

    val fol_of_term : term list -> term list -> term -> FOL.fol_term
    val fol_of_atom : term list -> term list -> term -> FOL.fol_atom
    val fol_of_literal : term list -> term list -> term -> FOL.fol_atom
    val fol_of_form : term list -> term list -> term -> FOL.fol_form
    val hol_of_term : FOL.fol_term -> term
    val hol_of_atom : FOL.fol_atom -> term
    val hol_of_literal : FOL.fol_atom -> term
	
end (* sig *)


