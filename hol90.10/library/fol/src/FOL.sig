(* ========================================================================= 
 * FOL <---> HOL
 * ========================================================================= *)

signature FOL_sig =
sig
 val offinc : int  (* offset for constants *)

 datatype fol_term = Var of int
                   | Fnapp of int * fol_term list

 type fol_atom
 datatype fol_form = Atom of (int * fol_term list)
                   | Conj of fol_form * fol_form
                   | Disj of fol_form * fol_form
                   | Forall of int * fol_form

 val fol_free_in : int -> fol_term -> bool
 val fol_frees : fol_term -> int list
 val fol_subst : (fol_term * int) list -> fol_term -> fol_term
 val fol_substl : (fol_term * int) list -> fol_term list -> fol_term list
 val fol_inst : (fol_term * int) list -> fol_atom -> fol_atom

 val augment_insts :fol_term*int -> (fol_term*int) list -> (fol_term*int) list
 val fol_unify :fol_term->fol_term->(fol_term*int) list -> (fol_term*int) list
 val form_inst : (fol_term * int) list -> fol_form -> fol_form

 val fol_eq : (fol_term * int) list -> fol_term -> fol_term -> bool
 val fol_atom_eq : (fol_term * int) list -> fol_atom -> fol_atom -> bool

 val augment_insts_bump 
   : int -> fol_term * int -> (fol_term * int) list -> (fol_term * int) list
 val fol_inst_bump : int -> (fol_term * int) list -> fol_atom -> fol_atom
 val fol_unify_bump 
   : int -> fol_term -> fol_term -> (fol_term*int) list -> (fol_term*int) list

end (* sig *)


