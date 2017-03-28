(* ===================================================================== *)
(* FILE          : thm.sig                                               *)
(* DESCRIPTION   : Signature for the "abstract data type" of theorems.   *)
(*                 Most of the inference rules have been translated from *)
(*                 hol88.                                                *)
(*                                                                       *)
(* AUTHORS       : (c) Mike Gordon, University of Cambridge              *)
(*                     Konrad Slind, University of Calgary               *)
(* DATE          : September 10, 1991                                    *)
(* ===================================================================== *)


signature Thm_sig =
sig
structure Term : Public_term_sig
type thm

(* Counting theorem production *)
val reset_thm_count : unit -> unit
(* Toggles switch that says whether to count inferences or not. *)
val counting_thms : bool -> unit
val thm_count : unit -> {ASSUME : int, REFL : int, BETA_CONV : int,
                         SUBST : int,  ABS : int,   DISCH : int,
                         MP : int, INST_TYPE : int, drule : int,
                         definition : int, axiom : int,
                         from_disk : int, valid_tac : int, other : int}
val hyp : thm -> Term.term list
val concl : thm -> Term.term
val dest_thm : thm -> (Term.term list * Term.term)
val thm_free_vars : thm -> Term.term list
val hyp_union : thm list -> Term.term list
val pp_thm : PP.ppstream -> thm -> unit
val thm_to_string : thm -> string
val print_thm : thm -> unit

(* The primitive rules of inference *)
val ASSUME : Term.term -> thm
val REFL : Term.term -> thm
val BETA_CONV : Term.term -> thm
val SUBST : {var:Term.term, thm:thm} list -> Term.term -> thm -> thm
val ABS : Term.term -> thm -> thm
val INST_TYPE : Term.Type.hol_type subst -> thm -> thm
val DISCH : Term.term -> thm -> thm
val MP : thm -> thm -> thm

val mk_axiom_thm : (Term.term list * Term.term) -> thm
val mk_definition_thm  : (Term.term list * Term.term) -> thm
val mk_drule_thm : (Term.term list * Term.term) -> thm
val mk_disk_thm  : (Term.term list * Term.term) -> thm
val mk_tac_thm  : (Term.term list * Term.term) -> thm
val mk_thm : (Term.term list * Term.term) -> thm
end;
