signature Theory_data_sig =
sig
structure Thm : Thm_sig
type theory
type theory_id
val mk_theory_id : {name:string, timestamp:System.Timer.time} -> theory_id
val theory_id : theory -> theory_id
val theory_id_name : theory_id -> string
val theory_id_timestamp : theory_id -> System.Timer.time
val theory_id_eq : (theory_id * theory_id) -> bool

val theory_draft_mode : theory -> bool
val theory_consistent_with_disk : theory -> bool
val theory_parents : theory -> theory_id list
val theory_type_constants 
   : theory -> {tyc:Thm.Term.Type.hol_type, arity :int, theory:string} list
val theory_term_constants 
   : theory -> {const:Thm.Term.term, theory:string, place:Thm.Term.fixity} list
val theory_axioms : theory -> (string * Thm.thm) list
val theory_definitions : theory -> (string * Thm.thm) list
val theory_theorems : theory -> (string * Thm.thm) list

val mk_theory : theory_id -> theory
val fresh_theory : string -> theory
val the_current_theory : unit -> theory
val make_current : theory -> unit

val set_draft_mode : bool -> theory -> theory
val set_consistency_with_disk : bool -> theory -> theory
val add_parent : theory_id -> theory -> theory
val add_type : {tyc:Thm.Term.Type.hol_type, arity :int, theory:string}
                -> theory -> theory
val add_term : {const:Thm.Term.term, theory:string, place:Thm.Term.fixity}
                -> theory -> theory
val add_axiom : (string * Thm.thm) -> theory -> theory
val add_definition : (string * Thm.thm) -> theory -> theory 
val add_theorem : (string * Thm.thm) -> theory -> theory

val pp_theory : PP.ppstream -> theory -> unit
end;
