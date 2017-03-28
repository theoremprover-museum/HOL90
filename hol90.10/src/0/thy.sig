signature Theory_sig = 
sig
  structure Thm : Thm_sig

(* Adding to the current theory *)
  val new_parent : string -> unit
  val new_type : {Name : string, Arity : int} -> unit
  val new_constant :{Name : string, Ty : Thm.Term.Type.hol_type} -> unit
  val new_infix : {Name: string, Ty: Thm.Term.Type.hol_type, Prec: int} -> unit
  val new_binder : {Name : string, Ty : Thm.Term.Type.hol_type} -> unit
  val new_open_axiom : string * Thm.Term.term -> Thm.thm
  val store_definition : string * Thm.Term.term -> Thm.thm
  val save_thm : string * Thm.thm -> Thm.thm

(* Information on constants *)
  val arity : string -> int
  val fixity : string -> Thm.Term.fixity
  val precedence : string -> int
  val const_decl : string -> {const:Thm.Term.term,
                              theory : string,
                              place: Thm.Term.fixity}

  val is_constant : string -> bool
  val is_type : string -> bool
  val is_binder : string -> bool
  val is_infix : string -> bool

(* Information on the current theory *)
  val draft_mode : unit -> bool
  val current_theory : unit -> string
  val parents : string -> string list
  val ancestry : string -> string list
  val types : string -> {Name :string, Arity :int} list
  val constants : string -> Thm.Term.term list
  val infixes : string -> Thm.Term.term list
  val binders : string -> Thm.Term.term list
  val axioms : string -> (string * Thm.thm) list
  val axiom : string -> string -> Thm.thm
  val definitions : string -> (string * Thm.thm) list
  val definition : string -> string -> Thm.thm
  val theorems : string -> (string * Thm.thm) list
  val theorem : string -> string -> Thm.thm
(*
  val print_theory_to_outstream : {outstream:Portable.outstream, theory:string}
                                   -> Portable.outstream
  val print_theory_to_file : {file:string, theory:string} -> unit
*)
  val print_theory :unit -> unit

(* Operations that change the current theory *)
  val new_theory : string -> unit

(* Operations that write the theory to disk *)
  val export_theory : unit -> unit

(* Support operations for theories-as-structures *)
  val raw_term_parser : Thm.Term.term vector -> 'a frag list -> Thm.Term.term

  val install_type : string*int*string -> unit
  val install_const : string * Thm.Term.Type.hol_type * Thm.Term.fixity * thy 
                      -> unit
  val add_parentage : string*int*int -> (string*int*int)list -> unit
end;