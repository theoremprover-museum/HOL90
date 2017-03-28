signature RETRIEVE_EXTRACT =
sig
   val get_ids :
      Term.term -> (Term.term list * Term.term list * Term.term list)
   val get_consts : Term.term -> Term.term list
   val get_freevars : Term.term -> Term.term list
   val get_boundvars : Term.term -> Term.term list
   val get_types : Term.term -> Type.hol_type list
   val is_primtype : Type.hol_type -> bool
   val subtypes : Type.hol_type -> Type.hol_type list
   val prim_subtypes : Type.hol_type -> Type.hol_type list
   val get_primtypes : Term.term -> Type.hol_type list
   val get_primvartypes : Term.term -> Type.hol_type list
end;
