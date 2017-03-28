signature RETRIEVE_EXTRACT =
sig
 type hol_type
 type term

   val get_ids : term -> (term list * term list * term list)
   val get_consts : term -> term list
   val get_freevars : term -> term list
   val get_boundvars : term -> term list
   val get_types : term -> hol_type list
   val is_primtype : hol_type -> bool
   val subtypes : hol_type -> hol_type list
   val prim_subtypes : hol_type -> hol_type list
   val get_primtypes : term -> hol_type list
   val get_primvartypes : term -> hol_type list
end;
