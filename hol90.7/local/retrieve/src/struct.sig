signature RETRIEVE_STRUCT =
sig
   type wildvar
   val show_wildvar : wildvar -> Term.term
   val make_wildvar : Term.term -> wildvar
   val wildvarlist : Term.term list -> wildvar list

   type wildtype
   val show_wildtype : wildtype -> Type.hol_type
   val make_wildtype : Type.hol_type -> wildtype
   val wildtypelist : Type.hol_type list -> wildtype list

   type termpattern
   val show_termpattern :
      termpattern -> Term.term * wildvar list * wildtype list
   val make_termpattern :
      Term.term * wildvar list * wildtype list -> termpattern
   val show_full_termpattern :
      termpattern -> Term.term * Term.term list * Type.hol_type list
   val make_full_termpattern :
      Term.term * Term.term list * Type.hol_type list -> termpattern
   val autotermpattern : Term.term -> termpattern

   type matching
   val show_matching :
      matching -> (wildvar * Term.term) list * (wildtype * Type.hol_type) list
   val null_matching : matching
   val make_matching : termpattern -> Term.term -> matching
   val join_matchings : matching -> matching -> matching
   val show_full_matching :
      matching ->
      (Term.term * Term.term) list * (Type.hol_type * Type.hol_type) list
   val match_of_var : matching -> wildvar -> Term.term
   val match_of_type : matching -> wildtype -> Type.hol_type

   datatype result_of_match = Nomatch
                            | Match of matching * (unit -> result_of_match)
   val Match_null : result_of_match
   val approms : (unit -> result_of_match) ->
                 (unit -> result_of_match) ->
                 (unit -> result_of_match)
   val bool_to_rom : bool -> result_of_match
   val rom_to_bool : result_of_match -> bool

   type side_condition
end;
