signature RETRIEVE_STRUCT =
sig
 type term
 type hol_type
 type side_condition

   type wildvar
   val show_wildvar : wildvar -> term
   val make_wildvar : term -> wildvar
   val wildvarlist : term list -> wildvar list

   type wildtype
   val show_wildtype : wildtype -> hol_type
   val make_wildtype : hol_type -> wildtype
   val wildtypelist : hol_type list -> wildtype list

   type termpattern
   val show_termpattern :
      termpattern -> term * wildvar list * wildtype list
   val make_termpattern :
      term * wildvar list * wildtype list -> termpattern
   val show_full_termpattern :
      termpattern -> term * term list * hol_type list
   val make_full_termpattern :
      term * term list * hol_type list -> termpattern
   val autotermpattern : term -> termpattern

   type matching
   val show_matching :
      matching -> (wildvar * term) list * (wildtype * hol_type) list
   val null_matching : matching
   val make_matching : termpattern -> term -> matching
   val join_matchings : matching -> matching -> matching
   val show_full_matching :
      matching ->
      (term * term) list * (hol_type * hol_type) list
   val match_of_var : matching -> wildvar -> term
   val match_of_type : matching -> wildtype -> hol_type

   datatype result_of_match = Nomatch
                            | Match of matching * (unit -> result_of_match)
   val Match_null : result_of_match
   val approms : (unit -> result_of_match) ->
                 (unit -> result_of_match) ->
                 (unit -> result_of_match)
   val bool_to_rom : bool -> result_of_match
   val rom_to_bool : result_of_match -> bool

end;
