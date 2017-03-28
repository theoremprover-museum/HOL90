signature RETRIEVE_USER =
sig
 type term
   val FT : RetrieveMatching.thmpattern ->
            RetrieveSearch.source ->
            RetrieveSearch.searchstep
   val CS : RetrieveSearch.searchstep -> RetrieveSearch.searchstep
   val run_search : RetrieveSearch.searchstep -> RetrieveMatching.foundthm list
   val full_search : RetrieveMatching.thmpattern ->
                     RetrieveSearch.source ->
                     RetrieveMatching.foundthm list
   val search_until_find :
      RetrieveSearch.searchstep -> RetrieveSearch.searchstep
   val search_n_theories :
      int -> RetrieveSearch.searchstep -> RetrieveSearch.searchstep
   val search_n_until_find :
      int -> RetrieveSearch.searchstep -> RetrieveSearch.searchstep

   val ancestors_excluding :
      string list -> string list -> RetrieveSearch.searchpath
   val Ancestry : string list -> RetrieveSearch.searchpath
   val List_from : RetrieveSearch.searchstep -> RetrieveSearch.source

   val kind : RetrieveMatching.thmkind -> RetrieveMatching.thmpattern
   val thryname : string -> RetrieveMatching.thmpattern
   val thmname : string -> RetrieveMatching.thmpattern
   val conc : term -> RetrieveMatching.thmpattern
   val hypP : term list -> RetrieveMatching.thmpattern
   val hypF : term list -> RetrieveMatching.thmpattern
   val side : RetrieveStruct.side_condition -> RetrieveMatching.thmpattern
   val BigAnd : RetrieveMatching.thmpattern list -> RetrieveMatching.thmpattern
   val BigOr : RetrieveMatching.thmpattern list -> RetrieveMatching.thmpattern
end;
