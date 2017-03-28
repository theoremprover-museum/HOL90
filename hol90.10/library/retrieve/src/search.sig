signature RETRIEVE_SEARCH =
sig
   datatype searchpath = Theory of string
                       | Ancestors of string list * string list
   datatype source = List of RetrieveMatching.foundthm list
                   | Paths of searchpath list
   val searchseq : string list -> string list -> string list
   val flatten_paths : searchpath list -> string list
   datatype searchstep = Endofsearch of RetrieveMatching.foundthm list
                       | Step of RetrieveMatching.foundthm list *
                                 (unit -> searchstep)
   val display_search : bool ref
   val find_theorems : RetrieveMatching.thmpattern -> source -> searchstep
   val show_step : searchstep -> RetrieveMatching.foundthm list
   val continue_search : searchstep -> searchstep
end;
