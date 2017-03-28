signature RETRIEVE_SIDECOND =
sig
 type hol_type
 type term

   val Contains : RetrieveStruct.wildvar * RetrieveStruct.termpattern ->
                  RetrieveMatching.thmpattern
   val contains : term * term -> RetrieveMatching.thmpattern
   val Matches : RetrieveStruct.wildvar * RetrieveStruct.termpattern ->
                 RetrieveMatching.thmpattern
   val matches : term * term -> RetrieveMatching.thmpattern
   val Has_body : RetrieveStruct.wildvar * RetrieveStruct.termpattern ->
                  RetrieveMatching.thmpattern
   val has_body : term * term -> RetrieveMatching.thmpattern

   val Test1term : (term -> bool) -> 
                   RetrieveStruct.wildvar ->
                   RetrieveMatching.thmpattern
   val test1term : (term -> bool) ->
                   term ->
                   RetrieveMatching.thmpattern
   val Test1type : (hol_type -> bool) ->
                   RetrieveStruct.wildtype ->
                   RetrieveMatching.thmpattern
   val test1type :(hol_type -> bool) -> hol_type -> RetrieveMatching.thmpattern
   val Test2terms : (term -> term -> bool) ->
                    RetrieveStruct.wildvar ->
                    RetrieveStruct.wildvar ->
                    RetrieveMatching.thmpattern
   val test2terms : (term -> term -> bool) 
                     -> term -> term -> RetrieveMatching.thmpattern
   val Test2types : (hol_type -> hol_type -> bool) ->
                    RetrieveStruct.wildtype ->
                    RetrieveStruct.wildtype ->
                    RetrieveMatching.thmpattern
   val test2types : (hol_type -> hol_type -> bool) ->
                    hol_type ->
                    hol_type ->
                    RetrieveMatching.thmpattern
end;
