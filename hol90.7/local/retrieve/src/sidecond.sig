signature RETRIEVE_SIDECOND =
sig
   val Contains : RetrieveStruct.wildvar * RetrieveStruct.termpattern ->
                  RetrieveMatching.thmpattern
   val contains : Term.term * Term.term -> RetrieveMatching.thmpattern
   val Matches : RetrieveStruct.wildvar * RetrieveStruct.termpattern ->
                 RetrieveMatching.thmpattern
   val matches : Term.term * Term.term -> RetrieveMatching.thmpattern
   val Has_body : RetrieveStruct.wildvar * RetrieveStruct.termpattern ->
                  RetrieveMatching.thmpattern
   val has_body : Term.term * Term.term -> RetrieveMatching.thmpattern

   val Test1term : (Term.term -> bool) ->
                   RetrieveStruct.wildvar ->
                   RetrieveMatching.thmpattern
   val test1term : (Term.term -> bool) ->
                   Term.term ->
                   RetrieveMatching.thmpattern
   val Test1type : (Type.hol_type -> bool) ->
                   RetrieveStruct.wildtype ->
                   RetrieveMatching.thmpattern
   val test1type : (Type.hol_type -> bool) ->
                   Type.hol_type ->
                   RetrieveMatching.thmpattern
   val Test2terms : (Term.term -> Term.term -> bool) ->
                    RetrieveStruct.wildvar ->
                    RetrieveStruct.wildvar ->
                    RetrieveMatching.thmpattern
   val test2terms : (Term.term -> Term.term -> bool) ->
                    Term.term ->
                    Term.term ->
                    RetrieveMatching.thmpattern
   val Test2types : (Type.hol_type -> Type.hol_type -> bool) ->
                    RetrieveStruct.wildtype ->
                    RetrieveStruct.wildtype ->
                    RetrieveMatching.thmpattern
   val test2types : (Type.hol_type -> Type.hol_type -> bool) ->
                    Type.hol_type ->
                    Type.hol_type ->
                    RetrieveMatching.thmpattern
end;
