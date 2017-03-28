signature RETRIEVE_MATCHING =
sig
   datatype thmkind = Axiom | Definition | Theorem;
   type foundthm

   type thmpattern
   val Any : thmpattern
   val None : thmpattern
   val Kind : thmkind -> thmpattern
   val Thryname : RetrieveName.namepattern -> thmpattern
   val Thmname : RetrieveName.namepattern -> thmpattern
   val Conc : RetrieveStruct.termpattern -> thmpattern
   val HypP : RetrieveStruct.termpattern list -> thmpattern
   val HypF : RetrieveStruct.termpattern list -> thmpattern
   val Side : RetrieveStruct.side_condition -> thmpattern
   val Andalso : (thmpattern * thmpattern) -> thmpattern
   val Orelse : (thmpattern * thmpattern) -> thmpattern
   val Not : thmpattern -> thmpattern
   val Where : (thmpattern * thmpattern) -> thmpattern
   val thmmatch : thmpattern -> (thmkind * string * string * Thm.thm) -> bool
   val thmfilter : thmpattern ->
                   (thmkind * string * string * Thm.thm) list -> 
                   (thmkind * string * string * Thm.thm) list
end;
