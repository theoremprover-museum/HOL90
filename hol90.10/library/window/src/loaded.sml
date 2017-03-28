(*---------------------------------------------------------------------------
 * This ensures that the "window" theory is loaded. 
 *---------------------------------------------------------------------------*)
structure windowTheoryLoaded : windowTheoryLoaded_sig =
struct
  type thm = CoreHol.Thm.thm

 val _ = Lib.try (CoreHol.Theory.loadLibThry "window") "window";

  val definition = CoreHol.Theory.definition
  val theorem = CoreHol.Theory.theorem

  val PMI_DEF = definition"window" "PMI_DEF"

   val IMP_REFL_THM = theorem "window" "IMP_REFL_THM"; 
   val IMP_TRANS_THM = theorem "window" "IMP_TRANS_THM";
   val PMI_REFL_THM = theorem "window" "PMI_REFL_THM"; 
   val PMI_TRANS_THM = theorem "window" "PMI_TRANS_THM";
   val COND1_THM = theorem "window" "COND1_THM";
   val COND2_THM = theorem "window" "COND2_THM";
   val BODY2_THM = theorem "window" "BODY2_THM";
   val LET_THM = theorem "window" "LET_THM"; 
   val CONJ1_THM = theorem "window" "CONJ1_THM";
   val CONJ2_THM = theorem "window" "CONJ2_THM";
   val IMP1_THM = theorem "window" "IMP1_THM";
   val IMP2_THM = theorem "window" "IMP2_THM";
   val PMI1_THM = theorem "window" "PMI1_THM";
   val PMI2_THM = theorem "window" "PMI2_THM";
   val DISJ1_THM = theorem "window" "DISJ1_THM";
   val DISJ2_THM = theorem "window" "DISJ2_THM";
   val DNEG_THM = theorem "window" "DNEG_THM";
   val NOT_DISJ_THM = theorem "window" "NOT_DISJ_THM";
   val NOT_IMP_THM = theorem "window" "NOT_IMP_THM";
   val NOT_PMI_THM = theorem "window" "NOT_PMI_THM";
   val COND_ABF_THM = theorem "window" "COND_ABF_THM";
   val COND_AFC_THM = theorem "window" "COND_AFC_THM";
   val IMP_CONJ1_THM = theorem "window" "IMP_CONJ1_THM";
   val IMP_CONJ2_THM = theorem "window" "IMP_CONJ2_THM";
   val IMP_IMP1_THM = theorem "window" "IMP_IMP1_THM";
   val IMP_IMP2_THM = theorem "window" "IMP_IMP2_THM";
   val IMP_PMI1_THM = theorem "window" "IMP_PMI1_THM";
   val IMP_PMI2_THM = theorem "window" "IMP_PMI2_THM";
   val IMP_DISJ1_THM = theorem "window" "IMP_DISJ1_THM";
   val IMP_DISJ2_THM = theorem "window" "IMP_DISJ2_THM";
   val IMP_NEG_THM = theorem "window" "IMP_NEG_THM";
   val PMI_CONJ1_THM = theorem "window" "PMI_CONJ1_THM";
   val PMI_CONJ2_THM = theorem "window" "PMI_CONJ2_THM";
   val PMI_IMP1_THM = theorem "window" "PMI_IMP1_THM";
   val PMI_IMP2_THM = theorem "window" "PMI_IMP2_THM";
   val PMI_PMI1_THM = theorem "window" "PMI_PMI1_THM";
   val PMI_PMI2_THM = theorem "window" "PMI_PMI2_THM";
   val PMI_DISJ1_THM = theorem "window" "PMI_DISJ1_THM";
   val PMI_DISJ2_THM = theorem "window" "PMI_DISJ2_THM";
   val PMI_NEG_THM = theorem "window" "PMI_NEG_THM";

end;