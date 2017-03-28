signature Hol_ext_sig =
sig

type hol_type
type term
type thm
type goal
type conv

  val true_tm : term
  val false_tm : term
  val imp_tm : term 
  val pmi_tm : term 
  val equiv_tm : term 

  val bndvar : term -> term

  val term_mem : term -> term list -> bool
  val term_subset : term list -> term list -> bool
  val term_setify : term list -> term list
  val term_intersect : term list -> term list -> term list
  val term_union : term list -> term list -> term list
  val term_subtract : term list -> term list -> term list

  val better_thm : thm -> thm -> bool
  val better_goal :goal -> goal -> bool
  val thm_subset : thm list -> thm list -> bool
  val thm_set_equal : thm list -> thm list -> bool

  val goal_subset : goal list -> goal list -> bool
  val goal_set_equal : goal list -> goal list -> bool

  val thm_setify : thm list -> thm list
  val goal_setify : goal list -> goal list

  val thm_subtract : thm list -> thm list -> thm list
  val goal_subtract: goal list -> goal list -> goal list

  val fun_type : hol_type list -> hol_type             
  val is_fun : term -> bool
  val dom : term -> hol_type
  val ran : term -> hol_type
  val is_trueimp : term -> bool
  val is_pmi : term -> bool

  val dest_pmi : term -> {ant:term, conseq:term}
  val IMP_PMI_CONV : conv
  val IMP_PMI : thm -> thm
  val PMI_IMP : thm -> thm

  val PMI_TRANS : thm -> thm -> thm

  val EXISTS_PMI : term -> thm -> thm

  val SMASH : thm -> thm list
  val prove_hyp : goal -> goal -> goal

end;
