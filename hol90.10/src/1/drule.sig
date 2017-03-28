(* ===================================================================== *)
(* FILE          : drule.sig                                             *)
(* DESCRIPTION   : Signature for many derived rules of inference.        *)
(*                 Translated from hol88.                                *)
(*                                                                       *)
(* AUTHORS       : (c) Mike Gordon and                                   *)
(*                     Tom Melham, University of Cambridge, for hol88    *)
(* TRANSLATOR    : Konrad Slind, University of Calgary                   *)
(* DATE          : September 11, 1991                                    *)
(* ===================================================================== *)


signature Drule1_sig =
sig
structure Thm : Thm_sig
val ADD_ASSUM : Thm.Term.term -> Thm.thm -> Thm.thm
val UNDISCH : Thm.thm -> Thm.thm
val SYM : Thm.thm -> Thm.thm
val TRANS : Thm.thm -> Thm.thm -> Thm.thm
val IMP_TRANS : Thm.thm -> Thm.thm -> Thm.thm
val AP_TERM : Thm.Term.term -> Thm.thm -> Thm.thm
val AP_THM : Thm.thm -> Thm.Term.term -> Thm.thm
val EQ_MP : Thm.thm -> Thm.thm -> Thm.thm
val EQ_IMP_RULE : Thm.thm -> Thm.thm * Thm.thm
val TRUTH : Thm.thm
val EQT_ELIM : Thm.thm -> Thm.thm
val SPEC : Thm.Term.term -> Thm.thm -> Thm.thm
val SPECL : Thm.Term.term list -> Thm.thm -> Thm.thm
val EQT_INTRO : Thm.thm -> Thm.thm
val GEN : Thm.Term.term -> Thm.thm -> Thm.thm
val GENL : Thm.Term.term list -> Thm.thm -> Thm.thm
val ETA_CONV : Thm.Term.term -> Thm.thm
val EXT : Thm.thm -> Thm.thm
val SELECT_INTRO : Thm.thm -> Thm.thm
val SELECT_ELIM : Thm.thm -> Thm.Term.term * Thm.thm -> Thm.thm
val EXISTS : Thm.Term.term * Thm.Term.term -> Thm.thm -> Thm.thm
val disch : (Thm.Term.term * (Thm.Term.term list)) -> Thm.Term.term list
val CHOOSE : Thm.Term.term * Thm.thm -> Thm.thm -> Thm.thm
val SELECT_RULE : Thm.thm -> Thm.thm
val IMP_ANTISYM_RULE : Thm.thm -> Thm.thm -> Thm.thm
val SPEC_VAR : Thm.thm -> Thm.Term.term * Thm.thm
val MK_EXISTS : Thm.thm -> Thm.thm
val LIST_MK_EXISTS : Thm.Term.term list -> Thm.thm -> Thm.thm
val FORALL_EQ : Thm.Term.term -> Thm.thm -> Thm.thm
val EXISTS_EQ : Thm.Term.term -> Thm.thm -> Thm.thm
val SELECT_EQ : Thm.Term.term -> Thm.thm -> Thm.thm
val SUBS : Thm.thm list -> Thm.thm -> Thm.thm
val SUBS_OCCS : (int list * Thm.thm) list -> Thm.thm -> Thm.thm
val SUBST_CONV : {var:Thm.Term.term, thm:Thm.thm} list -> 
                 Thm.Term.term -> Thm.Term.term -> Thm.thm
val RIGHT_BETA : Thm.thm -> Thm.thm
val LIST_BETA_CONV : Thm.Term.term -> Thm.thm
val RIGHT_LIST_BETA : Thm.thm -> Thm.thm
end;

signature Drule2_sig =
sig
include Drule1_sig
val AND_INTRO_THM : Thm.thm
val CONJ : Thm.thm -> Thm.thm -> Thm.thm
val AND1_THM : Thm.thm
val CONJUNCT1 : Thm.thm -> Thm.thm
val AND2_THM : Thm.thm
val CONJUNCT2 : Thm.thm -> Thm.thm
val CONJ_SYM : Thm.thm
val CONJ_ASSOC : Thm.thm
val CONJUNCTS_CONV : Thm.Term.term * Thm.Term.term -> Thm.thm
val CONJ_SET_CONV : Thm.Term.term list -> Thm.Term.term list -> Thm.thm
val FRONT_CONJ_CONV : Thm.Term.term list -> Thm.Term.term -> Thm.thm
val CONJ_DISCH : Thm.Term.term -> Thm.thm -> Thm.thm
val CONJ_DISCHL : Thm.Term.term list -> Thm.thm -> Thm.thm
val OR_INTRO_THM1 : Thm.thm
val DISJ1 : Thm.thm -> Thm.Term.term -> Thm.thm
val OR_INTRO_THM2 : Thm.thm
val DISJ2 : Thm.Term.term -> Thm.thm -> Thm.thm
val OR_ELIM_THM : Thm.thm
val DISJ_CASES : Thm.thm -> Thm.thm -> Thm.thm -> Thm.thm
val FALSITY : Thm.thm
val IMP_F : Thm.thm
val NOT_INTRO : Thm.thm -> Thm.thm
val NEG_DISCH : Thm.Term.term -> Thm.thm -> Thm.thm
val F_IMP : Thm.thm
val NOT_ELIM : Thm.thm -> Thm.thm
val NOT_EQ_SYM : Thm.thm -> Thm.thm
val AND_CLAUSES : Thm.thm
val OR_CLAUSES : Thm.thm
val IMP_CLAUSES : Thm.thm
val CONTR : Thm.Term.term -> Thm.thm -> Thm.thm
val EQF_INTRO : Thm.thm -> Thm.thm
val EQF_ELIM : Thm.thm -> Thm.thm
val EXCLUDED_MIDDLE : Thm.thm
val CCONTR : Thm.Term.term -> Thm.thm -> Thm.thm
val INST : Thm.Term.term Lib.subst -> Thm.thm -> Thm.thm
val NOT_F : Thm.thm
val NOT_AND : Thm.thm
end;
signature Drule3_sig =
sig
include Drule2_sig
val ISPEC : Thm.Term.term -> Thm.thm -> Thm.thm
val ISPECL : Thm.Term.term list -> Thm.thm -> Thm.thm
val SELECT_REFL : Thm.thm
val SELECT_UNIQUE : Thm.thm
val GEN_ALL : Thm.thm -> Thm.thm
val DISCH_ALL : Thm.thm -> Thm.thm
val UNDISCH_ALL : Thm.thm -> Thm.thm
val SPEC_ALL : Thm.thm -> Thm.thm
val PROVE_HYP : Thm.thm -> Thm.thm -> Thm.thm
val CONJ_PAIR : Thm.thm -> Thm.thm * Thm.thm
val LIST_CONJ : Thm.thm list -> Thm.thm
val CONJ_LIST : int -> Thm.thm -> Thm.thm list
val CONJUNCTS : Thm.thm -> Thm.thm list
val BODY_CONJUNCTS : Thm.thm -> Thm.thm list
val IMP_CANON : Thm.thm -> Thm.thm list
val LIST_MP : Thm.thm list -> Thm.thm -> Thm.thm
val CONTRAPOS : Thm.thm -> Thm.thm
val DISJ_IMP : Thm.thm -> Thm.thm
val IMP_ELIM : Thm.thm -> Thm.thm
val NOT_CLAUSES : Thm.thm
val DISJ_CASES_UNION : Thm.thm -> Thm.thm -> Thm.thm -> Thm.thm
end;
signature Drule_sig =
sig
include Drule3_sig
val EQ_REFL : Thm.thm
val REFL_CLAUSE : Thm.thm
val EQ_SYM : Thm.thm
val EQ_SYM_EQ : Thm.thm
val EQ_EXT : Thm.thm
val EQ_TRANS : Thm.thm
val BOOL_EQ_DISTINCT : Thm.thm
val EQ_CLAUSES : Thm.thm
val MK_COMB : Thm.thm * Thm.thm -> Thm.thm
val MK_ABS : Thm.thm -> Thm.thm
val ALPHA_CONV : Thm.Term.term -> Thm.Term.term -> Thm.thm
val ALPHA : Thm.Term.term -> Thm.Term.term -> Thm.thm
val GEN_ALPHA_CONV : Thm.Term.term -> Thm.Term.term -> Thm.thm
val COND_CLAUSES : Thm.thm
val COND_ID : Thm.thm
val IMP_CONJ : Thm.thm -> Thm.thm -> Thm.thm
val EXISTS_IMP : Thm.Term.term -> Thm.thm -> Thm.thm
val FORALL_SIMP : Thm.thm
val EXISTS_SIMP : Thm.thm
val ABS_SIMP : Thm.thm
end;
