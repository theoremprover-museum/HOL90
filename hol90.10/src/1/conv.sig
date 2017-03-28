(* ===================================================================== *)
(* FILE          : conv.sig                                              *)
(* DESCRIPTION   : Signature for various conversions. Translated from    *)
(*                 hol88.                                                *)
(* AUTHORS       : (c) Many people at Cambridge:                         *)
(*                        Larry Paulson                                  *)
(*                        Mike Gordon                                    *)
(*                        Richard Boulton and                            *)
(*                        Tom Melham, University of Cambridge plus       *)
(*                     Paul Loewenstein, for hol88                       *)
(* TRANSLATOR    : Konrad Slind, University of Calgary                   *)
(* DATE          : September 11, 1991                                    *)
(* ===================================================================== *)


signature Conv_sig =
sig
structure Thm : Thm_sig
val INST_TY_TERM :(Thm.Term.term Lib.subst * Thm.Term.Type.hol_type Lib.subst) -> 
                  Thm.thm -> Thm.thm
val GSPEC : Thm.thm -> Thm.thm
val PART_MATCH : (Thm.Term.term -> Thm.Term.term) -> Thm.thm -> Abbrev.conv
val REWR_CONV : Thm.thm -> Abbrev.conv
val MATCH_MP : Thm.thm -> Thm.thm -> Thm.thm
val NO_CONV : Abbrev.conv
val ALL_CONV : Abbrev.conv
val THENC : (Abbrev.conv * Abbrev.conv) -> Abbrev.conv
val ORELSEC : (Abbrev.conv * Abbrev.conv) -> Abbrev.conv
val FIRST_CONV : Abbrev.conv list -> Abbrev.conv
val EVERY_CONV : Abbrev.conv list -> Abbrev.conv
val REPEATC : Abbrev.conv -> Abbrev.conv
val CHANGED_CONV : Abbrev.conv -> Abbrev.conv
val TRY_CONV : Abbrev.conv -> Abbrev.conv
val SUB_CONV : Abbrev.conv -> Abbrev.conv
val DEPTH_CONV : Abbrev.conv -> Abbrev.conv
val REDEPTH_CONV : Abbrev.conv -> Abbrev.conv
val TOP_DEPTH_CONV : Abbrev.conv -> Abbrev.conv
val ONCE_DEPTH_CONV : Abbrev.conv -> Abbrev.conv
val CONV_RULE : Abbrev.conv -> Thm.thm -> Thm.thm
val CONV_TAC : Abbrev.conv -> Abbrev.tactic
val BETA_RULE : Thm.thm -> Thm.thm
val BETA_TAC : Abbrev.tactic
val NOT_FORALL_CONV : Abbrev.conv
val NOT_EXISTS_CONV : Abbrev.conv
val EXISTS_NOT_CONV : Abbrev.conv
val FORALL_NOT_CONV : Abbrev.conv
val FORALL_AND_CONV : Abbrev.conv
val EXISTS_OR_CONV : Abbrev.conv
val AND_FORALL_CONV : Abbrev.conv
val LEFT_AND_FORALL_CONV : Abbrev.conv
val RIGHT_AND_FORALL_CONV : Abbrev.conv
val OR_EXISTS_CONV : Abbrev.conv
val LEFT_OR_EXISTS_CONV : Abbrev.conv
val RIGHT_OR_EXISTS_CONV : Abbrev.conv
val EXISTS_AND_CONV : Abbrev.conv
val AND_EXISTS_CONV : Abbrev.conv
val LEFT_AND_EXISTS_CONV : Abbrev.conv
val RIGHT_AND_EXISTS_CONV : Abbrev.conv
val FORALL_OR_CONV : Abbrev.conv
val OR_FORALL_CONV : Abbrev.conv
val LEFT_OR_FORALL_CONV : Abbrev.conv
val RIGHT_OR_FORALL_CONV : Abbrev.conv
val FORALL_IMP_CONV : Abbrev.conv
val LEFT_IMP_EXISTS_CONV : Abbrev.conv
val RIGHT_IMP_FORALL_CONV : Abbrev.conv
val EXISTS_IMP_CONV : Abbrev.conv
val LEFT_IMP_FORALL_CONV : Abbrev.conv
val RIGHT_IMP_EXISTS_CONV : Abbrev.conv
val X_SKOLEM_CONV : Thm.Term.term -> Abbrev.conv
val SKOLEM_CONV : Abbrev.conv
val SYM_CONV : Abbrev.conv
val RIGHT_CONV_RULE : Abbrev.conv -> Thm.thm -> Thm.thm
val FUN_EQ_CONV : Abbrev.conv
val X_FUN_EQ_CONV : Thm.Term.term -> Abbrev.conv
val SELECT_CONV : Abbrev.conv
val CONTRAPOS_CONV : Abbrev.conv
val ANTE_CONJ_CONV : Abbrev.conv
val SWAP_EXISTS_CONV : Abbrev.conv
val RAND_CONV : Abbrev.conv -> Abbrev.conv
val RATOR_CONV : Abbrev.conv -> Abbrev.conv
val ABS_CONV : Abbrev.conv -> Abbrev.conv
val bool_EQ_CONV : Abbrev.conv
val EXISTS_UNIQUE_CONV : Abbrev.conv
val COND_CONV : Abbrev.conv
val EXISTENCE : Thm.thm -> Thm.thm
val AC_CONV : Thm.thm * Thm.thm -> Abbrev.conv
val GSYM : Thm.thm -> Thm.thm
end;
