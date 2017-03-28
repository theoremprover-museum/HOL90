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
val INST_TY_TERM :(Thm.Term.term subst * Thm.Term.Type.hol_type subst) -> 
                  Thm.thm -> Thm.thm
val GSPEC : Thm.thm -> Thm.thm
val PART_MATCH : (Thm.Term.term -> Thm.Term.term) -> Thm.thm -> conv
val REWR_CONV : Thm.thm -> conv
val MATCH_MP : Thm.thm -> Thm.thm -> Thm.thm
val NO_CONV : conv
val ALL_CONV : conv
val THENC : (conv * conv) -> conv
val ORELSEC : (conv * conv) -> conv
val FIRST_CONV : conv list -> conv
val EVERY_CONV : conv list -> conv
val REPEATC : conv -> conv
val CHANGED_CONV : conv -> conv
val TRY_CONV : conv -> conv
val SUB_CONV : conv -> conv
val DEPTH_CONV : conv -> conv
val REDEPTH_CONV : conv -> conv
val TOP_DEPTH_CONV : conv -> conv
val ONCE_DEPTH_CONV : conv -> conv
val CONV_RULE : conv -> Thm.thm -> Thm.thm
val CONV_TAC : conv -> tactic
val BETA_RULE : Thm.thm -> Thm.thm
val BETA_TAC : tactic
val NOT_FORALL_CONV : conv
val NOT_EXISTS_CONV : conv
val EXISTS_NOT_CONV : conv
val FORALL_NOT_CONV : conv
val FORALL_AND_CONV : conv
val EXISTS_OR_CONV : conv
val AND_FORALL_CONV : conv
val LEFT_AND_FORALL_CONV : conv
val RIGHT_AND_FORALL_CONV : conv
val OR_EXISTS_CONV : conv
val LEFT_OR_EXISTS_CONV : conv
val RIGHT_OR_EXISTS_CONV : conv
val EXISTS_AND_CONV : conv
val AND_EXISTS_CONV : conv
val LEFT_AND_EXISTS_CONV : conv
val RIGHT_AND_EXISTS_CONV : conv
val FORALL_OR_CONV : conv
val OR_FORALL_CONV : conv
val LEFT_OR_FORALL_CONV : conv
val RIGHT_OR_FORALL_CONV : conv
val FORALL_IMP_CONV : conv
val LEFT_IMP_EXISTS_CONV : conv
val RIGHT_IMP_FORALL_CONV : conv
val EXISTS_IMP_CONV : conv
val LEFT_IMP_FORALL_CONV : conv
val RIGHT_IMP_EXISTS_CONV : conv
val X_SKOLEM_CONV : Thm.Term.term -> conv
val SKOLEM_CONV : conv
val SYM_CONV : conv
val RIGHT_CONV_RULE : conv -> Thm.thm -> Thm.thm
val FUN_EQ_CONV : conv
val X_FUN_EQ_CONV : Thm.Term.term -> conv
val SELECT_CONV : conv
val CONTRAPOS_CONV : conv
val ANTE_CONJ_CONV : conv
val SWAP_EXISTS_CONV : conv
val RAND_CONV : conv -> conv
val RATOR_CONV : conv -> conv
val ABS_CONV : conv -> conv
val bool_EQ_CONV : conv
val EXISTS_UNIQUE_CONV : conv
val COND_CONV : conv
val EXISTENCE : Thm.thm -> Thm.thm
val AC_CONV : Thm.thm * Thm.thm -> conv
val GSYM : Thm.thm -> Thm.thm
end;
