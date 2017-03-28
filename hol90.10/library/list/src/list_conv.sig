signature List_conv1_sig =
sig
   type term 
   type thm 
   type tactic
   type conv

  val LIST_INDUCT : thm * thm -> thm
  val LIST_INDUCT_TAC : tactic
  val SNOC_INDUCT_TAC : tactic
  val EQ_LENGTH_INDUCT_TAC : tactic
  val EQ_LENGTH_SNOC_INDUCT_TAC : tactic
  val new_list_rec_definition : string * term -> thm
  val new_infix_list_rec_definition : string * term * int -> thm
  val list_EQ_CONV : conv -> conv
  val LENGTH_CONV : conv
  val APPEND_CONV : conv
  val MAP_CONV : conv -> conv
  val FOLDR_CONV : conv -> conv
  val FOLDL_CONV : conv -> conv
  val list_FOLD_CONV : thm -> conv -> conv
  val SUM_CONV : conv
  val FILTER_CONV : conv -> conv
  val SNOC_CONV : conv
  val REVERSE_CONV : conv
  val FLAT_CONV : conv
  val EL_CONV : conv
  val ELL_CONV : conv
  val MAP2_CONV : conv -> conv
  val ALL_EL_CONV : conv -> conv
  val SOME_EL_CONV : conv -> conv
  val IS_EL_CONV : conv -> conv
  val AND_EL_CONV : conv
  val OR_EL_CONV : conv
  val LAST_CONV : conv
  val BUTLAST_CONV : conv
  val SEG_CONV : conv
  val LASTN_CONV : conv
  val BUTLASTN_CONV : conv
  val BUTFIRSTN_CONV : conv
  val FIRSTN_CONV : conv
  val SCANL_CONV : conv -> conv
  val SCANR_CONV : conv -> conv
  val REPLICATE_CONV : conv
  val GENLIST_CONV : conv -> conv
end;


signature List_conv_sig =
sig
   type term 
   type thm
   type tactic 
   type conv

  val LIST_INDUCT : thm * thm -> thm
  val LIST_INDUCT_TAC : tactic
  val SNOC_INDUCT_TAC : tactic
  val EQ_LENGTH_INDUCT_TAC : tactic
  val EQ_LENGTH_SNOC_INDUCT_TAC : tactic
  val new_list_rec_definition : string * term -> thm
  val new_infix_list_rec_definition : string * term * int -> thm
  val list_EQ_CONV : conv -> conv
  val LENGTH_CONV : conv
  val APPEND_CONV : conv
  val MAP_CONV : conv -> conv
  val FOLDR_CONV : conv -> conv
  val FOLDL_CONV : conv -> conv
  val list_FOLD_CONV : thm -> conv -> conv
  val SUM_CONV : conv
  val FILTER_CONV : conv -> conv
  val SNOC_CONV : conv
  val REVERSE_CONV : conv
  val FLAT_CONV : conv
  val EL_CONV : conv
  val ELL_CONV : conv
  val MAP2_CONV : conv -> conv
  val ALL_EL_CONV : conv -> conv
  val SOME_EL_CONV : conv -> conv
  val IS_EL_CONV : conv -> conv
  val AND_EL_CONV : conv
  val OR_EL_CONV : conv
  val LAST_CONV : conv
  val BUTLAST_CONV : conv
  val SEG_CONV : conv
  val LASTN_CONV : conv
  val BUTLASTN_CONV : conv
  val BUTFIRSTN_CONV : conv
  val FIRSTN_CONV : conv
  val SCANL_CONV : conv -> conv
  val SCANR_CONV : conv -> conv
  val REPLICATE_CONV : conv
  val GENLIST_CONV : conv -> conv
  val LIST_CONV : conv
  val X_LIST_CONV : {Aux_thms: thm list, Fold_thms: thm list} -> conv
  val PURE_LIST_CONV : {Aux_thms: thm list, Fold_thms: thm list} -> conv
  val set_list_thm_database : {Aux_thms: thm list, Fold_thms: thm list} -> unit
  val list_thm_database : unit -> {Aux_thms: thm list, Fold_thms: thm list}
end;
