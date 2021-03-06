signature windowLib_sig =
sig
 type term
 type thm
 type goal
 type tactic
 type conv
 type rewrites
 type 'a signal
 type path
 type win_path
 type win_stack
 type window
 type window_rule
 type rule_id

 structure windowTheoryLoaded : windowTheoryLoaded_sig
 structure Hol_ext : Hol_ext_sig

val ADD_SUPPOSE : goal -> win_stack -> win_stack
val ADD_THEOREM : thm -> win_stack -> win_stack
val ALL_STACKS : unit -> string list
val ASM_REWRITE_WIN : thm list -> win_stack -> win_stack
val BEGIN_STACK : string -> term -> term list -> thm list -> unit
val BEGIN_STACK_TAC : thm list -> tactic
val CLOSE_WIN : win_stack -> win_stack
val CONJECTURE : term -> win_stack -> win_stack
val CONTEXT_LIST : (thm list -> win_stack -> win_stack) 
                     -> win_stack -> win_stack
val CONVERT_WIN : conv -> win_stack -> win_stack
val CURRENT_NAME : unit -> string
val CURRENT_STACK : unit -> win_stack
val DO : (win_stack -> win_stack) -> unit
val END_STACK : string -> unit
val END_STACK_TAC : unit -> tactic
val ESTABLISH : term -> win_stack -> win_stack
val FILTER_ASM_REWRITE_WIN 
    : (term -> bool) -> thm list -> win_stack -> win_stack
val FILTER_ONCE_ASM_REWRITE_WIN 
  : (term -> bool) -> thm list -> win_stack -> win_stack
val FILTER_PURE_ASM_REWRITE_WIN 
  : (term -> bool) -> thm list -> win_stack -> win_stack
val FILTER_PURE_ONCE_ASM_REWRITE_WIN 
  : (term -> bool) -> thm list -> win_stack -> win_stack
val FOC_RULE_WIN : (term -> thm) -> win_stack -> win_stack
val GEN_REWRITE_WIN 
  : (conv -> conv) -> rewrites -> thm list -> win_stack -> win_stack
val GET_STACK : string -> win_stack
val MATCH_TRANSFORM_WIN : thm -> win_stack -> win_stack
val ONCE_ASM_REWRITE_WIN : thm list -> win_stack -> win_stack
val ONCE_REWRITE_WIN : thm list -> win_stack -> win_stack
val OPEN_CONTEXT : term * path -> win_stack -> win_stack
val OPEN_WIN : path -> win_stack -> win_stack
val PRINT_STACK : unit -> unit
val PURE_ASM_REWRITE_WIN : thm list -> win_stack -> win_stack
val PURE_ONCE_ASM_REWRITE_WIN : thm list -> win_stack -> win_stack
val PURE_ONCE_REWRITE_WIN : thm list -> win_stack -> win_stack
val PURE_REWRITE_WIN : thm list -> win_stack -> win_stack
val REDO : unit -> unit
val REWRITE_WIN : thm list -> win_stack -> win_stack
val RULE_WIN : (thm -> thm) -> win_stack -> win_stack
val SAVE_WIN_THM : unit -> thm
val SET_MAX_HIST : int -> unit
val SET_STACK : string -> unit
val TACTIC_WIN : tactic -> win_stack -> win_stack
val THM_RULE_WIN : (thm -> thm) -> win_stack -> win_stack
val TRANSFORM_WIN : thm -> win_stack -> win_stack
val UNDO : unit -> unit
val UNDO_WIN : win_stack -> win_stack
val WIN_THM : unit -> thm
val add_relation : thm * thm -> unit
val add_suppose : goal -> window -> window
val add_theorem : thm -> window -> window
val add_weak : thm -> unit
val all_hypotheses : window -> term list
val bad_conjectures : win_stack -> term list
val beg_stack_sig : string signal
val bound : window -> term list
val boundin : path -> term -> term list
val cng_win_sig  : unit signal
val conjecture : term -> window -> window
val conjectures : window -> term list
val context : window -> term list
val convert_win : conv -> window -> window
val create_stack : window -> win_stack
val create_win : term -> term -> term list -> thm list -> window
val depth_stack : win_stack -> int
val disp_hypotheses : window -> term list
val end_stack_sig  : string signal
val foc_rule_win : (term -> thm) -> window -> window
val focus : window -> term
val get_thm : term -> window -> thm
val hyp_thms : window -> thm list
val hypotheses : window -> term list
val is_weaker : term -> term -> bool
val kill_rule : rule_id -> unit
val lemma_thms : window -> thm list
val lemmas : window -> term list
val make_win : term
               -> term
                 -> (term list * term) list
                   -> term list -> thm list -> thm list -> window
val match_transform_win : thm -> window -> window
val origin : window -> term
val pop_win_sig  : unit signal
val psh_win_sig  : unit signal
val reflexive : term -> thm
val relation : window -> term
val rule_win : (thm -> thm) -> window -> window
val search_rule : path -> (window_rule * rule_id) list
val set_stack_sig : string signal
val store_rule : window_rule -> rule_id
val suppositions : window -> goal list
val tactic_win : tactic -> window -> window
val thm_rule_win : (thm -> thm) -> window -> window
val top_path : win_stack -> win_path
val top_window : win_stack -> window
val transfer_sups_thms : window -> window -> window
val transform_win : thm -> window -> window
val transitive : thm -> thm
val traverse : path -> term -> term
val used_conjectures : window -> term list
val used_hypotheses : window -> term list
val weaken : term -> thm -> thm
val win_thm : window -> thm
val window_version : string
end;
