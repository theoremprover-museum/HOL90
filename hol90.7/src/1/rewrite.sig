(* ===================================================================== *)
(* FILE          : rewrite.sig                                           *)
(* DESCRIPTION   : Signature for the rewriting routines. Translated from *)
(*                 hol88.                                                *)
(*                                                                       *)
(* AUTHOR        : (c) Larry Paulson, University of Cambridge, for hol88 *)
(* TRANSLATOR    : Konrad Slind, University of Calgary                   *)
(* DATE          : September 11, 1991                                    *)
(* ===================================================================== *)


signature Rewrite_sig =
sig
structure Base_logic : Base_logic_sig

type rewrites
val empty_rewrites : rewrites
val add_rewrites : rewrites -> Base_logic.Thm.thm list -> rewrites
val set_base_rewrites : rewrites -> unit
val base_rewrites : unit -> rewrites
val add_base_rewrites : Base_logic.Thm.thm list -> unit
val pp_rewrites : PP.ppstream -> rewrites -> unit

val REWRITES_CONV : rewrites -> conv

val GEN_REWRITE_CONV : (conv -> conv)
                         -> rewrites -> Base_logic.Thm.thm list -> conv
val GEN_REWRITE_RULE : (conv -> conv) 
                         -> rewrites -> Base_logic.Thm.thm list
                             -> Base_logic.Thm.thm -> Base_logic.Thm.thm
val GEN_REWRITE_TAC : (conv -> conv) 
                        -> rewrites -> Base_logic.Thm.thm list -> tactic

val PURE_REWRITE_CONV : Base_logic.Thm.thm list -> conv
val REWRITE_CONV : Base_logic.Thm.thm list -> conv
val PURE_ONCE_REWRITE_CONV : Base_logic.Thm.thm list -> conv
val ONCE_REWRITE_CONV : Base_logic.Thm.thm list -> conv

val PURE_REWRITE_RULE : Base_logic.Thm.thm list -> 
                        Base_logic.Thm.thm -> Base_logic.Thm.thm
val REWRITE_RULE : Base_logic.Thm.thm list -> 
                   Base_logic.Thm.thm -> Base_logic.Thm.thm
val PURE_ONCE_REWRITE_RULE : Base_logic.Thm.thm list -> 
                             Base_logic.Thm.thm -> Base_logic.Thm.thm
val ONCE_REWRITE_RULE : Base_logic.Thm.thm list -> 
                        Base_logic.Thm.thm -> Base_logic.Thm.thm
val PURE_ASM_REWRITE_RULE : Base_logic.Thm.thm list -> 
                            Base_logic.Thm.thm -> Base_logic.Thm.thm
val ASM_REWRITE_RULE : Base_logic.Thm.thm list -> 
                       Base_logic.Thm.thm -> Base_logic.Thm.thm
val PURE_ONCE_ASM_REWRITE_RULE : Base_logic.Thm.thm list -> 
                                 Base_logic.Thm.thm -> Base_logic.Thm.thm
val ONCE_ASM_REWRITE_RULE : Base_logic.Thm.thm list -> 
                            Base_logic.Thm.thm -> Base_logic.Thm.thm

val PURE_REWRITE_TAC : Base_logic.Thm.thm list -> tactic
val REWRITE_TAC : Base_logic.Thm.thm list -> tactic
val PURE_ONCE_REWRITE_TAC : Base_logic.Thm.thm list -> tactic
val ONCE_REWRITE_TAC : Base_logic.Thm.thm list -> tactic
val PURE_ASM_REWRITE_TAC : Base_logic.Thm.thm list -> tactic
val ASM_REWRITE_TAC : Base_logic.Thm.thm list -> tactic
val PURE_ONCE_ASM_REWRITE_TAC : Base_logic.Thm.thm list -> tactic
val ONCE_ASM_REWRITE_TAC : Base_logic.Thm.thm list -> tactic

val FILTER_PURE_ASM_REWRITE_RULE :(Base_logic.Net.Term.term -> bool) -> 
                                   Base_logic.Thm.thm list -> 
                                   Base_logic.Thm.thm -> Base_logic.Thm.thm
val FILTER_ASM_REWRITE_RULE :(Base_logic.Net.Term.term -> bool) -> 
                             Base_logic.Thm.thm list -> Base_logic.Thm.thm ->
                             Base_logic.Thm.thm
val FILTER_PURE_ONCE_ASM_REWRITE_RULE :(Base_logic.Net.Term.term -> bool) -> 
                                       Base_logic.Thm.thm list -> 
                                       Base_logic.Thm.thm -> Base_logic.Thm.thm
val FILTER_ONCE_ASM_REWRITE_RULE :(Base_logic.Net.Term.term -> bool) -> 
                                  Base_logic.Thm.thm list -> 
                                  Base_logic.Thm.thm -> Base_logic.Thm.thm
val FILTER_PURE_ASM_REWRITE_TAC :(Base_logic.Net.Term.term -> bool) -> 
                                 Base_logic.Thm.thm list -> tactic
val FILTER_ASM_REWRITE_TAC :(Base_logic.Net.Term.term -> bool) -> 
                            Base_logic.Thm.thm list -> tactic
val FILTER_PURE_ONCE_ASM_REWRITE_TAC :(Base_logic.Net.Term.term -> bool) -> 
                                      Base_logic.Thm.thm list -> tactic
val FILTER_ONCE_ASM_REWRITE_TAC :(Base_logic.Net.Term.term -> bool) -> 
                                 Base_logic.Thm.thm list -> tactic

val SUBST_MATCH : Base_logic.Thm.thm -> 
                  Base_logic.Thm.thm -> Base_logic.Thm.thm
end;
