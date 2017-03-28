(************************ mk_apply_f_until_finished.sml *****************)
(*                                                                      *)
(* Author: Ralf Reetz                                                   *)
(* Date:   5.10.1994                                                    *)
(*                                                                      *)
(* Description:                                                         *)
(*                                                                      *)
(*   Theory about the repeated application of f:'a->'a to x:'a          *)
(*                                                                      *)
(* Used files:                                                          *)
(* Used modules:                                                        *)
(* Used theories:  prim_rec                                             *)
(* Used libraries: more_utils                                           *)
(*                                                                      *)
(************************************************************************)

new_theory "apply_f_until_finished";

val _ = load_library{lib=(find_library "more_utils"),theory="-"};

(*------------------definitions--------------------------------------------*)

new_recursive_definition
{name="apply_f_cond_n_times",
 fixity = Prefix,
 rec_axiom = (theorem "prim_rec" "num_Axiom"),
 def       = (--`
 (apply_f_cond_n_times (finished:'a->bool) (f:'a->'a) (x:'a) 0 = x)
 /\
 (apply_f_cond_n_times finished f x (SUC n) = 
 (finished (apply_f_cond_n_times finished f x n) => 
 apply_f_cond_n_times finished f x n
 |
 f (apply_f_cond_n_times finished f x n)))`--)};

new_definition("apply_f_until_finished",--`
 apply_f_until_finished (finished:'a->bool) (f:'a->'a) (x:'a) =
 (@y.finished y /\ ?n.(apply_f_cond_n_times finished f x n) = y)`--);

(*----------------theorems--------------------------------------------------*)

val FINISHED_IMPLIES_NO_CHANGE =
 save_thm("FINISHED_IMPLIES_NO_CHANGE",
 mk_thm([],
 --`!finished f (x:'a).
    ?n0.finished(apply_f_cond_n_times finished f x n0) ==>
    (!n.(n0<=n) ==> 
    ((apply_f_cond_n_times finished f x n)=
    (apply_f_cond_n_times finished f x n0)))
 `--));

val FINISHED_IMPLIES_LOWEST =
 save_thm("FINISHED_IMPLIES_LOWEST",
 mk_thm([],
 --`!finished f (x:'a).
    ?n.finished(apply_f_cond_n_times finished f x n) ==>
    ?!n0.finished(apply_f_cond_n_times finished f x n0)
 `--));

val FINISHED_UNIQUE =
 save_thm("FINISHED_UNIQUE",
 mk_thm([],
 --`!finished f (x:'a) y z.
    (finished z /\ (?n.apply_f_cond_n_times finished f x n = z)) /\
     finished y /\ (?n.apply_f_cond_n_times finished f x n = y) ==>
     (z = y)`--));

val apply_f_until_finished_TERMINATE_CASE =
 save_thm("apply_f_until_finished_TERMINATE_CASE",
 prove(--`
  !finished f (y:'a) x.
  finished y /\ (?n.(apply_f_cond_n_times finished f x n) = y) ==>
  ((apply_f_until_finished finished f x) = y)`--,
  EVERY [
   REPEAT GEN_TAC,
   PURE_ONCE_REWRITE_TAC [definition "-" "apply_f_until_finished"],
   DISCH_TAC,
   more_utils.SELECT_UNIQUE_TAC THENL [
    ASM_REWRITE_TAC []
    ,
    REWRITE_TAC [FINISHED_UNIQUE]
   ]
  ]));

close_theory();
export_theory();
