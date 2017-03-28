(* File: MLexbind_eval.sml *)

(* eval_exbind_pred gives the conditions that a potential relation must
   satisfy in order to be the evaluation relation for exception bindings --
   namely, it must satisfy the rules 138 and 139.
   (eval_exbind eb s E s' eep = true) means that the exception binding
    eb, evaluated in environment E and initial state s results in the 
    exception environment or packet eep and the new state s'. *)

(* exbind ::= EXBIND1 excon (exbind option) |
              EXBIND2 excon (excon long) (exbind option) *)

val eval_exbind_pred_def = 
--`!(eval_exbind:exbind->state->env->state->exconenv_pack->bool).
eval_exbind_pred eval_exbind = 

(* Rule 138a *)
   (!excon s E s' en.
    ((en = new_exname (STATE_arg2 s)) /\ (s' = add_exname en s)) ==>
    (eval_exbind (EXBIND1 excon NONE) s E s'
     (EXCONENVeep (insert_into_exconenv empty_exconenv excon en)))) /\

(* Rule 138b1 *)
   (!excon eb s E s'' en EE.
    (?s'. (en = new_exname (STATE_arg2 s)) /\ (s' = add_exname en s) /\
          (eval_exbind eb s' E s'' (EXCONENVeep EE))) ==>
    (eval_exbind (EXBIND1 excon (SOME eb)) s E s'' 
     (EXCONENVeep
      (add_exconenv (insert_into_exconenv empty_exconenv excon en) EE)))) /\

(* Rule 138b2 *)
   (!excon eb s E s'' p.
    (?en s'. (en = new_exname (STATE_arg2 s)) /\ (s' = add_exname en s) /\
             (eval_exbind eb s' E s'' (PACKeep p))) ==>
    (eval_exbind (EXBIND1 excon (SOME eb)) s E s'' (PACKeep p))) /\

(* Rule 139a *)
   (!excon longexcon s E en.
    (lookuplongexcon_env E longexcon = lift en) ==>
    (eval_exbind (EXBIND2 excon longexcon NONE) s E s 
     (EXCONENVeep (insert_into_exconenv empty_exconenv excon en)))) /\

(* Rule 139b1 *)
   (!excon longexcon eb s E s' en EE.
    ((lookuplongexcon_env E longexcon = lift en) /\
     (eval_exbind eb s E s' (EXCONENVeep EE))) ==>
    (eval_exbind (EXBIND2 excon longexcon (SOME eb)) s E s'
     (EXCONENVeep 
      (add_exconenv (insert_into_exconenv empty_exconenv excon en) EE)))) /\

(* Rule 139b2 *)
   (!excon longexcon eb s E s' p.
    (?en. (lookuplongexcon_env E longexcon = lift en) /\
          (eval_exbind eb s E s' (PACKeep p))) ==>
    (eval_exbind (EXBIND2 excon longexcon (SOME eb)) s E s' (PACKeep p)))`--

val eval_exbind_pred_DEF =
         new_definition ("eval_exbind_pred_DEF", eval_exbind_pred_def);

val eval_exbind_DEF = new_definition
    ("eval_exbind_DEF",
     --`eval_exbind eb s E s' eep =
        ! poss_eval_exbind. eval_exbind_pred poss_eval_exbind ==>
               poss_eval_exbind eb s E s' eep`--);

local
   val eb_DEF =
        CONV_RULE (REDEPTH_CONV LEFT_IMP_EXISTS_CONV) eval_exbind_pred_DEF
   val eval_defs = [eval_exbind_DEF]
in
val EVAL_EXBIND_RULES_SATISFIED = store_thm
("EVAL_EXBIND_RULES_SATISFIED",
 --`eval_exbind_pred eval_exbind`--,
 EVAL_RULE_TAC (eb_DEF :: eval_defs))

val eval_exbind_induction = save_thm 
("eval_exbind_induction",
 PURE_ONCE_REWRITE_RULE[eb_DEF]
 (prove
  (--`!P_exbind. eval_exbind_pred P_exbind ==>
      (!eb s E s' eep. eval_exbind eb s E s' eep ==>
	  P_exbind eb s E s' eep)`--,
   PURE_REWRITE_TAC eval_defs THEN
   REPEAT STRIP_TAC THEN RES_TAC)))

end;
