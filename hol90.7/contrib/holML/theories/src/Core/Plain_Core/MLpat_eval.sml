(* MLpat_eval.sml *)

(* Note: the mark *** next to a rule number means that I think that the *)
(* encoding of the marked rule is not completely straightforward.       *)

val eval_pat_pred_def = 
--`!(eval_atpat:atpat->state->env->val->state->varenv_fail->bool)
    (eval_patrow:patrow->state->env->record->state->varenv_fail->bool)
    (eval_pat:pat->state->env->val->state->varenv_fail->bool).

eval_pat_pred eval_atpat eval_patrow eval_pat =

(* Atomic Patterns *)
(* Rule 140 *)
   (!s E v. eval_atpat WILDCARDatpat s E v s (VARENVvef empty_varenv)) /\

(* Rule 141 *)
   (!s E scon v. (v =  SVALval (value_of scon)) ==>
        eval_atpat (SCONatpat scon) s E v s (VARENVvef empty_varenv)) /\

(* Rule 142 *)
   (!s E scon v. ~(v =  SVALval (value_of scon)) ==>
        eval_atpat (SCONatpat scon) s E v s FAILvef) /\

(* Rule 143 *)
   (!s E var v. eval_atpat (VARatpat var) s E v s 
    (VARENVvef (insert_into_varenv empty_varenv var v))) /\

(* Rule 144 *)
   (!s E longcon v. (v = CONval (long_base longcon)) ==>
        eval_atpat (CONatpat longcon) s E v s (VARENVvef empty_varenv)) /\

(* Rule 145 *) 
   (!s E longcon v. ~(v = CONval (long_base longcon)) ==>
       eval_atpat (CONatpat longcon) s E v s FAILvef) /\

(* Rule 146 *** *)
   (!s E longexcon en. (lookuplongexcon_env E longexcon = lift en) ==>
       eval_atpat (EXCONatpat longexcon) s E (EXVALval (NAMEexval en)) s
          (VARENVvef empty_varenv)) /\

(* Rule 147 *** *)
   (!s E longexcon en.
    (? en'. (lookuplongexcon_env E longexcon = lift en') /\ (~(en = en'))) ==>
        eval_atpat (EXCONatpat longexcon) s E (EXVALval (NAMEexval en))
	           s FAILvef) /\

(* Rule 148a *)
   (!s E v. (v = RECORDval (empty_record)) ==>
       eval_atpat (RECORDatpat NONE) s E v s (VARENVvef empty_varenv)) /\

(* Rule 148b *)
   (!s1 s2 E v VE patrow. 
    (?r. (v = RECORDval (add_record empty_record r)) /\
         (eval_patrow patrow s1 E r s2 (VARENVvef VE))) ==>
    (eval_atpat (RECORDatpat (SOME patrow)) s1 E v s2 
     (VARENVvef (add_varenv empty_varenv VE)))) /\

   (!s1 s2 E v patrow. 
    (?r. (v = RECORDval (add_record empty_record r)) /\
         (eval_patrow patrow s1 E r s2 FAILvef)) ==>
    (eval_atpat (RECORDatpat (SOME patrow)) s1 E v s2 FAILvef)) /\

(* Rule 149 *)
   (!s1 s2 E v vef pat. (eval_pat pat s1 E v s2 vef) ==>
       (eval_atpat (PARatpat pat) s1 E v s2 vef)) /\

(* Pattern Rows *)

(* Rule 150 *)
   (!s E r. eval_patrow DOTDOTDOT s E r s (VARENVvef empty_varenv)) /\

(* Rule 151a *)
   (!s1 s2 E r lab pat. 
    (eval_pat pat s1 E (lower (lookup_label r lab)) s2 FAILvef) ==>
    (eval_patrow (PATROW lab pat NONE) s1 E r s2 FAILvef)) /\

(* Rule 151b *)
   (!s1 s2 E r lab pat patrow.
    (eval_pat pat s1 E (lower (lookup_label r lab)) s2 FAILvef) ==>
    (eval_patrow (PATROW lab pat (SOME patrow)) s1 E r s2 FAILvef)) /\

(* Rule 152a *)
   (!s1 s2 E r lab pat VE.
    (eval_pat pat s1 E (lower (lookup_label r lab)) s2 (VARENVvef VE)) ==>
    (eval_patrow (PATROW lab pat NONE) s1 E r s2 (VARENVvef VE))) /\

(* Rule 152b *)
   (!s1 s2 E r lab pat patrow VE VE'.
    (?s'. (eval_pat pat s1 E (lower (lookup_label r lab)) s'
             (VARENVvef VE)) /\
          (eval_patrow patrow s' E r s2 (VARENVvef VE'))) ==>
    (eval_patrow (PATROW lab pat (SOME patrow)) 
             s1 E r s2 (VARENVvef (add_varenv VE VE')))) /\

   (!s1 s2 E r lab pat patrow.
    (?s' VE. (eval_pat pat s1 E (lower (lookup_label r lab)) s'
          (VARENVvef VE)) /\
     (eval_patrow patrow s' E r s2 FAILvef)) ==>
    (eval_patrow (PATROW lab pat (SOME patrow)) s1 E r s2 FAILvef)) /\

(* Patterns *)

(* Rule 153 *)
   (!s1 s2 E v atpat vef. (eval_atpat atpat s1 E v s2 vef) ==>
         (eval_pat (ATPATpat atpat) s1 E v s2 vef)) /\

(* Rule 154 *) 
   (!s1 s2 E v longcon atpat vef.
    (?con v'. (long_base longcon = con) /\ ~(con = CON "ref") /\
              (v = APPCONval con v') /\
              (eval_atpat atpat s1 E v' s2 vef)) ==>
    (eval_pat (CONpat longcon atpat) s1 E v s2 vef)) /\

(* Rule 155 *** *) 
   (!s E v longcon atpat.
    (?con. (long_base longcon = con) /\ ~(con = CON "ref") /\
           (!v'. ~(v = APPCONval con v'))) ==>
    (eval_pat (CONpat longcon atpat) s E v s FAILvef)) /\

(* Rule 156 *** *)
   (!s1 s2 E v longexcon atpat vef.
    (?v' en. (lookuplongexcon_env E longexcon = lift en) /\
             (v = EXVALval (NAMEVALexval en v')) /\
             (eval_atpat atpat s1 E v' s2 vef)) ==>
    (eval_pat (EXCONpat longexcon atpat) s1 E v s2 vef)) /\

(* Rule 157 *** *) 
   (!s E v longexcon atpat.
    (?en.(lookuplongexcon_env E longexcon = lift en) /\
         (!v'. ~(v = EXVALval (NAMEVALexval en v')))) ==>
    (eval_pat (EXCONpat longexcon atpat) s E v s FAILvef)) /\


(* Rule 158 *** *) 
   (!s E a atpat vef.
    (?v.(lookupaddr_state s a = lift v) /\
        (eval_atpat atpat s E v s vef)) ==>
    (eval_pat (CONpat (BASE (CON "ref")) atpat) s E (ADDRval a) s vef)) /\

(* Rule 159 *)
   (!s1 s2 E v var pat VE.
    (eval_pat pat s1 E v s2 (VARENVvef VE)) ==>
    (eval_pat (LAYEREDpat var pat) s1 E v s2 
          (VARENVvef (add_varenv 
		      (insert_into_varenv empty_varenv var v) VE)))) /\

   (!s1 s2 E v var pat.
    (eval_pat pat s1 E v s2 FAILvef) ==>
    (eval_pat (LAYEREDpat var pat) s1 E v s2 FAILvef))`--;


val eval_pat_pred_DEF =
	 new_definition ("eval_pat_pred_DEF", eval_pat_pred_def);

val eval_atpat_DEF = new_definition 
    ("eval_atpat_DEF",
     --`eval_atpat ap s1 v e s2 vef =
        ! poss_eval_atpat poss_eval_patrow poss_eval_pat.
        eval_pat_pred poss_eval_atpat poss_eval_patrow poss_eval_pat ==>
	  poss_eval_atpat ap s1 v e s2 vef`--);

val eval_patrow_DEF = new_definition 
    ("eval_patrow_DEF",
     --`eval_patrow pr s1 r e s2 vef =
        ! poss_eval_atpat poss_eval_patrow poss_eval_pat.
        eval_pat_pred poss_eval_atpat poss_eval_patrow poss_eval_pat ==>
	  poss_eval_patrow pr s1 r e s2 vef`--);

val eval_pat_DEF = new_definition 
    ("eval_pat_DEF",
     --`eval_pat p s1 v e s2 vef =
        ! poss_eval_atpat poss_eval_patrow poss_eval_pat.
        eval_pat_pred poss_eval_atpat poss_eval_patrow poss_eval_pat ==>
	  poss_eval_pat p s1  v e s2 vef`--);

local
   val ep_DEF =
        CONV_RULE (REDEPTH_CONV LEFT_IMP_EXISTS_CONV)eval_pat_pred_DEF
   val eval_defs = [eval_atpat_DEF, eval_patrow_DEF, eval_pat_DEF]
in
val EVAL_PAT_RULES_SATISFIED = store_thm
("EVAL_PAT_RULES_SATISFIED",
 --`eval_pat_pred eval_atpat eval_patrow eval_pat`--,
 EVAL_RULE_TAC (ep_DEF :: eval_defs))

val eval_pat_induction = save_thm ("eval_pat_induction",
PURE_ONCE_REWRITE_RULE[ep_DEF]
(prove 
((--`!P_atpat P_patrow P_pat. eval_pat_pred P_atpat P_patrow P_pat ==>
 (!ap s1 v e s2 vef. eval_atpat ap s1 v e s2 vef ==>
                     P_atpat ap s1 v e s2 vef) /\
 (!pr s1 r e s2 vef. eval_patrow pr s1 r e s2 vef ==>
                     P_patrow pr s1 r e s2 vef) /\
 (!p s1 v e s2 vef. eval_pat p s1 v e s2 vef ==> P_pat p s1 v e s2 vef)`--),
PURE_REWRITE_TAC eval_defs THEN
REPEAT STRIP_TAC THEN RES_TAC)))

end;


