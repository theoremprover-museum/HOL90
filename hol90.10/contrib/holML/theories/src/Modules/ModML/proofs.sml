(* file: ModML/proofs.sml *)

(* Description: Proofs that the evaluation rules satisfy the evaluation
   predicates.  *)

(* This file has been inlined into eval.sml *)

val EVAL_SIG_RULES_SATISFIED = store_thm("EVAL_SIG_RULES_SATISFIED",
(--`ModML_eval_signatures_pred eval_sigexp eval_spec eval_strdesc`--),
EVAL_RULE_TAC [ModML_eval_signatures_pred_DEF,eval_sigexp_DEF, eval_spec_DEF,
          eval_strdesc_DEF]);


(* Hand worked proof of above theorem:

set_goal ([],
 (--`ModML_eval_signatures_pred eval_sigexp eval_spec eval_strdesc`--));
e (PURE_REWRITE_TAC [ModML_eval_signatures_pred_DEF]);
e (REPEAT CONJ_TAC);

e (PURE_REWRITE_TAC [eval_spec_DEF, eval_sigexp_DEF]);  (* SIGsigexp *)
e (REPEAT GEN_TAC);
e (PURE_REWRITE_TAC [ModML_eval_signatures_pred_DEF]);
e (REPEAT STRIP_TAC);
e (FIRST_ASSUM (fn th => MP_IMP_TAC (SPEC_ALL th)));
e (FIRST_ASSUM (fn th => MP_IMP_TAC (SPEC_ALL th)));
e ((REPEAT CONJ_TAC) THEN (FIRST_ASSUM ACCEPT_TAC));
 Lib.say "\nFinished case SIGsigexp.\n";

e (PURE_REWRITE_TAC [eval_sigexp_DEF]);                 (* SIGIDsigexp *)
e (REPEAT GEN_TAC);
e (PURE_REWRITE_TAC [ModML_eval_signatures_pred_DEF]);
e (REPEAT STRIP_TAC);
e (FIRST_ASSUM (fn th => MP_IMP_TAC (SPEC_ALL th)));
e (FIRST_ASSUM ACCEPT_TAC);
 Lib.say "\nFinished case SIGIDsigexp.\n";

e (PURE_REWRITE_TAC [eval_spec_DEF]);                   (* VALspec *)
e (REPEAT GEN_TAC);
e (PURE_REWRITE_TAC [ModML_eval_signatures_pred_DEF]);
e (REPEAT STRIP_TAC);
e (FIRST_ASSUM (fn th => MP_IMP_TAC (SPEC_ALL th)));
e (FIRST_ASSUM ACCEPT_TAC);
 Lib.say "\nFinished case VALspec.\n";

e (PURE_REWRITE_TAC [eval_spec_DEF]);                   (* EXCEPTIONspec *)
e (REPEAT GEN_TAC);
e (PURE_REWRITE_TAC [ModML_eval_signatures_pred_DEF]);
e (REPEAT STRIP_TAC);
e (FIRST_ASSUM (fn th => MP_IMP_TAC (SPEC_ALL th)));
e (FIRST_ASSUM ACCEPT_TAC);
 Lib.say "\nFinished case EXCEPTIONspec.\n";

e (PURE_REWRITE_TAC [eval_spec_DEF, eval_strdesc_DEF]); (* STRUCTUREspec *)
e (REPEAT GEN_TAC);
e (PURE_REWRITE_TAC [ModML_eval_signatures_pred_DEF]);
e (REPEAT STRIP_TAC);
e (FIRST_ASSUM (fn th => MP_IMP_TAC (SPEC_ALL th)));
e (FIRST_ASSUM (fn th => MP_IMP_TAC (SPEC_ALL th)));
e ((REPEAT CONJ_TAC) THEN (FIRST_ASSUM ACCEPT_TAC));
 Lib.say "\nFinished case STRUCTUREspec.\n";

e (PURE_REWRITE_TAC [eval_spec_DEF]);                   (* LOCALspec *)
e (REPEAT GEN_TAC);
e (PURE_REWRITE_TAC [ModML_eval_signatures_pred_DEF]);
e (REPEAT STRIP_TAC);
e (FIRST_ASSUM (fn th => MP_IMP_TAC (SPEC_ALL th)));
e CONJ_TAC;
e (FIRST_ASSUM (fn th => MP_IMP_TAC (SPEC_ALL th)));
e ((REPEAT CONJ_TAC) THEN (FIRST_ASSUM ACCEPT_TAC));
e (FIRST_ASSUM (fn th => MP_IMP_TAC (SPEC_ALL th)));
e ((REPEAT CONJ_TAC) THEN (FIRST_ASSUM ACCEPT_TAC));
 Lib.say "\nFinished case LOCALspec\n";

e (PURE_REWRITE_TAC [eval_spec_DEF]);                   (* OPENspec *)
e (REPEAT GEN_TAC);
e (PURE_REWRITE_TAC [ModML_eval_signatures_pred_DEF]);
e (REPEAT STRIP_TAC);
e (FIRST_ASSUM (fn th => MP_IMP_TAC (SPEC_ALL th)));
e CONJ_TAC;
e (FIRST_ASSUM ACCEPT_TAC);
e (FIRST_ASSUM ACCEPT_TAC);
 Lib.say "\nFinished case OPENspec.\n";

e (PURE_REWRITE_TAC [eval_spec_DEF]);                   (* INCLUDEspec *)
e (REPEAT GEN_TAC);
e (PURE_REWRITE_TAC [ModML_eval_signatures_pred_DEF]);
e (REPEAT STRIP_TAC);
e (FIRST_ASSUM (fn th => MP_IMP_TAC (SPEC_ALL th)));
e CONJ_TAC;
e (FIRST_ASSUM ACCEPT_TAC);
e (FIRST_ASSUM ACCEPT_TAC);
 Lib.say "\nFinished case INCLUDEspec.\n";

e (PURE_REWRITE_TAC [eval_spec_DEF]);                   (* EMPTYspec *)
e (REPEAT GEN_TAC);
e (PURE_REWRITE_TAC [ModML_eval_signatures_pred_DEF]);
e (REPEAT STRIP_TAC);
e (FIRST_ASSUM (fn th => ACCEPT_TAC (SPEC_ALL th)));
 Lib.say "\nFinished case EMPTYspec.\n";

e (PURE_REWRITE_TAC [eval_spec_DEF]);                   (* SEQspec *)
e (REPEAT GEN_TAC);
e (PURE_REWRITE_TAC [ModML_eval_signatures_pred_DEF]);
e (REPEAT STRIP_TAC);
e (FIRST_ASSUM (fn th => MP_IMP_TAC (SPEC_ALL th)));
e CONJ_TAC;
e (FIRST_ASSUM (fn th => MP_IMP_TAC (SPEC_ALL th)));
e ((REPEAT CONJ_TAC) THEN (FIRST_ASSUM ACCEPT_TAC));
e (FIRST_ASSUM (fn th => MP_IMP_TAC (SPEC_ALL th)));
e ((REPEAT CONJ_TAC) THEN (FIRST_ASSUM ACCEPT_TAC));
 Lib.say "\nFinished case SEQspec.\n";

e (PURE_REWRITE_TAC [eval_sigexp_DEF, eval_strdesc_DEF]); (* STRIDstrdesc *)
e (REPEAT GEN_TAC);
e (PURE_REWRITE_TAC [ModML_eval_signatures_pred_DEF]);
e (REPEAT STRIP_TAC);
e (FIRST_ASSUM (fn th => MP_IMP_TAC (SPEC_ALL th)));
e (FIRST_ASSUM (fn th => MP_IMP_TAC (SPEC_ALL th)));
e ((REPEAT CONJ_TAC) THEN (FIRST_ASSUM ACCEPT_TAC));
 Lib.say "\nFinished case STRIDstrdesc.\n";

e (PURE_REWRITE_TAC [eval_sigexp_DEF, eval_strdesc_DEF]); (* ANDstrdesc *)
e (REPEAT GEN_TAC);
e (PURE_REWRITE_TAC [ModML_eval_signatures_pred_DEF]);
e (REPEAT STRIP_TAC);
e (FIRST_ASSUM (fn th => MP_IMP_TAC (SPEC_ALL th)));
e CONJ_TAC;
e (FIRST_ASSUM (fn th => MP_IMP_TAC (SPEC_ALL th)));
e ((REPEAT CONJ_TAC) THEN (FIRST_ASSUM ACCEPT_TAC));
e (FIRST_ASSUM (fn th => MP_IMP_TAC (SPEC_ALL th)));
e ((REPEAT CONJ_TAC) THEN (FIRST_ASSUM ACCEPT_TAC));
 Lib.say "\nFinished case ANDstrdesc.\n";
*)


val EVAL_STRUCT_RULES_SATISFIED = store_thm("EVAL_STRUCT_RULES_SATISFIED",
(--`ModML_eval_structures_pred eval_strexp eval_strdec eval_strbind`--),
EVAL_RULE_TAC [ModML_eval_structures_pred_DEF,eval_strexp_DEF, eval_strdec_DEF,
          eval_strbind_DEF]);

(* Hand worked proof of above: 

set_goal ([],
 (--`ModML_eval_structures_pred eval_strexp eval_strdec eval_strbind`--));

e (PURE_REWRITE_TAC [ModML_eval_structures_pred_DEF]);
e (REPEAT CONJ_TAC);

e (PURE_REWRITE_TAC [eval_strdec_DEF, eval_strexp_DEF]);  (* STRUCTstrexp *)
e (REPEAT GEN_TAC);
e (PURE_REWRITE_TAC [ModML_eval_structures_pred_DEF]);
e (REPEAT STRIP_TAC);
e (FIRST_ASSUM (fn th => MP_IMP_TAC (SPEC_ALL th)));
e (FIRST_ASSUM (fn th => MP_IMP_TAC (SPEC_ALL th)));
e ((REPEAT CONJ_TAC) THEN (FIRST_ASSUM ACCEPT_TAC));
 Lib.say "\nFinished case STRUCTstrexp - value.\n";

e (PURE_REWRITE_TAC [eval_strdec_DEF, eval_strexp_DEF]);
e (REPEAT GEN_TAC);
e (PURE_REWRITE_TAC [ModML_eval_structures_pred_DEF]);
e (REPEAT STRIP_TAC);
e (FIRST_ASSUM (fn th => MP_IMP_TAC (SPEC_ALL th)));
e (FIRST_ASSUM (fn th => MP_IMP_TAC (SPEC_ALL th)));
e ((REPEAT CONJ_TAC) THEN (FIRST_ASSUM ACCEPT_TAC));
 Lib.say "\nFinished case STRUCTstrexp - exception.\n";

e (PURE_REWRITE_TAC [eval_strexp_DEF]);                  (* LONGSTRIDstrexp *)
e (REPEAT GEN_TAC);
e (PURE_REWRITE_TAC [ModML_eval_structures_pred_DEF]);
e (REPEAT STRIP_TAC);
e (FIRST_ASSUM (fn th => MP_IMP_TAC (SPEC_ALL th)));
e (FIRST_ASSUM ACCEPT_TAC);
 Lib.say "\nFinished case LONGSTRIDstrexp.\n";

e (PURE_REWRITE_TAC [eval_strexp_DEF]);                  (* APPstrexp *)
e (REPEAT GEN_TAC);
e (PURE_REWRITE_TAC [ModML_eval_structures_pred_DEF]);
e (REPEAT STRIP_TAC);
e (FIRST_ASSUM (fn th => MP_IMP_TAC (SPEC_ALL th)));
e (REPEAT CONJ_TAC);
e (FIRST_ASSUM ACCEPT_TAC);
e (FIRST_ASSUM (fn th => MP_IMP_TAC (SPEC_ALL th)));
e ((REPEAT CONJ_TAC) THEN (FIRST_ASSUM ACCEPT_TAC));
e (FIRST_ASSUM (fn th => MP_IMP_TAC (SPEC_ALL th)));
e ((REPEAT CONJ_TAC) THEN (FIRST_ASSUM ACCEPT_TAC));
 Lib.say "\nFinished case APPstrexp - value.\n";

e (PURE_REWRITE_TAC [eval_strexp_DEF]); 
e (REPEAT GEN_TAC);
e (PURE_REWRITE_TAC [ModML_eval_structures_pred_DEF]);
e (REPEAT STRIP_TAC);
e (MP_IMP_TAC (SPEC_ALL (ASSUME
(--`!(B:basis) (B':basis) (i:int) (funid:funid) (p:pack)
     (strexp:strexp) (strexp':strexp) (strid:strid) (s1:state) (s2:state).
      (lift (BASICfunclos strid i strexp' B') = lookup_funid_basis B funid) /\
      poss_eval_strexp strexp s1 B s2 (PACKep p) ==>
      poss_eval_strexp (APPstrexp funid strexp) s1 B s2 (PACKep p)`--))));
e (REPEAT CONJ_TAC);
e (FIRST_ASSUM ACCEPT_TAC);
e (FIRST_ASSUM (fn th => MP_IMP_TAC (SPEC_ALL th)));
e ((REPEAT CONJ_TAC) THEN (FIRST_ASSUM ACCEPT_TAC));
 Lib.say "\nFinished case APPstrexp - exception1.\n";

e (PURE_REWRITE_TAC [eval_strexp_DEF]); 
e (REPEAT GEN_TAC);
e (PURE_REWRITE_TAC [ModML_eval_structures_pred_DEF]);
e (REPEAT STRIP_TAC);
e (MP_IMP_TAC (SPEC_ALL (ASSUME
(--`!(B:basis) (B':basis) (E:env) (i:int) (funid:funid) (p:pack)(strexp:strexp)
     (strexp':strexp) (strid:strid) (s1:state) (s2:state) (s3:state).
      (lift (BASICfunclos strid i strexp' B') = lookup_funid_basis B funid) /\
      poss_eval_strexp strexp s1 B s2 (ENVep E) /\
      poss_eval_strexp strexp' s2
        (add_basis B' (strenv_in_basis (strenv_map strid (cut_env E i))))
        s3
        (PACKep p) ==>
      poss_eval_strexp (APPstrexp funid strexp) s1 B s3 (PACKep p)`--))));
e (REPEAT CONJ_TAC);
e (FIRST_ASSUM ACCEPT_TAC);
e (FIRST_ASSUM (fn th => MP_IMP_TAC (SPEC_ALL th)));
e ((REPEAT CONJ_TAC) THEN (FIRST_ASSUM ACCEPT_TAC));
e (FIRST_ASSUM (fn th => MP_IMP_TAC (SPEC_ALL th)));
e ((REPEAT CONJ_TAC) THEN (FIRST_ASSUM ACCEPT_TAC));
 Lib.say "\nFinished case APPstrexp - exception2.\n";

e (PURE_REWRITE_TAC [eval_strexp_DEF]); 
e (REPEAT GEN_TAC);
e (PURE_REWRITE_TAC [ModML_eval_structures_pred_DEF]);
e (REPEAT STRIP_TAC);
e (FIRST_ASSUM (fn th => MP_IMP_TAC (SPEC_ALL th)));
e (REPEAT CONJ_TAC);
e (FIRST_ASSUM ACCEPT_TAC);
e (FIRST_ASSUM (fn th => MP_IMP_TAC (SPEC_ALL th)));
e ((REPEAT CONJ_TAC) THEN (FIRST_ASSUM ACCEPT_TAC));
e (FIRST_ASSUM (fn th => MP_IMP_TAC (SPEC_ALL th)));
e ((REPEAT CONJ_TAC) THEN (FIRST_ASSUM ACCEPT_TAC));
 Lib.say "\nFinished case APPstrexp b - value.\n";

e (PURE_REWRITE_TAC [eval_strexp_DEF]); 
e (REPEAT GEN_TAC);
e (PURE_REWRITE_TAC [ModML_eval_structures_pred_DEF]);
e (REPEAT STRIP_TAC);
e (MP_IMP_TAC (SPEC_ALL (ASSUME
(--`!(B:basis) (B':basis) (i:int) (i':int) (funid:funid) (p:pack)
     (strexp:strexp) (strexp':strexp) (strid:strid) (s1:state) (s2:state).
      (lift (CONSTRAINfunclos strid i strexp' i' B') =
       lookup_funid_basis B funid) /\
      poss_eval_strexp strexp s1 B s2 (PACKep p) ==>
      poss_eval_strexp (APPstrexp funid strexp) s1 B s2 (PACKep p)`--))));
e (REPEAT CONJ_TAC);
e (FIRST_ASSUM ACCEPT_TAC);
e (FIRST_ASSUM (fn th => MP_IMP_TAC (SPEC_ALL th)));
e ((REPEAT CONJ_TAC) THEN (FIRST_ASSUM ACCEPT_TAC));
 Lib.say "\nFinished case APPstrexp b - exception1.\n";


e (PURE_REWRITE_TAC [eval_strexp_DEF]); 
e (REPEAT GEN_TAC);
e (PURE_REWRITE_TAC [ModML_eval_structures_pred_DEF]);
e (REPEAT STRIP_TAC);
e (MP_IMP_TAC (SPEC_ALL (ASSUME
(--`!(B:basis) (B':basis) (E:env) (i:int) (i':int) (funid:funid) (p:pack)
     (strexp:strexp) (strexp':strexp) (strid:strid) (s1:state) (s2:state) 
     (s3:state).
      (lift (CONSTRAINfunclos strid i strexp' i' B') =
       lookup_funid_basis B funid) /\
      poss_eval_strexp strexp s1 B s2 (ENVep E) /\
      poss_eval_strexp strexp' s2
        (add_basis B' (strenv_in_basis (strenv_map strid (cut_env E i))))
        s3
        (PACKep p) ==>
      poss_eval_strexp (APPstrexp funid strexp) s1 B s3 (PACKep p)`--))));
e (REPEAT CONJ_TAC);
e (FIRST_ASSUM ACCEPT_TAC);
e (FIRST_ASSUM (fn th => MP_IMP_TAC (SPEC_ALL th)));
e ((REPEAT CONJ_TAC) THEN (FIRST_ASSUM ACCEPT_TAC));
e (FIRST_ASSUM (fn th => MP_IMP_TAC (SPEC_ALL th)));
e ((REPEAT CONJ_TAC) THEN (FIRST_ASSUM ACCEPT_TAC));
 Lib.say "\nFinished case APPstrexp b - exception2.\n";


e (PURE_REWRITE_TAC [eval_strexp_DEF,eval_strdec_DEF]);  (* LETstrexp *)
e (REPEAT GEN_TAC);
e (PURE_REWRITE_TAC [ModML_eval_structures_pred_DEF]);
e (REPEAT STRIP_TAC);
e (FIRST_ASSUM (fn th => MP_IMP_TAC (SPEC_ALL th)));
e (REPEAT CONJ_TAC);
e (FIRST_ASSUM (fn th => MP_IMP_TAC (SPEC_ALL th)));
e ((REPEAT CONJ_TAC) THEN (FIRST_ASSUM ACCEPT_TAC));
e (FIRST_ASSUM (fn th => MP_IMP_TAC (SPEC_ALL th)));
e ((REPEAT CONJ_TAC) THEN (FIRST_ASSUM ACCEPT_TAC));
 Lib.say "\nFinished case LETstrexp - value.\n";


e (PURE_REWRITE_TAC [eval_strexp_DEF,eval_strdec_DEF]); 
e (REPEAT GEN_TAC);
e (PURE_REWRITE_TAC [ModML_eval_structures_pred_DEF]);
e (REPEAT STRIP_TAC);
e (FIRST_ASSUM (fn th => MP_IMP_TAC (SPEC_ALL th)));
e (FIRST_ASSUM (fn th => MP_IMP_TAC (SPEC_ALL th)));
e ((REPEAT CONJ_TAC) THEN (FIRST_ASSUM ACCEPT_TAC));
 Lib.say "\nFinished case LETstrexp - exception1.\n";


e (PURE_REWRITE_TAC [eval_strexp_DEF,eval_strdec_DEF]); 
e (REPEAT GEN_TAC);
e (PURE_REWRITE_TAC [ModML_eval_structures_pred_DEF]);
e (REPEAT STRIP_TAC);
e (FIRST_ASSUM (fn th => MP_IMP_TAC (SPEC_ALL th)));
e CONJ_TAC;
e (FIRST_ASSUM (fn th => MP_IMP_TAC (SPEC_ALL th)));
e ((REPEAT CONJ_TAC) THEN (FIRST_ASSUM ACCEPT_TAC));
e (FIRST_ASSUM (fn th => MP_IMP_TAC (SPEC_ALL th)));
e ((REPEAT CONJ_TAC) THEN (FIRST_ASSUM ACCEPT_TAC));
 Lib.say "\nFinished case LETstrexp - exception2.\n";


e (PURE_REWRITE_TAC [eval_strdec_DEF]);                 (* DECstrdec *)
e (REPEAT GEN_TAC);
e (PURE_REWRITE_TAC [ModML_eval_structures_pred_DEF]);
e (REPEAT STRIP_TAC);
e (FIRST_ASSUM (fn th => MP_IMP_TAC (SPEC_ALL th)));
e (FIRST_ASSUM ACCEPT_TAC);
 Lib.say "\nFinished case DECstrdec - value.\n";

e (PURE_REWRITE_TAC [eval_strdec_DEF]); 
e (REPEAT GEN_TAC);
e (PURE_REWRITE_TAC [ModML_eval_structures_pred_DEF]);
e (REPEAT STRIP_TAC);
e (FIRST_ASSUM (fn th => MP_IMP_TAC (SPEC_ALL th)));
e (FIRST_ASSUM ACCEPT_TAC);
 Lib.say "\nFinished case DECstrdec - exception.\n";


e (PURE_REWRITE_TAC [eval_strdec_DEF,eval_strbind_DEF]);  (* STRUCTUREstrdec *)
e (REPEAT GEN_TAC);
e (PURE_REWRITE_TAC [ModML_eval_structures_pred_DEF]);
e (REPEAT STRIP_TAC);
e (FIRST_ASSUM (fn th => MP_IMP_TAC (SPEC_ALL th)));
e (FIRST_ASSUM (fn th => MP_IMP_TAC (SPEC_ALL th)));
e ((REPEAT CONJ_TAC) THEN (FIRST_ASSUM ACCEPT_TAC));
 Lib.say "\nFinished case STRUCTUREstrdec - value.\n";

e (PURE_REWRITE_TAC [eval_strdec_DEF,eval_strbind_DEF]); 
e (REPEAT GEN_TAC);
e (PURE_REWRITE_TAC [ModML_eval_structures_pred_DEF]);
e (REPEAT STRIP_TAC);
e (FIRST_ASSUM (fn th => MP_IMP_TAC (SPEC_ALL th)));
e (FIRST_ASSUM (fn th => MP_IMP_TAC (SPEC_ALL th)));
e ((REPEAT CONJ_TAC) THEN (FIRST_ASSUM ACCEPT_TAC));
 Lib.say "\nFinished case STRUCTUREstrdec - exception.\n";


e (PURE_REWRITE_TAC [eval_strdec_DEF]);                   (* LOCALstrdec *)
e (REPEAT GEN_TAC);
e (PURE_REWRITE_TAC [ModML_eval_structures_pred_DEF]);
e (REPEAT STRIP_TAC);
e (FIRST_ASSUM (fn th => MP_IMP_TAC (SPEC_ALL th)));
e CONJ_TAC;
e (FIRST_ASSUM (fn th => MP_IMP_TAC (SPEC_ALL th)));
e ((REPEAT CONJ_TAC) THEN (FIRST_ASSUM ACCEPT_TAC));
e (FIRST_ASSUM (fn th => MP_IMP_TAC (SPEC_ALL th)));
e ((REPEAT CONJ_TAC) THEN (FIRST_ASSUM ACCEPT_TAC));
 Lib.say "\nFinished case LOCALstrdec - value.\n";

e (PURE_REWRITE_TAC [eval_strdec_DEF]);    
e (REPEAT GEN_TAC);
e (PURE_REWRITE_TAC [ModML_eval_structures_pred_DEF]);
e (REPEAT STRIP_TAC);
e (FIRST_ASSUM (fn th => MP_IMP_TAC (SPEC_ALL th)));
e (FIRST_ASSUM (fn th => MP_IMP_TAC (SPEC_ALL th)));
e ((REPEAT CONJ_TAC) THEN (FIRST_ASSUM ACCEPT_TAC));
 Lib.say "\nFinished case LOCALstrdec - exception1.\n";


e (PURE_REWRITE_TAC [eval_strdec_DEF]);    
e (REPEAT GEN_TAC);
e (PURE_REWRITE_TAC [ModML_eval_structures_pred_DEF]);
e (REPEAT STRIP_TAC);
e (FIRST_ASSUM (fn th => MP_IMP_TAC (SPEC_ALL th)));
e CONJ_TAC;
e (FIRST_ASSUM (fn th => MP_IMP_TAC (SPEC_ALL th)));
e ((REPEAT CONJ_TAC) THEN (FIRST_ASSUM ACCEPT_TAC));
e (FIRST_ASSUM (fn th => MP_IMP_TAC (SPEC_ALL th)));
e ((REPEAT CONJ_TAC) THEN (FIRST_ASSUM ACCEPT_TAC));
 Lib.say "\nFinished case LOCALstrdec - exception2.\n";


e (PURE_REWRITE_TAC [eval_strdec_DEF]);                  (* EMPTYstrdec *)
e (REPEAT GEN_TAC);
e (PURE_REWRITE_TAC [ModML_eval_structures_pred_DEF]);
e (REPEAT STRIP_TAC);
e (FIRST_ASSUM (fn th => ACCEPT_TAC (SPEC_ALL th)));
 Lib.say "\nFinished case EMPTYstrdec - value.\n";


e (PURE_REWRITE_TAC [eval_strdec_DEF]);                   (* SEQstrdec *)
e (REPEAT GEN_TAC);
e (PURE_REWRITE_TAC [ModML_eval_structures_pred_DEF]);
e (REPEAT STRIP_TAC);
e (FIRST_ASSUM (fn th => MP_IMP_TAC (SPEC_ALL th)));
e CONJ_TAC;
e (FIRST_ASSUM (fn th => MP_IMP_TAC (SPEC_ALL th)));
e ((REPEAT CONJ_TAC) THEN (FIRST_ASSUM ACCEPT_TAC));
e (FIRST_ASSUM (fn th => MP_IMP_TAC (SPEC_ALL th)));
e ((REPEAT CONJ_TAC) THEN (FIRST_ASSUM ACCEPT_TAC));
 Lib.say "\nFinished case SEQstrdec - value.\n";


e (PURE_REWRITE_TAC [eval_strdec_DEF]);    
e (REPEAT GEN_TAC);
e (PURE_REWRITE_TAC [ModML_eval_structures_pred_DEF]);
e (REPEAT STRIP_TAC);
e (FIRST_ASSUM (fn th => MP_IMP_TAC (SPEC_ALL th)));
e (FIRST_ASSUM (fn th => MP_IMP_TAC (SPEC_ALL th)));
e ((REPEAT CONJ_TAC) THEN (FIRST_ASSUM ACCEPT_TAC));
 Lib.say "\nFinished case SEQstrdec - exception 1.\n";


e (PURE_REWRITE_TAC [eval_strdec_DEF]);    
e (REPEAT GEN_TAC);
e (PURE_REWRITE_TAC [ModML_eval_structures_pred_DEF]);
e (REPEAT STRIP_TAC);
e (FIRST_ASSUM (fn th => MP_IMP_TAC (SPEC_ALL th)));
e CONJ_TAC;
e (FIRST_ASSUM (fn th => MP_IMP_TAC (SPEC_ALL th)));
e ((REPEAT CONJ_TAC) THEN (FIRST_ASSUM ACCEPT_TAC));
e (FIRST_ASSUM (fn th => MP_IMP_TAC (SPEC_ALL th)));
e ((REPEAT CONJ_TAC) THEN (FIRST_ASSUM ACCEPT_TAC));
 Lib.say "\nFinished case SEQstrdec - exception 2.\n";


e (PURE_REWRITE_TAC [eval_strexp_DEF, eval_strbind_DEF]);   (* BINDstrbind *)  
e (REPEAT GEN_TAC);
e (PURE_REWRITE_TAC [ModML_eval_structures_pred_DEF]);
e (REPEAT STRIP_TAC);
e (FIRST_ASSUM (fn th => MP_IMP_TAC (SPEC_ALL th)));
e (FIRST_ASSUM (fn th => MP_IMP_TAC (SPEC_ALL th)));
e ((REPEAT CONJ_TAC) THEN (FIRST_ASSUM ACCEPT_TAC));
 Lib.say "\nFinished case BINDstrbind - value.\n";


e (PURE_REWRITE_TAC [eval_strexp_DEF, eval_strbind_DEF]);    
e (REPEAT GEN_TAC);
e (PURE_REWRITE_TAC [ModML_eval_structures_pred_DEF]);
e (REPEAT STRIP_TAC);
e (FIRST_ASSUM (fn th => MP_IMP_TAC (SPEC_ALL th)));
e (FIRST_ASSUM (fn th => MP_IMP_TAC (SPEC_ALL th)));
e ((REPEAT CONJ_TAC) THEN (FIRST_ASSUM ACCEPT_TAC));
 Lib.say "\nFinished case BINDstrbind - exception.\n";


e (PURE_REWRITE_TAC [eval_strexp_DEF, eval_strbind_DEF]);(* CONSTRAINstrbind *)
e (REPEAT GEN_TAC);
e (PURE_REWRITE_TAC [ModML_eval_structures_pred_DEF]);
e (REPEAT STRIP_TAC);
e (FIRST_ASSUM (fn th => MP_IMP_TAC (SPEC_ALL th)));
e CONJ_TAC;
e (FIRST_ASSUM (fn th => MP_IMP_TAC (SPEC_ALL th)));
e ((REPEAT CONJ_TAC) THEN (FIRST_ASSUM ACCEPT_TAC));
e (FIRST_ASSUM ACCEPT_TAC);
 Lib.say "\nFinished case CONSTRAINstrbind - value.\n";


e (PURE_REWRITE_TAC [eval_strexp_DEF, eval_strbind_DEF]);(* CONSTRAINstrbind *)
e (REPEAT GEN_TAC);
e (PURE_REWRITE_TAC [ModML_eval_structures_pred_DEF]);
e (REPEAT STRIP_TAC);
e (FIRST_ASSUM (fn th => MP_IMP_TAC (SPEC_ALL th)));
e (FIRST_ASSUM (fn th => MP_IMP_TAC (SPEC_ALL th)));
e ((REPEAT CONJ_TAC) THEN (FIRST_ASSUM ACCEPT_TAC));
 Lib.say "\nFinished case CONSTRAINstrbind - exception.\n";


e (PURE_REWRITE_TAC [eval_strexp_DEF, eval_strbind_DEF]);(* ANDstrbind *)
e (REPEAT GEN_TAC);
e (PURE_REWRITE_TAC [ModML_eval_structures_pred_DEF]);
e (REPEAT STRIP_TAC);
e (FIRST_ASSUM (fn th => MP_IMP_TAC (SPEC_ALL th)));
e CONJ_TAC;
e (FIRST_ASSUM (fn th => MP_IMP_TAC (SPEC_ALL th)));
e ((REPEAT CONJ_TAC) THEN (FIRST_ASSUM ACCEPT_TAC));
e (FIRST_ASSUM (fn th => MP_IMP_TAC (SPEC_ALL th)));
e ((REPEAT CONJ_TAC) THEN (FIRST_ASSUM ACCEPT_TAC));
 Lib.say "\nFinished case ANDstrbind - value.\n";


e (PURE_REWRITE_TAC [eval_strexp_DEF, eval_strbind_DEF]);
e (REPEAT GEN_TAC);
e (PURE_REWRITE_TAC [ModML_eval_structures_pred_DEF]);
e (REPEAT STRIP_TAC);
e (FIRST_ASSUM (fn th => MP_IMP_TAC (SPEC_ALL th)));
e (FIRST_ASSUM (fn th => MP_IMP_TAC (SPEC_ALL th)));
e ((REPEAT CONJ_TAC) THEN (FIRST_ASSUM ACCEPT_TAC));
 Lib.say "\nFinished case ANDstrbind - exception 1.\n";


e (PURE_REWRITE_TAC [eval_strexp_DEF, eval_strbind_DEF]);
e (REPEAT GEN_TAC);
e (PURE_REWRITE_TAC [ModML_eval_structures_pred_DEF]);
e (REPEAT STRIP_TAC);
e (FIRST_ASSUM (fn th => MP_IMP_TAC (SPEC_ALL th)));
e CONJ_TAC;
e (FIRST_ASSUM (fn th => MP_IMP_TAC (SPEC_ALL th)));
e ((REPEAT CONJ_TAC) THEN (FIRST_ASSUM ACCEPT_TAC));
e (FIRST_ASSUM (fn th => MP_IMP_TAC (SPEC_ALL th)));
e ((REPEAT CONJ_TAC) THEN (FIRST_ASSUM ACCEPT_TAC));
 Lib.say "\nFinished case ANDstrbind - exception 2.\n";


e (PURE_REWRITE_TAC [eval_strexp_DEF,eval_strbind_DEF]);(*CONSTRAINANDstrbind*)
e (REPEAT GEN_TAC);
e (PURE_REWRITE_TAC [ModML_eval_structures_pred_DEF]);
e (REPEAT STRIP_TAC);
e (FIRST_ASSUM (fn th => MP_IMP_TAC (SPEC_ALL th)));
e (REPEAT CONJ_TAC);
e (FIRST_ASSUM (fn th => MP_IMP_TAC (SPEC_ALL th)));
e ((REPEAT CONJ_TAC) THEN (FIRST_ASSUM ACCEPT_TAC));
e (FIRST_ASSUM ACCEPT_TAC);
e (FIRST_ASSUM (fn th => MP_IMP_TAC (SPEC_ALL th)));
e ((REPEAT CONJ_TAC) THEN (FIRST_ASSUM ACCEPT_TAC));
 Lib.say "\nFinished case CONSTRAINANDstrbind - value.\n";

e (PURE_REWRITE_TAC [eval_strexp_DEF,eval_strbind_DEF]);
e (REPEAT GEN_TAC);
e (PURE_REWRITE_TAC [ModML_eval_structures_pred_DEF]);
e (REPEAT STRIP_TAC);
e (FIRST_ASSUM (fn th => MP_IMP_TAC (SPEC_ALL th)));
e (FIRST_ASSUM (fn th => MP_IMP_TAC (SPEC_ALL th)));
e ((REPEAT CONJ_TAC) THEN (FIRST_ASSUM ACCEPT_TAC));
 Lib.say "\nFinished case CONSTRAINANDstrbind - exception 1.\n";

e (PURE_REWRITE_TAC [eval_strexp_DEF,eval_strbind_DEF]);
e (REPEAT GEN_TAC);
e (PURE_REWRITE_TAC [ModML_eval_structures_pred_DEF]);
e (REPEAT STRIP_TAC);
e (FIRST_ASSUM (fn th => MP_IMP_TAC (SPEC_ALL th)));
e (REPEAT CONJ_TAC);
e (FIRST_ASSUM (fn th => MP_IMP_TAC (SPEC_ALL th)));
e ((REPEAT CONJ_TAC) THEN (FIRST_ASSUM ACCEPT_TAC));
e (FIRST_ASSUM ACCEPT_TAC);
e (FIRST_ASSUM (fn th => MP_IMP_TAC (SPEC_ALL th)));
e ((REPEAT CONJ_TAC) THEN (FIRST_ASSUM ACCEPT_TAC));
 Lib.say "\nFinished case CONSTRAINANDstrbind - exception 2.\n";
*)