(* File: ModML/eval.sml *)

(* Description: This file contains the definitions of the evaluation
   relations that give the dynamic semantics of the ML Module system. *)

(* Reference: The "Definition", Section 7.3 *)

val ModML_eval_signatures_pred_def =
--`ModML_eval_signatures_pred
   (eval_sigexp:sigexp->state->intbasis->state->int->bool)
   (eval_spec:spec->state->intbasis->state->int->bool)
   (eval_strdesc:strdesc->state->intbasis->state->intenv->bool) =

(* Signature Expressions     IB |- sigexp => I *)

(* Rule 170 *)
   (!i IB spec s1 s2. 
       (eval_spec spec s1 IB s2 i) ==> 
       (eval_sigexp (SIGsigexp spec) s1 IB s2 i)) /\

(* Rule 171 *)
   (!i IB s sigid.
       (lookup_sigid_intbasis IB sigid = lift i) ==>
       (eval_sigexp (SIGIDsigexp sigid) s IB s i)) /\

(* Specifications     IB |- spec => I *)

(* Rule 176 *)
   (!IB valdesc vars s1 s2.
       (eval_valdesc valdesc s1 s2 vars) ==>
       (eval_spec (VALspec valdesc) s1 IB s2 (vars_in_int vars))) /\

(* Rule 177 *)
   (!IB excons exdesc s1 s2.
       (eval_exdesc exdesc s1 s2 excons) ==>
       (eval_spec (EXCEPTIONspec exdesc) s1 IB s2 (excons_in_int excons))) /\

(* Rule 178 *)
   (!IB IE strdesc s1 s2.
       (eval_strdesc strdesc s1 IB s2 IE) ==>
       (eval_spec (STRUCTUREspec strdesc) s1 IB s2 (intenv_in_int IE))) /\

(* Rule 179 *)
   (!IB I1 I2 spec1 spec2 s1 s2 s3.
       (eval_spec spec1 s1 IB s2 I1) /\
       (eval_spec spec2 s2 
            (add_intenv_to_intbasis IB (intenv_of_int I1)) s3 I2) ==>
       (eval_spec (LOCALspec spec1 spec2) s1 IB s3 I2)) /\

(* Rule 180 *)
   (!IB nonempty_int_list nonempty_lift_int_list nonempty_longstrid_list s.
       ((nonempty_MAP (lookup_longstrid_intbasis IB) 
               nonempty_longstrid_list) = nonempty_lift_int_list) /\
       ((nonempty_MAP lift nonempty_int_list) = nonempty_lift_int_list) ==>
       (eval_spec (OPENspec nonempty_longstrid_list) s IB 
            s (nonempty_FOLDL_WITH_INIT add_int nonempty_int_list))) /\

(* Rule 181 *)
   (!IB nonempty_int_list nonempty_lift_int_list nonempty_sigid_list s.
       ((nonempty_MAP (lookup_sigid_intbasis IB) nonempty_sigid_list)
            = nonempty_lift_int_list) /\
       ((nonempty_MAP lift nonempty_int_list) = nonempty_lift_int_list) ==>
       (eval_spec (INCLUDEspec nonempty_sigid_list) s IB 
            s (nonempty_FOLDL_WITH_INIT add_int nonempty_int_list))) /\

(* Rule 182 *)
    (!IB s. eval_spec EMPTYspec s IB s empty_int) /\

(* Rule 183 *)
    (!IB I1 I2 spec1 spec2 s1 s2 s3.
       (eval_spec spec1 s1 IB s2 I1) /\
       (eval_spec spec2 s2 
            (add_intenv_to_intbasis IB (intenv_of_int I1)) s3 I2) ==>
       (eval_spec (SEQspec spec1 spec2) s1 IB s3 (add_int I1 I2))) /\

(* Structure Descriptions     IB |- strdesc => IE *)

(* Rule 186a *)
    (!i IB sigexp strid s1 s2.
       (eval_sigexp sigexp s1 IB s2 i) ==>
       (eval_strdesc (STRIDstrdesc strid sigexp NONE) s1 IB 
             s2 (intenv_map strid i))) /\

(* Rule 186b *)
    (!i IB IE sigexp strdesc strid s1 s2 s3.
       (eval_sigexp sigexp s1 IB s2 i) /\
       (eval_strdesc strdesc s2 IB s3 IE) ==>
       (eval_strdesc (STRIDstrdesc strid sigexp (SOME strdesc)) s1 IB
             s3 (add_intenv (intenv_map strid i) IE)))`--;

val ModML_eval_signatures_pred_DEF = 
   new_definition ("ModML_eval_signatures_pred_DEF", 
                    ModML_eval_signatures_pred_def);

val eval_sigexp_DEF = new_definition
    ("eval_sigexp_DEF",
    --`eval_sigexp sigexp s1 IB s2 i =
       !poss_eval_sigexp poss_eval_spec poss_eval_strdesc.
        ModML_eval_signatures_pred poss_eval_sigexp 
                   poss_eval_spec poss_eval_strdesc ==>
        poss_eval_sigexp sigexp s1 IB s2 i`--);

val eval_spec_DEF = new_definition
    ("eval_spec_DEF",
    --`eval_spec spec s1 IB s2 i =
       !poss_eval_sigexp poss_eval_spec poss_eval_strdesc.
        ModML_eval_signatures_pred poss_eval_sigexp 
                   poss_eval_spec poss_eval_strdesc ==>
        poss_eval_spec spec s1 IB s2 i`--);

val eval_strdesc_DEF = new_definition
    ("eval_strdesc_DEF",
    --`eval_strdesc strdesc s1 IB s2 int =
       !poss_eval_sigexp poss_eval_spec poss_eval_strdesc.
        ModML_eval_signatures_pred
                   poss_eval_sigexp poss_eval_spec poss_eval_strdesc ==>
        poss_eval_strdesc strdesc s1 IB s2 int`--);


val EVAL_SIG_RULES_SATISFIED = store_thm("EVAL_SIG_RULES_SATISFIED",
(--`ModML_eval_signatures_pred eval_sigexp eval_spec eval_strdesc`--),
EVAL_RULE_TAC [ModML_eval_signatures_pred_DEF,eval_sigexp_DEF, eval_spec_DEF,
          eval_strdesc_DEF]);


val ModML_eval_signatures_induction =
    save_thm(" ModML_eval_signatures_induction",
PURE_ONCE_REWRITE_RULE[ModML_eval_signatures_pred_DEF]
(prove
((--`!P_sigexp P_spec P_strdesc.
ModML_eval_signatures_pred P_sigexp P_spec P_strdesc ==>
((!sigexp s1 IB s2 i. eval_sigexp sigexp s1 IB s2 i ==>
                        P_sigexp sigexp s1 IB s2 i) /\
 (!spec s1 IB s2 i. eval_spec spec s1 IB s2 i ==>
                      P_spec spec s1 IB s2 i) /\
 (!strdesc s1 IB s2 int. eval_strdesc strdesc s1 IB s2 int ==>
                             P_strdesc strdesc s1 IB s2 int))`--),
PURE_REWRITE_TAC[eval_sigexp_DEF,eval_spec_DEF,eval_strdesc_DEF] THEN
REPEAT STRIP_TAC THEN RES_TAC)));


val ModML_eval_sigbind_pred_def = 
(--`ModML_eval_sigbind_pred eval_sigbind =

(* Rule 175a *)
(!sigexp IB i sigid s1 s2.
 (eval_sigexp (sigexp:sigexp) (s1:state) (IB:intbasis) (s2:state) (i:int))==>
     (eval_sigbind
      (BINDsigbind (sigid:sigid) (sigexp:sigexp) NONE)
      (s1:state) (IB:intbasis) (s2:state)
      (sigenv_map sigid (i:int)))) /\

(* Rule 175b *)
(!sigbind IB G sigexp i sigid s1 s2 s3.
 ((eval_sigbind (sigbind:sigbind) (s2:state) (IB:intbasis)
                       (s3:state) (G:sigenv)) /\
  (eval_sigexp(sigexp:sigexp)(s1:state) (IB:intbasis) (s2:state) (i:int)))==>
 (eval_sigbind (BINDsigbind (sigid:sigid) (sigexp:sigexp)
		(SOME (sigbind:sigbind)))
  (s1:state) (IB:intbasis) (s3:state) 
  (add_sigenv (sigenv_map sigid (i:int))
   (G:sigenv))))`--)

val ModML_eval_sigbind_pred_DEF = 
   new_definition ("ModML_eval_sigbind_pred_DEF", 
                    ModML_eval_sigbind_pred_def);

val eval_sigbind_DEF = new_definition
    ("eval_sigbind_DEF",
     (--`eval_sigbind sigbind s1 IB s2 G =
      !poss_eval_sigbind. ModML_eval_sigbind_pred poss_eval_sigbind ==>
      poss_eval_sigbind sigbind s1 IB s2 G`--));

val EVAL_STRUCT_RULES_SATISFIED = store_thm("EVAL_SIGBIND_RULES_SATISFIED",
(--`ModML_eval_sigbind_pred eval_sigbind`--),
EVAL_RULE_TAC [ModML_eval_sigbind_pred_DEF,eval_sigbind_DEF]);


val ModML_eval_sigbind_induction =
    save_thm("ModML_eval_sigbind_induction",
PURE_ONCE_REWRITE_RULE[ModML_eval_sigbind_pred_DEF]
(prove
((--`!P_sigbind.
ModML_eval_sigbind_pred P_sigbind ==>
(!sigbind s1 IB s2 G. eval_sigbind sigbind s1 IB s2 G ==>
                      P_sigbind sigbind s1 IB s2 G)`--),
PURE_REWRITE_TAC[eval_sigbind_DEF] THEN
REPEAT STRIP_TAC THEN RES_TAC)));


(* Signature Declarations     IB |- sigdec => G *)

val {desc, induction_thm} = new_inductive_definition
{name = "eval_sigdec_DEF",
 fixity = Prefix,
 patt = ((--`(eval_sigdec (sigdec:sigdec) (s1:state) (IB:intbasis) 
                (s2:state) (G:sigenv)):bool`--),[]),
 rules = [

(* Rule 172 *)
{hypotheses = [],
 side_conditions = [(--`(eval_sigbind (sigbind:sigbind) (s1:state) 
                           (IB:intbasis) (s2:state) (G:sigenv)):bool`--)],
 conclusion = (--`(eval_sigdec (SIGNATUREsigdec (sigbind:sigbind))
                     (s1:state) (IB:intbasis) (s2:state) (G:sigenv)):bool`--)},

(* Rule 173 *)
{hypotheses = [],
 side_conditions = [],
 conclusion = (--`(eval_sigdec EMPTYsigdec (s:state) (IB:intbasis) s
                     empty_sigenv):bool`--)},

(* Rule 174 *)
{hypotheses = [(--`(eval_sigdec (sigdec1:sigdec) (s1:state) (IB:intbasis)
                      (s2:state) (G1:sigenv)):bool`--),
               (--`(eval_sigdec (sigdec2:sigdec) (s2:state) 
                      (add_sigenv_to_intbasis (IB:intbasis) (G1:sigenv))
                      (s3:state) (G2:sigenv)):bool`--)],
 side_conditions = [],
 conclusion = (--`(eval_sigdec (SEQsigdec (sigdec1:sigdec) (sigdec2:sigdec))
                     (s1:state) (IB:intbasis) (s3:state) 
                     (add_sigenv (G1:sigenv) (G2:sigenv))):bool`--)}]};

val [Rule172,Rule173,Rule174] =
    map save_thm(zip ["Rule172","Rule173","Rule174"] desc);
val eval_sigdec_induction_thm =
    save_thm("eval_sigdec_induction_thm",induction_thm);


val ModML_eval_structures_pred_def =
(--`ModML_eval_structures_pred
   (eval_strexp:strexp->state->basis->state->env_pack->bool)
   (eval_strdec:strdec->state->basis->state->env_pack->bool)
   (eval_strbind:strbind->state->basis->state->strenv_pack->bool) =

(* Structure Expressions     B |- strexp => E/p *)

(* Rule 160 *)
    (!B E strdec s1 s2.
       (eval_strdec strdec s1 B s2 (ENVep E)) ==>
       eval_strexp (STRUCTstrexp strdec) s1 B s2 (ENVep E)) /\

    (!B p strdec s1 s2.
       (eval_strdec strdec s1 B s2 (PACKep p)) ==>
       eval_strexp (STRUCTstrexp strdec) s1 B s2 (PACKep p)) /\

(* Rule 161 *)
    (!B E longstrid s. 
       (lift E = lookup_longstrid_basis B longstrid) ==>
       eval_strexp (LONGSTRIDstrexp longstrid) s B s (ENVep E)) /\

(* Rule 162a *)
    (!B B' E E' i funid strexp strexp' strid s1 s2 s3.
       (lift (FUNCLOS strid i strexp' NONE B') = lookup_funid_basis B funid) /\
       (eval_strexp strexp s1 B s2 (ENVep E)) /\
       (eval_strexp 
           strexp' s2 
           (add_basis B' (strenv_in_basis (strenv_map strid (cut_env E i))))
           s3 (ENVep E')) ==>
       (eval_strexp (APPstrexp funid strexp) s1 B s3 (ENVep E'))) /\

    (!B B' i funid p strexp strexp' strid s1 s2.
       (lift (FUNCLOS strid i strexp' NONE B') = lookup_funid_basis B funid) /\
       (eval_strexp strexp s1 B s2 (PACKep p)) ==>
       (eval_strexp (APPstrexp funid strexp) s1 B s2 (PACKep p))) /\

    (!B B' E i funid p strexp strexp' strid s1 s2 s3.
       (lift (FUNCLOS strid i strexp' NONE B') =
                           lookup_funid_basis B funid) /\
       (eval_strexp strexp s1 B s2 (ENVep E)) /\
       (eval_strexp 
           strexp' s2 
           (add_basis B' (strenv_in_basis (strenv_map strid (cut_env E i))))
           s3 (PACKep p)) ==>
       (eval_strexp (APPstrexp funid strexp) s1 B s3 (PACKep p))) /\

(* Rule 162b *)
    (!B B' E E' i i' funid strexp strexp' strid s1 s2 s3.
       (lift (FUNCLOS strid i strexp' (SOME i') B') =
                             lookup_funid_basis B funid) /\
       (eval_strexp strexp s1 B s2 (ENVep E)) /\
       (eval_strexp 
           strexp' s2 
           (add_basis B' (strenv_in_basis (strenv_map strid (cut_env E i))))
           s3 (ENVep E')) ==>
       (eval_strexp (APPstrexp funid strexp)
                     s1 B s3 (ENVep (cut_env E' i')))) /\

(* Change all CONSTRAINfunclos! *)
    (!B B' i i' funid p strexp strexp' strid s1 s2.
       (lift (FUNCLOS strid i strexp' (SOME i') B') = 
                             lookup_funid_basis B funid) /\
       (eval_strexp strexp s1 B s2 (PACKep p)) ==>
       (eval_strexp (APPstrexp funid strexp) s1 B s2 (PACKep p))) /\

    (!B B' E i i' funid p strexp strexp' strid s1 s2 s3.
       (lift (FUNCLOS strid i strexp' (SOME i') B') =
                             lookup_funid_basis B funid) /\
       (eval_strexp strexp s1 B s2 (ENVep E)) /\
       (eval_strexp 
           strexp' s2 
           (add_basis B' (strenv_in_basis (strenv_map strid (cut_env E i))))
           s3 (PACKep p)) ==>
       (eval_strexp (APPstrexp funid strexp) s1 B s3 (PACKep p))) /\

(* Rule 163 *)

    (!B E E' strdec strexp s1 s2 s3.
       (eval_strdec strdec s1 B s2 (ENVep E)) /\
       (eval_strexp strexp s2 (add_env_to_basis B E) s3 (ENVep E')) ==>
       (eval_strexp (LETstrexp strdec strexp) s1 B s3 (ENVep E'))) /\

    (!B p strdec strexp s1 s2.
       (eval_strdec strdec s1 B s2 (PACKep p)) ==>
       (eval_strexp (LETstrexp strdec strexp) s1 B s2 (PACKep p))) /\

    (!B E p strdec strexp s1 s2 s3.
       (eval_strdec strdec s1 B s2 (ENVep E)) /\
       (eval_strexp strexp s2 (add_env_to_basis B E) s3 (PACKep p)) ==>
       (eval_strexp (LETstrexp strdec strexp) s1 B s3 (PACKep p))) /\

(* Structure Declarations     B |- strdec => E/p *)

(* Rule 164 *)
    (!B E' dec s1 s2.
       (eval_dec dec s1 (env_of_basis B) s2 (ENVep E')) ==>
       (eval_strdec (DECstrdec dec) s1 B s2 (ENVep E'))) /\

    (!B dec p s1 s2.
       (eval_dec dec s1 (env_of_basis B) s2 (PACKep p)) ==>
       (eval_strdec (DECstrdec dec) s1 B s2 (PACKep p))) /\

(* Rule 165 *)
    (!B SE strbind s1 s2.
       (eval_strbind strbind s1 B s2 (STRENVsp SE)) ==>
       (eval_strdec (STRUCTUREstrdec strbind) s1 B s2 
                               (ENVep (strenv_in_env SE)))) /\

    (!B p strbind s1 s2.
       (eval_strbind strbind s1 B s2 (PACKsp p)) ==>
       (eval_strdec (STRUCTUREstrdec strbind) s1 B s2 (PACKep p))) /\

(* Rule 166 *)

    (!B E1 E2 strdec1 strdec2 s1 s2 s3.
       (eval_strdec strdec1 s1 B s2 (ENVep E1)) /\
       (eval_strdec strdec2 s2 (add_env_to_basis B E1) s3 (ENVep E2)) ==>
       (eval_strdec (LOCALstrdec strdec1 strdec2) s1 B s3 (ENVep E2))) /\

    (!B p strdec1 strdec2 s1 s2.
       (eval_strdec strdec1 s1 B s2 (PACKep p)) ==>
       (eval_strdec (LOCALstrdec strdec1 strdec2) s1 B s2 (PACKep p))) /\

    (!B E p strdec1 strdec2 s1 s2 s3.
       (eval_strdec strdec1 s1 B s2 (ENVep E)) /\
       (eval_strdec strdec2 s2 (add_env_to_basis B E) s3 (PACKep p)) ==>
       (eval_strdec (LOCALstrdec strdec1 strdec2) s1 B s3 (PACKep p))) /\

(* Rule 167 *)
    (!B s. eval_strdec EMPTYstrdec s B s (ENVep empty_env)) /\

(* Rule 168 *)
    (!B E1 E2 strdec1 strdec2 s1 s2 s3.
       (eval_strdec strdec1 s1 B s2 (ENVep E1)) /\
       (eval_strdec strdec2 s2 (add_env_to_basis B E1) s3 (ENVep E2)) ==>
       (eval_strdec (SEQstrdec strdec1 strdec2)
                    s1 B s3 (ENVep (add_env E1 E2)))) /\

    (!B p strdec1 strdec2 s1 s2.
       (eval_strdec strdec1 s1 B s2 (PACKep p)) ==>
       (eval_strdec (SEQstrdec strdec1 strdec2) s1 B s2 (PACKep p))) /\

    (!B E p strdec1 strdec2 s1 s2 s3.
       (eval_strdec strdec1 s1 B s2 (ENVep E)) /\
       (eval_strdec strdec2 s2 (add_env_to_basis B E) s3 (PACKep p)) ==>
       (eval_strdec (SEQstrdec strdec1 strdec2) s1 B s3 (PACKep p))) /\

(* Structure Bindings     B |- strbind => SE/p *)

(* Rule 169a *)
    (!B E strexp strid s1 s2.
       (eval_strexp strexp s1 B s2 (ENVep E)) ==>
       (eval_strbind (BINDstrbind strid NONE strexp NONE) s1 B 
                     s2 (STRENVsp (strenv_map strid E)))) /\

    (!B p strexp strid s1 s2.
       (eval_strexp strexp s1 B s2 (PACKep p)) ==>
       (eval_strbind (BINDstrbind strid NONE strexp NONE)
	              s1 B s2 (PACKsp p))) /\

(* Rule 169b *) 
    (!B E i sigexp strexp strid s1 s2 s3.
       (eval_strexp strexp s1 B s2 (ENVep E)) /\
       (eval_sigexp sigexp s2 (Inter_basis B) s3 i) ==>
       (eval_strbind (BINDstrbind strid (SOME sigexp) strexp NONE) s1 B
                       s3 (STRENVsp (strenv_map strid (cut_env E i))))) /\

    (!B p sigexp strexp strid s1 s2.
       (eval_strexp strexp s1 B s2 (PACKep p)) ==>
       (eval_strbind 
          (BINDstrbind strid (SOME sigexp) strexp NONE) s1 B s2 (PACKsp p))) /\
    
(* Rule 169c *)
    (!B E SE strbind strexp strid s1 s2 s3.
       (eval_strexp strexp s1 B s2 (ENVep E)) /\
       (eval_strbind strbind s2 B s3 (STRENVsp SE)) ==>
       (eval_strbind (BINDstrbind strid NONE strexp (SOME strbind)) s1 B s3
           (STRENVsp (add_strenv (strenv_map strid E) SE)))) /\

    (!B p strbind strexp strid s1 s2.
       (eval_strexp strexp s1 B s2 (PACKep p)) ==>
       (eval_strbind 
         (BINDstrbind strid NONE strexp (SOME strbind)) s1 B s2 (PACKsp p))) /\

    (!B E p strbind strexp  strid s1 s2 s3.
       (eval_strexp strexp s1 B s2 (ENVep E)) /\
       (eval_strbind strbind s2 B s3 (PACKsp p)) ==>
       (eval_strbind 
         (BINDstrbind strid NONE strexp (SOME strbind)) s1 B s3 (PACKsp p))) /\

(* Rule 169d *)
   (!B E i SE sigexp strbind strexp strid s1 s2 s3 s4.
       (eval_strexp strexp s1 B s2 (ENVep E)) /\
       (eval_sigexp sigexp s2 (Inter_basis B) s3 i) /\
       (eval_strbind strbind s3 B s4 (STRENVsp SE)) ==>
       (eval_strbind (BINDstrbind strid (SOME sigexp) strexp (SOME strbind))
          s1 B s4
	  (STRENVsp (add_strenv (strenv_map strid (cut_env E i)) SE)))) /\

   (!B p sigexp strbind strexp strid s1 s2. 
       (eval_strexp strexp s1 B s2 (PACKep p)) ==>
       (eval_strbind (BINDstrbind strid (SOME sigexp) strexp (SOME strbind))
           s1 B s2 (PACKsp p))) /\

   (!B E i p sigexp strbind strexp strid s1 s2 s3 s4.
       (eval_strexp strexp s1 B s2 (ENVep E)) /\
       (eval_sigexp sigexp s2 (Inter_basis B) s3 i) /\
       (eval_strbind strbind s3 B s4 (PACKsp p)) ==>
       (eval_strbind (BINDstrbind strid (SOME sigexp) strexp (SOME strbind))
           s1 B s4 (PACKsp p)))`--);

val ModML_eval_structures_pred_DEF = new_definition
("ModML_eval_structures_pred_DEF", ModML_eval_structures_pred_def);

val eval_strexp_DEF = new_definition
("eval_strexp_DEF",
--`eval_strexp strexp s1 B s2 ep =
   !poss_eval_strexp poss_eval_strdec poss_eval_strbind.
   ModML_eval_structures_pred
       poss_eval_strexp poss_eval_strdec poss_eval_strbind ==>
   poss_eval_strexp strexp s1 B s2 ep`--);

val eval_strdec_DEF = new_definition
("eval_strdec_DEF",
--`eval_strdec strdec s1 B s2 ep =
   !poss_eval_strexp poss_eval_strdec poss_eval_strbind.
   ModML_eval_structures_pred 
       poss_eval_strexp poss_eval_strdec poss_eval_strbind ==>
   poss_eval_strdec strdec s1 B s2 ep`--);

val eval_strbind_DEF = new_definition
("eval_strbind_DEF",
--`eval_strbind strbind s1 B s2 sep =
   !poss_eval_strexp poss_eval_strdec poss_eval_strbind.
   ModML_eval_structures_pred 
       poss_eval_strexp poss_eval_strdec poss_eval_strbind ==>
   poss_eval_strbind strbind s1 B s2 sep`--);

val EVAL_STRUCT_RULES_SATISFIED = store_thm("EVAL_STRUCT_RULES_SATISFIED",
(--`ModML_eval_structures_pred eval_strexp eval_strdec eval_strbind`--),
EVAL_RULE_TAC [ModML_eval_structures_pred_DEF,eval_strexp_DEF, eval_strdec_DEF,
          eval_strbind_DEF]);


val ModML_eval_structures_induction =
    save_thm("ModML_eval_structures_induction",
PURE_ONCE_REWRITE_RULE[ModML_eval_structures_pred_DEF]
(prove
((--`!P_strexp P_strdec P_strbind.
ModML_eval_structures_pred P_strexp P_strdec P_strbind ==>
((!strexp s1 B s2 ep. eval_strexp strexp s1 B s2 ep ==>
                      P_strexp strexp s1 B s2 ep) /\
 (!strdec s1 B s2 ep. eval_strdec strdec s1 B s2 ep ==>
                      P_strdec strdec s1 B s2 ep) /\
 (!strbind s1 B s2 sep. eval_strbind strbind s1 B s2 sep ==>
                      P_strbind strbind s1 B s2 sep))`--),
PURE_REWRITE_TAC[eval_strexp_DEF, eval_strdec_DEF, eval_strbind_DEF] THEN
REPEAT STRIP_TAC THEN RES_TAC)));


(* Functor Bindings     B |- funbind => F *)

val ModML_eval_funbind_pred_def =
(--`ModML_eval_funbind_pred eval_funbind =

(* Rule 187a *)
(!sigexp B i funid strid strexp s1 s2.
 (eval_sigexp (sigexp:sigexp) (s1:state) 
              (Inter_basis (B:basis)) (s2:state) (i:int)) ==>
 (eval_funbind (BINDfunbind (funid:funid) (strid:strid)
                            (sigexp:sigexp) NONE (strexp:strexp) NONE)
               (s1:state) (B:basis) (s2:state)
               (funenv_map funid 
                         (FUNCLOS strid (i:int) strexp NONE B)))) /\

(* Rule 187b *)
(!sigexp sigexp' B i i' funid strid strexp s1 s2 s3.
((eval_sigexp (sigexp:sigexp) (s1:state) 
              (Inter_basis (B:basis))(s2:state) (i:int)) /\
 (eval_sigexp (sigexp':sigexp) (s2:state)
              (add_intenv_to_intbasis 
                (Inter_basis (B:basis))
                (intenv_map (strid:strid) (i:int)))
             (s3:state) (i':int))) ==>
(eval_funbind (BINDfunbind (funid:funid) (strid:strid)
                           (sigexp:sigexp) (SOME(sigexp':sigexp)) 
                           (strexp:strexp) NONE)
              (s1:state) (B:basis) (s3:state)
              (funenv_map funid 
                         (FUNCLOS strid (i:int) strexp (SOME(i':int)) B)))) /\

(* Rule 187c *)
(!sigexp B i funbind f funid strid strexp s1 s2 s3.
 ((eval_sigexp (sigexp:sigexp) (s1:state) 
               (Inter_basis (B:basis)) (s2:state) (i:int)) /\
  (eval_funbind (funbind:funbind) (s2:state) (B:basis)
                (s3:state) (f:funenv))) ==>
 (eval_funbind (BINDfunbind (funid:funid) (strid:strid)
                            (sigexp:sigexp) NONE (strexp:strexp)
                            (SOME (funbind:funbind)))
               (s1:state) (B:basis) (s3:state)
               (add_funenv 
		(funenv_map funid 
                            (FUNCLOS strid (i:int) strexp NONE B))
                (f:funenv)))) /\

(* Rule 187d *)
(!sigexp sigexp' B i i' funbind f funid strid strexp s1 s2 s3 s4.
 ((eval_sigexp (sigexp:sigexp) (s1:state) 
               (Inter_basis (B:basis)) (s2:state) (i:int)) /\
  (eval_sigexp (sigexp':sigexp) (s2:state)
               (add_intenv_to_intbasis
		(Inter_basis (B:basis))
		(intenv_map (strid:strid) (i:int)))
	       (s3:state) (i':int)) /\
  (eval_funbind (funbind:funbind) (s3:state) (B:basis)
                (s4:state) (f:funenv))) ==>
 (eval_funbind (BINDfunbind (funid:funid) (strid:strid) (sigexp:sigexp)
                            (SOME(sigexp':sigexp)) (strexp:strexp) 
			    (SOME(funbind:funbind)))
               (s1:state) (B:basis) (s4:state)
	       (add_funenv
		(funenv_map funid 
                            (FUNCLOS strid (i:int) strexp (SOME(i':int)) B))
                        (f:funenv))))`--);

val ModML_eval_funbind_pred_DEF = new_definition
("ModML_eval_funbind_pred_DEF", ModML_eval_funbind_pred_def);

val eval_funbind_DEF = new_definition
("eval_funbind_DEF",
--`eval_funbind funbind s1 B s2 f =
   !poss_eval_funbind.
   ModML_eval_funbind_pred poss_eval_funbind ==>
   poss_eval_funbind funbind s1 B s2 f`--);

val EVAL_FUNBIND_RULES_SATISFIED = store_thm("EVAL_FUNBIND_RULES_SATISFIED",
(--`ModML_eval_funbind_pred eval_funbind`--),
EVAL_RULE_TAC [ModML_eval_funbind_pred_DEF,eval_funbind_DEF]);


val ModML_eval_funbind_induction =
    save_thm("ModML_eval_funbind_induction",
PURE_ONCE_REWRITE_RULE[ModML_eval_funbind_pred_DEF]
(prove
((--`!P_funbind.
ModML_eval_funbind_pred P_funbind ==>
(!funbind s1 B s2 f. eval_funbind funbind s1 B s2 f ==>
                    P_funbind funbind s1 B s2 f)`--),
PURE_REWRITE_TAC[eval_funbind_DEF] THEN
REPEAT STRIP_TAC THEN RES_TAC)));



(* Functor Declarations     B |- fundec => F *)

val {desc, induction_thm} = new_inductive_definition
{name = "eval_fundec_DEF",
 fixity = Prefix,
 patt = ((--`(eval_fundec (fundec:fundec) (s1:state) (B:basis) 
                (s2:state) (f:funenv)):bool`--),[]),
 rules = [

(* Rule 188 *)
{hypotheses = [],
 side_conditions = [(--`(eval_funbind (funbind:funbind) (s1:state) (B:basis)
                          (s2:state) (f:funenv)):bool`--)],
 conclusion = (--`(eval_fundec (FUNCTORfundec (funbind:funbind))
                     (s1:state) (B:basis) (s2:state) (f:funenv)):bool`--)},

(* Rule 189 *)
{hypotheses = [],
 side_conditions = [],
 conclusion = (--`(eval_fundec EMPTYfundec (s:state) (B:basis) s
                     empty_funenv):bool`--)},

(* Rule 190 *)
{hypotheses = [(--`(eval_fundec (fundec1:fundec) (s1:state) (B:basis)
                      (s2:state) (F1:funenv)):bool`--),
               (--`(eval_fundec (fundec2:fundec) (s2:state) 
                      (add_funenv_to_basis (B:basis) (F1:funenv))
                      (s3:state) (F2:funenv)):bool`--)],
 side_conditions = [],
 conclusion = (--`(eval_fundec (SEQfundec (fundec1:fundec) (fundec2:fundec))
                     (s1:state) (B:basis) (s3:state) 
                     (add_funenv (F1:funenv) (F2:funenv))):bool`--)}]};

val [Rule188,Rule189,Rule190] = 
    map save_thm (zip ["Rule188","Rule189","Rule190"] desc);
val eval_fundec_induction_thm =
    save_thm("eval_fundec_induction_thm",induction_thm);

(* Top-level Declarations      B |- topdec => B'/p *)

val {desc, induction_thm} = new_inductive_definition
{name = "eval_topdec_DEF",
 fixity = Prefix,
 patt = ((--`(eval_topdec (topdec:topdec) (s1:state) (B:basis) 
                (s2:state) (bp:basis_pack)):bool`--),[]),
 rules = [

(* Rule 191 *)
{hypotheses = [],
 side_conditions = [(--`(eval_strdec (strdec:strdec) (s1:state) (B:basis)
                           (s2:state) (ENVep (E:env))):bool`--)],
 conclusion = (--`(eval_topdec (STRDEC (strdec:strdec)) (s1:state) (B:basis) 
                     (s2:state) (BASISbp (env_in_basis (E:env)))):bool`--)},

{hypotheses = [],
 side_conditions = [(--`(eval_strdec (strdec:strdec) (s1:state) (B:basis)
                           (s2:state) (PACKep (p:pack))):bool`--)],
 conclusion = (--`(eval_topdec (STRDEC (strdec:strdec)) (s1:state) (B:basis) 
                     (s2:state) (PACKbp (p:pack))):bool`--)},

(* Rule 192 *)
{hypotheses = [],
 side_conditions = [(--`(eval_sigdec (sigdec:sigdec) (s1:state) 
                     (Inter_basis (B:basis)) (s2:state) (G:sigenv)):bool`--)],
 conclusion = (--`(eval_topdec (SIGDEC (sigdec:sigdec)) (s1:state) (B:basis)
                  (s2:state) (BASISbp (sigenv_in_basis (G:sigenv)))):bool`--)},

(* Rule 193 *)
{hypotheses = [],
 side_conditions = [(--`(eval_fundec (fundec:fundec) (s1:state) (B:basis)
                           (s2:state) (f:funenv)):bool`--)],
 conclusion = (--`(eval_topdec (FUNDEC (fundec:fundec)) (s1:state) (B:basis) 
                (s2:state) (BASISbp (funenv_in_basis (f:funenv)))):bool`--)}]};


val [Rule191,Rule192a,Rule192,Rule193] =
    map save_thm(zip ["Rule191","Rule192","Rule192b","Rule193"] desc);
val eval_topdec_induction_thm =
    save_thm("eval_topdec_induction_thm",induction_thm);


