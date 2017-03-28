(* File: HOFML/eval.sml *)

(* Description: This file contains proposed definitions for the evaluation
   relations that give the dynamic semantics of the ML Module system
   extended with higher-order functors.                              *)


val HOFML_eval_signatures_pred_def =
--`HOFML_eval_signatures_pred
   (eval_sigexp_h:sigexp_h->state->intbasis_h->state->int_h->bool)
   (eval_spec_h:spec_h->state->intbasis_h->state->int_h->bool)
   (eval_strdesc_h:strdesc_h->state->intbasis_h->state->strintenv_h->bool) =

(* Signature Expressions     IB |- sigexp_h => I *)

(* Rule 170 *)
   (!i IB spec s1 s2. 
       (eval_spec_h spec s1 IB s2 i) ==> 
       (eval_sigexp_h (SIGsigexp_h spec) s1 IB s2 i)) /\

(* Rule 171 *)
   (!i IB s sigid.
       (lookup_sigid_intbasis_h IB sigid = lift i) ==>
       (eval_sigexp_h (SIGIDsigexp_h sigid) s IB s i)) /\

(* Specifications     IB |- spec_h => I *)

(* Rule 176 *)
   (!IB valdesc vars s1 s2.
       (eval_valdesc valdesc s1 s2 vars) ==>
       (eval_spec_h (VALspec_h valdesc) s1 IB s2 (vars_in_int_h vars))) /\

(* Rule 177 *)
   (!IB excons exdesc s1 s2.
       (eval_exdesc exdesc s1 s2 excons) ==>
       (eval_spec_h (EXCEPTIONspec_h exdesc) s1 IB s2 
                    (excons_in_int_h excons))) /\

(* Rule 178 *)
   (!IB SIE strdesc_h s1 s2.
       (eval_strdesc_h strdesc_h s1 IB s2 SIE) ==>
       (eval_spec_h (STRUCTUREspec_h strdesc_h) s1 IB s2 
                    (strintenv_h_in_int_h SIE))) /\

(* Rule 179 *)   
   (!IB I1 I2 spec_h1 spec_h2 s1 s2 s3.
       (eval_spec_h spec_h1 s1 IB s2 I1) /\
       (eval_spec_h spec_h2 s2 
         (add_strintenv_h_to_intbasis_h IB (strintenv_h_of_int_h I1))
         s3 I2) ==>
       (eval_spec_h (LOCALspec_h spec_h1 spec_h2) s1 IB s3 I2)) /\

(* Rule 180 *) (* Changed by Elsa to map lift, not map lower *)
   (!IB nonempty_int_h_list nonempty_lift_int_h_list
     nonempty_longstrid_list s.
      ((nonempty_MAP (lookup_longstrid_intbasis_h IB) 
              nonempty_longstrid_list) = nonempty_lift_int_h_list) /\
      ((nonempty_MAP lift nonempty_int_h_list) = nonempty_lift_int_h_list) ==>
      (eval_spec_h (OPENspec_h nonempty_longstrid_list) s IB 
           s (nonempty_FOLDL_WITH_INIT add_int_h nonempty_int_h_list))) /\

(* Rule 181 *) (* Changed by Elsa to map lift, not map lower *)
   (!IB nonempty_int_h_list nonempty_lift_int_h_list nonempty_sigid_list s.
      ((nonempty_MAP (lookup_sigid_intbasis_h IB) nonempty_sigid_list)
            = nonempty_lift_int_h_list) /\
      ((nonempty_MAP lift nonempty_int_h_list) = nonempty_lift_int_h_list) ==>
      (eval_spec_h (INCLUDEspec_h nonempty_sigid_list) s IB 
           s (nonempty_FOLDL_WITH_INIT add_int_h nonempty_int_h_list))) /\

(* Rule 182 *)
    (!IB s. eval_spec_h EMPTYspec_h s IB s empty_int_h) /\

(* Rule 183 *)
    (!IB I1 I2 spec_h1 spec_h2 s1 s2 s3.
       (eval_spec_h spec_h1 s1 IB s2 I1) /\
       (eval_spec_h spec_h2 s2 
         (add_strintenv_h_to_intbasis_h IB (strintenv_h_of_int_h I1))
	 s3 I2) ==>
       (eval_spec_h (SEQspec_h spec_h1 spec_h2) s1 IB s3 (add_int_h I1 I2))) /\

(* New Rule (A) *)

(*
      IB |- sigexp_h => I1       IB + {strid -> I1} |- sig exp_h' => I2
----------------------------------------------------------------------------
 IB |- functor funid (strid : sigexp_h) : sigexp_h' => {funid -> I2} in Int
*)
    (!IB I1 I2 funid sigexp_h sigexp_h' strid s1 s2 s3.
       (eval_sigexp_h sigexp_h s1 IB s2 I1) /\
       (eval_sigexp_h sigexp_h' s2 
           (add_strintenv_h_to_intbasis_h IB (strintenv_h_map strid I1))
            s3 I2) ==>
       (eval_spec_h (FUNCTORspec_h funid strid sigexp_h sigexp_h') s1 IB s3
           (funintenv_h_in_int_h (funintenv_h_map funid I1)))) /\  


(* Structure Descriptions     IB |- strdesc_h => SIE *)

(* Rule 186a *)
    (!i IB sigexp_h strid s1 s2.
       (eval_sigexp_h sigexp_h s1 IB s2 i) ==>
       (eval_strdesc_h (STRIDstrdesc_h strid sigexp_h NONE) s1 IB 
             s2 (strintenv_h_map strid i))) /\

(* Rule 186b *)
    (!i IB SIE sigexp_h strdesc_h strid s1 s2 s3.
       (eval_sigexp_h sigexp_h s1 IB s2 i) /\
       (eval_strdesc_h strdesc_h s2 IB s3 SIE) ==>
       (eval_strdesc_h (STRIDstrdesc_h strid sigexp_h (SOME strdesc_h)) s1 IB
             s3 (add_strintenv_h (strintenv_h_map strid i) SIE)))`--;

val HOFML_eval_signatures_pred_DEF = 
   new_definition ("HOFML_eval_signatures_pred_DEF", 
                    HOFML_eval_signatures_pred_def);

val eval_sigexp_h_DEF = new_definition
    ("eval_sigexp_h_DEF",
    --`eval_sigexp_h sigexp_h s1 IB s2 i =
       !poss_eval_sigexp_h poss_eval_spec_h poss_eval_strdesc_h.
        HOFML_eval_signatures_pred poss_eval_sigexp_h 
                   poss_eval_spec_h poss_eval_strdesc_h ==>
        poss_eval_sigexp_h sigexp_h s1 IB s2 i`--);

val eval_spec_h_DEF = new_definition
    ("eval_spec_h_DEF",
    --`eval_spec_h spec_h s1 IB s2 i =
       !poss_eval_sigexp_h poss_eval_spec_h poss_eval_strdesc_h.
        HOFML_eval_signatures_pred poss_eval_sigexp_h 
                   poss_eval_spec_h poss_eval_strdesc_h ==>
        poss_eval_spec_h spec_h s1 IB s2 i`--);

val eval_strdesc_h_DEF = new_definition
    ("eval_strdesc_h_DEF",
    --`eval_strdesc_h strdesc_h s1 IB s2 int_h =
       !poss_eval_sigexp_h poss_eval_spec_h poss_eval_strdesc_h.
        HOFML_eval_signatures_pred
                   poss_eval_sigexp_h poss_eval_spec_h poss_eval_strdesc_h ==>
        poss_eval_strdesc_h strdesc_h s1 IB s2 int_h`--);

val HOFML_EVAL_SIG_RULES_SATISFIED =
store_thm("HOFML_EVAL_SIG_RULES_SATISFIED",
(--`HOFML_eval_signatures_pred eval_sigexp_h eval_spec_h eval_strdesc_h`--),
EVAL_RULE_TAC [HOFML_eval_signatures_pred_DEF,
	       eval_sigexp_h_DEF, eval_spec_h_DEF, eval_strdesc_h_DEF]);


val HOFML_eval_signatures_h_induction =
save_thm("HOFML_eval_signatures_h_induction",
PURE_ONCE_REWRITE_RULE[HOFML_eval_signatures_pred_DEF]
(prove
((--`!P_sigexp_h P_spec_h P_strdesc_h.
HOFML_eval_signatures_pred P_sigexp_h  P_spec_h P_strdesc_h ==>
((!sigexp_h s1 IB s2 i. eval_sigexp_h sigexp_h s1 IB s2 i ==>
                        P_sigexp_h sigexp_h s1 IB s2 i) /\
 (!spec_h s1 IB s2 i. eval_spec_h spec_h s1 IB s2 i ==>
                      P_spec_h spec_h s1 IB s2 i) /\
 (!strdesc_h s1 IB s2 int_h. eval_strdesc_h strdesc_h s1 IB s2 int_h ==>
                             P_strdesc_h strdesc_h s1 IB s2 int_h))`--),
PURE_REWRITE_TAC[eval_sigexp_h_DEF,eval_spec_h_DEF,eval_strdesc_h_DEF] THEN
REPEAT STRIP_TAC THEN RES_TAC)));



val {desc, induction_thm} = new_inductive_definition
{name = "eval_sigbind_h_DEF",
 fixity = Prefix,
 patt = ((--`(eval_sigbind_h (sigbind_h:sigbind_h) (s1:state) (IB:intbasis_h) 
                (s2:state) (G:sigenv_h)):bool`--),[]),
 rules = [

(* Rule 175a *)
{hypotheses = [],
 side_conditions = 
 [(--`(eval_sigexp_h (sigexp_h:sigexp_h) (s1:state) (IB:intbasis_h)
                           (s2:state) (i:int_h)):bool`--)],
 conclusion = 
  (--`(eval_sigbind_h (BINDsigbind_h (sigid:sigid) (sigexp_h:sigexp_h) NONE)
                     (s1:state) (IB:intbasis_h) (s2:state)
                     (sigenv_h_map sigid (i:int_h))):bool`--)},

(* Rule 175b *)
{hypotheses = 
 [(--`(eval_sigbind_h (sigbind_h:sigbind_h) (s2:state) (IB:intbasis_h)
                       (s3:state) (G:sigenv_h)):bool`--)],
 side_conditions = 
 [(--`(eval_sigexp_h (sigexp_h:sigexp_h) (s1:state) (IB:intbasis_h)
                     (s2:state) (i:int_h)):bool`--)],
 conclusion = 
 (--`(eval_sigbind_h (BINDsigbind_h (sigid:sigid) (sigexp_h:sigexp_h) 
                                    (SOME(sigbind_h:sigbind_h)))
                     (s1:state) (IB:intbasis_h) (s3:state) 
                     (add_sigenv_h (sigenv_h_map sigid (i:int_h))
                                 (G:sigenv_h))):bool`--)}]};

val [Rule175a_h,Rule175b_h] =
    map save_thm (zip ["Rule175a_h","Rule175b_h"] desc);
val eval_sigbind_h_induction_thm =
    save_thm("eval_sigbind_h_induction_thm",induction_thm);


(* Signature Declarations     IB |- sigdec_h => G *)

val {desc, induction_thm} = new_inductive_definition
{name = "eval_sigdec_h_DEF",
 fixity = Prefix,
 patt = ((--`(eval_sigdec_h (sigdec_h:sigdec_h) (s1:state) (IB:intbasis_h) 
                (s2:state) (G:sigenv_h)):bool`--),[]),
 rules = [

(* Rule 172 *)
{hypotheses = [],
 side_conditions = [(--`(eval_sigbind_h (sigbind_h:sigbind_h) (s1:state) 
                           (IB:intbasis_h) (s2:state) (G:sigenv_h)):bool`--)],
 conclusion = (--`(eval_sigdec_h (SIGNATUREsigdec_h (sigbind_h:sigbind_h))
                 (s1:state) (IB:intbasis_h) (s2:state) (G:sigenv_h)):bool`--)},

(* Rule 173 *)
{hypotheses = [],
 side_conditions = [],
 conclusion = (--`(eval_sigdec_h EMPTYsigdec_h (s:state) (IB:intbasis_h) s
                     empty_sigenv_h):bool`--)},

(* Rule 174 *)
{hypotheses = 
[(--`(eval_sigdec_h (sigdec_h1:sigdec_h) (s1:state) (IB:intbasis_h)
                      (s2:state) (G1:sigenv_h)):bool`--),
 (--`(eval_sigdec_h (sigdec_h2:sigdec_h) (s2:state) 
                    (add_sigenv_h_to_intbasis_h (IB:intbasis_h) (G1:sigenv_h))
                      (s3:state) (G2:sigenv_h)):bool`--)],
 side_conditions = [],
 conclusion = 
(--`(eval_sigdec_h (SEQsigdec_h (sigdec_h1:sigdec_h) (sigdec_h2:sigdec_h))
                     (s1:state) (IB:intbasis_h) (s3:state) 
                     (add_sigenv_h (G1:sigenv_h) (G2:sigenv_h))):bool`--)}]};

val [Rule172_h,Rule_173_h,Rule_174_h] =
    map save_thm (zip ["Rule172_h","Rule_173_h","Rule_174_h"] desc);
val eval_sigdec_h_induction_thm =
    save_thm("eval_sigdec_h_induction_thm",induction_thm);


val HOFML_eval_structures_pred_def =
--`HOFML_eval_structures_pred
   (eval_strexp_h:strexp_h->state->basis_h->state->env_pack_h->bool)
   (eval_moddec_h:moddec_h->state->basis_h->state->env_pack_h->bool)
   (eval_strbind_h:strbind_h->state->basis_h->state->strenv_pack_h->bool)
   (eval_funbind_h:funbind_h->state->basis_h->state->funenv_h->bool) =

(* Structure Expressions     B |- strexp_h => E/p *)

(* Rule 160 *)
    (!B E moddec_h s1 s2.
       (eval_moddec_h moddec_h s1 B s2 (ENVep_h E)) ==>
       eval_strexp_h (STRUCTstrexp_h moddec_h) s1 B s2 (ENVep_h E)) /\

    (!B p moddec_h s1 s2.
       (eval_moddec_h moddec_h s1 B s2 (PACKep_h p)) ==>
       eval_strexp_h (STRUCTstrexp_h moddec_h) s1 B s2 (PACKep_h p)) /\

(* Rule 161 *)
    (!B E longstrid s. 
       (lift E = lookup_longstrid_basis_h B longstrid) ==>
       eval_strexp_h (LONGSTRIDstrexp_h longstrid) s B s (ENVep_h E)) /\


(* Rule 162a  *)  (* different -long funids *)
    (!B B' E E' i longfunid strexp_h strexp_h' strid s1 s2 s3.
       (lift (FUNCLOS_H strid i strexp_h' NONE B') =
	          lookup_longfunid_basis_h B longfunid) /\
       (eval_strexp_h strexp_h s1 B s2 (ENVep_h E)) /\
       (eval_strexp_h
           strexp_h' s2
           (add_basis_h B'
	    (strenv_h_in_basis_h (strenv_h_map strid (cut_env_h E i))))
	    s3 (ENVep_h E')) ==>
       (eval_strexp_h (APPstrexp_h longfunid strexp_h)
	               s1 B s3 (ENVep_h E'))) /\

    (!B B' i longfunid p strexp_h strexp_h' strid s1 s2.
       (lift (FUNCLOS_H strid i strexp_h' NONE B') = 
                             lookup_longfunid_basis_h B longfunid) /\
       (eval_strexp_h strexp_h s1 B s2 (PACKep_h p)) ==>
       (eval_strexp_h (APPstrexp_h longfunid strexp_h) 
                      s1 B s2 (PACKep_h p))) /\

    (!B B' E i longfunid p strexp_h strexp_h' strid s1 s2 s3.
       (lift (FUNCLOS_H strid i strexp_h' NONE B') =
                             lookup_longfunid_basis_h B longfunid) /\
       (eval_strexp_h strexp_h s1 B s2 (ENVep_h E)) /\
       (eval_strexp_h 
           strexp_h' s2 
           (add_basis_h B' 
           (strenv_h_in_basis_h (strenv_h_map strid (cut_env_h E i))))
           s3 (PACKep_h p)) ==>
       (eval_strexp_h (APPstrexp_h longfunid strexp_h) 
                      s1 B s3 (PACKep_h p))) /\

(* Rule 162b *)  (* different - long funids *)
    (!B B' E E' i i' longfunid strexp_h strexp_h' strid s1 s2 s3.
       (lift (FUNCLOS_H strid i strexp_h' (SOME i') B') =
                             lookup_longfunid_basis_h B longfunid) /\
       (eval_strexp_h strexp_h s1 B s2 (ENVep_h E)) /\
       (eval_strexp_h 
           strexp_h' s2 
           (add_basis_h B' 
           (strenv_h_in_basis_h (strenv_h_map strid (cut_env_h E i))))
           s3 (ENVep_h E')) ==>
       (eval_strexp_h (APPstrexp_h longfunid strexp_h)
                     s1 B s3 (ENVep_h (cut_env_h E' i')))) /\

    (!B B' i i' longfunid p strexp_h strexp_h' strid s1 s2.
       (lift (FUNCLOS_H strid i strexp_h'  (SOME i') B') = 
                             lookup_longfunid_basis_h B longfunid) /\
       (eval_strexp_h strexp_h s1 B s2 (PACKep_h p)) ==>
       (eval_strexp_h (APPstrexp_h longfunid strexp_h) 
                      s1 B s2 (PACKep_h p))) /\

    (!B B' E i i' longfunid p strexp_h strexp_h' strid s1 s2 s3.
       (lift (FUNCLOS_H strid i strexp_h' (SOME i') B') =
                             lookup_longfunid_basis_h B longfunid) /\
       (eval_strexp_h strexp_h s1 B s2 (ENVep_h E)) /\
       (eval_strexp_h 
           strexp_h' s2 
           (add_basis_h B' 
           (strenv_h_in_basis_h (strenv_h_map strid (cut_env_h E i))))
           s3 (PACKep_h p)) ==>
       (eval_strexp_h (APPstrexp_h longfunid strexp_h) 
                      s1 B s3 (PACKep_h p))) /\

(* Rule 163 *)

    (!B E E' moddec_h strexp_h s1 s2 s3.
       (eval_moddec_h moddec_h s1 B s2 (ENVep_h E)) /\
       (eval_strexp_h strexp_h s2 
                      (add_env_h_to_basis_h B E) s3 (ENVep_h E')) ==>
       (eval_strexp_h (LETstrexp_h moddec_h strexp_h) s1 B s3 (ENVep_h E'))) /\

    (!B p moddec_h strexp_h s1 s2.
       (eval_moddec_h moddec_h s1 B s2 (PACKep_h p)) ==>
       (eval_strexp_h (LETstrexp_h moddec_h strexp_h) s1 B s2 (PACKep_h p))) /\

    (!B E p moddec_h strexp_h s1 s2 s3.
       (eval_moddec_h moddec_h s1 B s2 (ENVep_h E)) /\
       (eval_strexp_h strexp_h s2 
           (add_env_h_to_basis_h B E) s3 (PACKep_h p)) ==>
       (eval_strexp_h (LETstrexp_h moddec_h strexp_h) s1 B s3 (PACKep_h p))) /\

(* Structure Declarations     B |- moddec_h => E/p *)

(* Rule 164 *)
 (* different - need to cut env_h to env, and later inject env into env_h *)
 
    (!B E' dec s1 s2.
       (eval_dec dec s1 (cut_env_h_to_env (env_h_of_basis_h B))
                 s2 (ENVep E')) ==>
       (eval_moddec_h (DECmoddec_h dec) s1 B s2
                      (ENVep_h (env_in_env_h E')))) /\

    (!B dec p s1 s2.
       (eval_dec dec s1 (cut_env_h_to_env (env_h_of_basis_h B))
                 s2 (PACKep p)) ==>
       (eval_moddec_h (DECmoddec_h dec) s1 B s2 (PACKep_h p))) /\


(* Rule 165 *)
    (!B SE strbind_h s1 s2.
       (eval_strbind_h strbind_h s1 B s2 (STRENVsp_h SE)) ==>
       (eval_moddec_h (STRUCTUREmoddec_h strbind_h) s1 B s2 
                               (ENVep_h (strenv_h_in_env_h SE)))) /\

    (!B p strbind_h s1 s2.
       (eval_strbind_h strbind_h s1 B s2 (PACKsp_h p)) ==>
       (eval_moddec_h (STRUCTUREmoddec_h strbind_h) s1 B s2 (PACKep_h p))) /\

(* Rule 166 *)

    (!B E1 E2 moddec_h1 moddec_h2 s1 s2 s3.
       (eval_moddec_h moddec_h1 s1 B s2 (ENVep_h E1)) /\
       (eval_moddec_h moddec_h2 s2 
                      (add_env_h_to_basis_h B E1) s3 (ENVep_h E2)) ==>
       (eval_moddec_h (LOCALmoddec_h moddec_h1 moddec_h2) s1 B s3
                      (ENVep_h E2))) /\

    (!B p moddec_h1 moddec_h2 s1 s2.
       (eval_moddec_h moddec_h1 s1 B s2 (PACKep_h p)) ==>
       (eval_moddec_h (LOCALmoddec_h moddec_h1 moddec_h2) s1 B s2 
                      (PACKep_h p))) /\

    (!B E p moddec_h1 moddec_h2 s1 s2 s3.
       (eval_moddec_h moddec_h1 s1 B s2 (ENVep_h E)) /\
       (eval_moddec_h moddec_h2 s2 (add_env_h_to_basis_h B E) s3 
                      (PACKep_h p)) ==>
       (eval_moddec_h (LOCALmoddec_h moddec_h1 moddec_h2) s1 B s3 
                      (PACKep_h p))) /\

(* Rule 132mod *) (* Extended from dec to moddec_h *)
(*
          B(longstrid_1) = E1 ... B(longstrid_n) = En
  -------------------------------------------------------
   B |- open longstrid_1 ... longstrid_n => E1 + ... + En
*)

    (!B E_1_n longstrid_1_n s:state.
     (nonempty_MAP (lookup_longstrid_basis_h B) longstrid_1_n = 
      nonempty_MAP lift E_1_n) ==>
     eval_moddec_h (OPENmoddec_h longstrid_1_n) s B s
              (ENVep_h (nonempty_FOLDL_WITH_INIT add_env_h E_1_n))) /\

(* Rule 167 *)
    (!B s. eval_moddec_h EMPTYmoddec_h s B s (ENVep_h empty_env_h)) /\

(* Rule 168 *)
    (!B E1 E2 moddec_h1 moddec_h2 s1 s2 s3.
       (eval_moddec_h moddec_h1 s1 B s2 (ENVep_h E1)) /\
       (eval_moddec_h moddec_h2 s2 (add_env_h_to_basis_h B E1) s3 
                      (ENVep_h E2)) ==>
       (eval_moddec_h (SEQmoddec_h moddec_h1 moddec_h2)
                      s1 B s3 (ENVep_h (add_env_h E1 E2)))) /\

    (!B p moddec_h1 moddec_h2 s1 s2.
       (eval_moddec_h moddec_h1 s1 B s2 (PACKep_h p)) ==>
       (eval_moddec_h (SEQmoddec_h moddec_h1 moddec_h2) s1 B s2 
                      (PACKep_h p))) /\

    (!B E p moddec_h1 moddec_h2 s1 s2 s3.
       (eval_moddec_h moddec_h1 s1 B s2 (ENVep_h E)) /\
       (eval_moddec_h moddec_h2 s2 (add_env_h_to_basis_h B E) s3 
                      (PACKep_h p)) ==>
       (eval_moddec_h (SEQmoddec_h moddec_h1 moddec_h2) s1 B s3 
                      (PACKep_h p))) /\

(* New rule (C) *)
(* Rule 188 *)
    (!B f funbind_h s1 s2.
       (eval_funbind_h funbind_h s1 B s2 f) ==>
       (eval_moddec_h 
           (FUNCTORmoddec_h funbind_h) s1 B s2 
           (ENVep_h (funenv_h_in_env_h f)))) /\


(* Structure Bindings     B |- strbind_h => SE/p *)

(* Rule 169a *)
    (!B E strexp_h strid s1 s2.
       (eval_strexp_h strexp_h s1 B s2 (ENVep_h E)) ==>
       (eval_strbind_h (BINDstrbind_h strid NONE strexp_h NONE) s1 B 
                       s2 (STRENVsp_h (strenv_h_map strid E)))) /\

    (!B p strexp_h strid s1 s2.
       (eval_strexp_h strexp_h s1 B s2 (PACKep_h p)) ==>
       (eval_strbind_h (BINDstrbind_h strid NONE strexp_h NONE) s1 B s2 (PACKsp_h p))) /\

(* Rule 169b *) 
    (!B E i sigexp_h strexp_h strid s1 s2 s3.
       (eval_strexp_h strexp_h s1 B s2 (ENVep_h E)) /\
       (eval_sigexp_h sigexp_h s2 (Inter_basis_h B) s3 i) ==>
       (eval_strbind_h (BINDstrbind_h strid (SOME sigexp_h) strexp_h NONE) s1 B
                      s3 (STRENVsp_h (strenv_h_map strid (cut_env_h E i))))) /\

    (!B p sigexp_h strexp_h strid s1 s2.
       (eval_strexp_h strexp_h s1 B s2 (PACKep_h p)) ==>
       (eval_strbind_h 
         (BINDstrbind_h strid (SOME sigexp_h) strexp_h NONE) s1 B s2 (PACKsp_h p))) /\
    
(* Rule 169c *)
    (!B E SE strbind_h strexp_h strid s1 s2 s3.
       (eval_strexp_h strexp_h s1 B s2 (ENVep_h E)) /\
       (eval_strbind_h strbind_h s2 B s3 (STRENVsp_h SE)) ==>
       (eval_strbind_h (BINDstrbind_h strid NONE strexp_h (SOME strbind_h)) s1 B s3
           (STRENVsp_h (add_strenv_h (strenv_h_map strid E) SE)))) /\

    (!B p strbind_h strexp_h strid s1 s2.
       (eval_strexp_h strexp_h s1 B s2 (PACKep_h p)) ==>
       (eval_strbind_h 
           (BINDstrbind_h strid NONE strexp_h (SOME strbind_h)) s1 B s2 (PACKsp_h p))) /\


    (!B E p strbind_h strexp_h  strid s1 s2 s3.
       (eval_strexp_h strexp_h s1 B s2 (ENVep_h E)) /\
       (eval_strbind_h strbind_h s2 B s3 (PACKsp_h p)) ==>
       (eval_strbind_h 
           (BINDstrbind_h strid NONE strexp_h (SOME strbind_h)) s1 B s3 (PACKsp_h p))) /\

(* Rule 169d *)
   (!B E i SE sigexp_h strbind_h strexp_h strid s1 s2 s3 s4.
       (eval_strexp_h strexp_h s1 B s2 (ENVep_h E)) /\
       (eval_sigexp_h sigexp_h s2 (Inter_basis_h B) s3 i) /\
       (eval_strbind_h strbind_h s3 B s4 (STRENVsp_h SE)) ==>
       (eval_strbind_h 
             (BINDstrbind_h strid (SOME sigexp_h) strexp_h (SOME strbind_h)) s1 B 
             s4 (STRENVsp_h (add_strenv_h 
                                (strenv_h_map strid (cut_env_h E i)) SE)))) /\

   (!B p sigexp_h strbind_h strexp_h strid s1 s2. 
       (eval_strexp_h strexp_h s1 B s2 (PACKep_h p)) ==>
       (eval_strbind_h 
            (BINDstrbind_h strid (SOME sigexp_h) strexp_h (SOME strbind_h)) s1 B
            s2 (PACKsp_h p))) /\

   (!B E i p sigexp_h strbind_h strexp_h strid s1 s2 s3 s4.
       (eval_strexp_h strexp_h s1 B s2 (ENVep_h E)) /\
       (eval_sigexp_h sigexp_h s2 (Inter_basis_h B) s3 i) /\
       (eval_strbind_h strbind_h s3 B s4 (PACKsp_h p)) ==>
       (eval_strbind_h 
            (BINDstrbind_h strid (SOME sigexp_h) strexp_h (SOME strbind_h)) s1 B 
            s4 (PACKsp_h p))) /\

(* Functor Bindings     B |- funbind_h => F *)

(* Rule 187a *)

   (!B funid i sigexp_h strexp_h strid s1 s2.
       (eval_sigexp_h sigexp_h s1 (Inter_basis_h B) s2 i) ==>
       (eval_funbind_h
	    (BINDfunbind_h funid strid sigexp_h NONE strexp_h NONE) s1 B s2
            (funenv_h_map funid (FUNCLOS_H strid i strexp_h NONE B)))) /\ 

(* Rule 187b *)

   (!B funid i i' sigexp_h sigexp_h' strexp_h strid s1 s2 s3.
       (eval_sigexp_h sigexp_h s1 (Inter_basis_h B) s2 i) /\
       (eval_sigexp_h sigexp_h' s2
             (add_strintenv_h_to_intbasis_h 
                  (Inter_basis_h B) (strintenv_h_map strid i)) 
             s3 i') ==>
       (eval_funbind_h 
          (BINDfunbind_h funid strid sigexp_h (SOME sigexp_h') strexp_h NONE)
	  s1 B s3
          (funenv_h_map funid (FUNCLOS_H strid i strexp_h (SOME i') B)))) /\

(* Rule 187c *)

   (!B funbind_h funid f i sigexp_h strexp_h strid s1 s2 s3.
       (eval_sigexp_h sigexp_h s1 (Inter_basis_h B) s2 i) /\
       (eval_funbind_h funbind_h s2 B s3 f) ==>
       (eval_funbind_h 
         (BINDfunbind_h funid strid sigexp_h NONE strexp_h (SOME funbind_h))
	 s1 B s3 (add_funenv_h
                        (funenv_h_map funid 
			   (FUNCLOS_H strid i strexp_h NONE B))
			f))) /\


(* Rule 187d *)

   (!B funbind_h funid f i i' sigexp_h sigexp_h' strexp_h strid s1 s2 s3 s4.
       (eval_sigexp_h sigexp_h s1 (Inter_basis_h B) s2 i) /\
       (eval_sigexp_h sigexp_h' s2 (add_strintenv_h_to_intbasis_h 
                                       (Inter_basis_h B)
                                       (strintenv_h_map strid i))
            s3 i') /\
       (eval_funbind_h funbind_h s3 B s4 f) ==>
       (eval_funbind_h 
           (BINDfunbind_h funid strid sigexp_h (SOME sigexp_h') strexp_h
	       (SOME funbind_h))
            s1 B s4
            (add_funenv_h
                (funenv_h_map funid (FUNCLOS_H strid i strexp_h (SOME i') B))
                f))) /\

(* New Rule (E) *)

   (!B funclos_h funid longfunid s. 
       (lookup_longfunid_basis_h B longfunid = lift funclos_h) ==>
       (eval_funbind_h 
           (REBINDfunbind_h funid longfunid) s B s 
               (funenv_h_map funid funclos_h)))`--;


val HOFML_eval_structures_pred_DEF = new_definition
("HOFML_eval_structures_pred_DEF", HOFML_eval_structures_pred_def);
  
val eval_strexp_h_DEF = new_definition
("eval_strexp_h_DEF",
--`eval_strexp_h strexp_h s1 B s2 ep =
   !poss_eval_strexp_h poss_eval_moddec_h 
    poss_eval_strbind_h poss_eval_funbind_h.
   HOFML_eval_structures_pred
       poss_eval_strexp_h poss_eval_moddec_h 
       poss_eval_strbind_h poss_eval_funbind_h ==>
   poss_eval_strexp_h strexp_h s1 B s2 ep`--);

val eval_moddec_h_DEF = new_definition
("eval_moddec_h_DEF",
--`eval_moddec_h moddec_h s1 B s2 ep =
   !poss_eval_strexp_h poss_eval_moddec_h 
   poss_eval_strbind_h poss_eval_funbind_h.
   HOFML_eval_structures_pred 
       poss_eval_strexp_h poss_eval_moddec_h 
       poss_eval_strbind_h poss_eval_funbind_h ==>
   poss_eval_moddec_h moddec_h s1 B s2 ep`--);

val eval_strbind_h_DEF = new_definition
("eval_strbind_h_DEF",
--`eval_strbind_h strbind_h s1 B s2 sep =
   !poss_eval_strexp_h poss_eval_moddec_h 
    poss_eval_strbind_h poss_eval_funbind_h.
   HOFML_eval_structures_pred 
       poss_eval_strexp_h poss_eval_moddec_h 
       poss_eval_strbind_h  poss_eval_funbind_h ==>
   poss_eval_strbind_h strbind_h s1 B s2 sep`--);

val eval_funbind_h_DEF = new_definition
("eval_funbind_h_DEF",
--`eval_funbind_h funbind_h s1 B s2 fe =
   !poss_eval_strexp_h poss_eval_moddec_h 
    poss_eval_strbind_h poss_eval_funbind_h.
   HOFML_eval_structures_pred 
       poss_eval_strexp_h poss_eval_moddec_h 
       poss_eval_strbind_h  poss_eval_funbind_h ==>
   poss_eval_funbind_h funbind_h s1 B s2 fe`--);


val HOFML_EVAL_STRUCT_RULES_SATISFIED =
store_thm("HOFML_EVAL_STRUCT_RULES_SATISFIED",
(--`HOFML_eval_structures_pred
       eval_strexp_h eval_moddec_h eval_strbind_h eval_funbind_h`--),
EVAL_RULE_TAC [HOFML_eval_structures_pred_DEF,
eval_strexp_h_DEF,eval_moddec_h_DEF,eval_strbind_h_DEF,eval_funbind_h_DEF]);


val HOFML_eval_structures_induction =
save_thm("HOFML_eval_structures_induction",
PURE_ONCE_REWRITE_RULE[HOFML_eval_structures_pred_DEF]
(prove
((--`!P_strexp_h P_moddec_h P_strbind_h P_funbind_h.
HOFML_eval_structures_pred P_strexp_h P_moddec_h P_strbind_h P_funbind_h ==>
((!strexp_h s1 B s2 ep. eval_strexp_h strexp_h s1 B s2 ep ==>
                        P_strexp_h strexp_h s1 B s2 ep) /\
 (!moddec_h s1 B s2 ep. eval_moddec_h moddec_h s1 B s2 ep ==>
                        P_moddec_h moddec_h s1 B s2 ep) /\
 (!strbind_h s1 B s2 sep. eval_strbind_h strbind_h s1 B s2 sep ==>
                          P_strbind_h strbind_h s1 B s2 sep) /\
 (!funbind_h s1 B s2 fe. eval_funbind_h funbind_h s1 B s2 fe ==>
                         P_funbind_h funbind_h s1 B s2 fe))`--),
PURE_REWRITE_TAC[eval_strexp_h_DEF,eval_moddec_h_DEF,
		 eval_strbind_h_DEF,eval_funbind_h_DEF] THEN
REPEAT STRIP_TAC THEN RES_TAC)));


(* Top-level Declarations      B |- topdec_h => B'/p *)

val {desc, induction_thm} = new_inductive_definition
{name = "eval_topdec_h_DEF",
 fixity = Prefix,
 patt = ((--`(eval_topdec_h (topdec_h:topdec_h) (s1:state) (B:basis_h) 
                (s2:state) (bp:basis_pack_h)):bool`--),[]),
 rules = [

(* Rule 191 *)
{hypotheses = [],
 side_conditions = 
[(--`(eval_moddec_h (moddec_h:moddec_h) (s1:state) (B:basis_h)
                           (s2:state) (ENVep_h (E:env_h))):bool`--)],
 conclusion = 
(--`(eval_topdec_h (MODDEC_H (moddec_h:moddec_h)) (s1:state) (B:basis_h) 
               (s2:state) (BASISbp_h (env_h_in_basis_h (E:env_h)))):bool`--)},

{hypotheses = [],
 side_conditions = 
[(--`(eval_moddec_h (moddec_h:moddec_h) (s1:state) (B:basis_h)
                           (s2:state) (PACKep_h (p:pack))):bool`--)],
 conclusion = 
(--`(eval_topdec_h (MODDEC_H (moddec_h:moddec_h)) (s1:state) (B:basis_h) 
                     (s2:state) (PACKbp_h (p:pack))):bool`--)},

(* Rule 192 *)
{hypotheses = [],
 side_conditions = 
[(--`(eval_sigdec_h (sigdec_h:sigdec_h) (s1:state) 
           (Inter_basis_h (B:basis_h)) (s2:state) (G:sigenv_h)):bool`--)],
 conclusion = 
(--`(eval_topdec_h (SIGDEC_H (sigdec_h:sigdec_h)) (s1:state) (B:basis_h)
          (s2:state) (BASISbp_h (sigenv_h_in_basis_h (G:sigenv_h)))):bool`--)}
]};


val [Rule191a_h,Rule191b_h,Rule192_h] =
    map save_thm (zip ["Rule191a_h","Rule191b_h","Rule192_h"] desc);
val eval_topdec_h_induction_thm =
    save_thm ("eval_topdec_h_induction_thm",induction_thm);

