Hol90.ppOn();
open Hol90;
infix THEN THENL ##;
open RW;
val Term = Parse.term_parser;
open arithLib.Arith;


new_theory"kls_list";
open Rewrite;
use"Q.sig";use"Q.sml";

val _ = add_theory_to_sml"list";

val mem_def = new_recursive_definition
  {def = --`(mem (x:'a) [] = F) /\ (mem x (CONS y L) = (x=y) \/ mem x L)`--,
   fixity = Prefix,
   name = "mem_def",
   rec_axiom = theorem "list" "list_Axiom"};


val filter_def = new_recursive_definition
  {name = "filter_def",
   def = --`(filter P [] = []) /\
          (filter P (CONS x L) = (P x => CONS x (filter P L) | filter P L))`--,
   rec_axiom = theorem"list" "list_Axiom",
   fixity = Prefix};


val append_infix = new_infix_definition("append_infix",
 --`$++ :'a list -> 'a list -> 'a list = APPEND`--, 500);

val LIST_INDUCT_TAC = INDUCT_THEN (theorem "list" "list_INDUCT") ASSUME_TAC;

val mem_filter = Q.store_thm("mem_filter",
`!P L (x:'a). mem x (filter P L) = P x /\ mem x L`,
GEN_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[mem_def,filter_def] THEN
 REPEAT GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[mem_def] THEN
 EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN POP_ASSUM SUBST_ALL_TAC
 THEN RES_TAC);


val mem_filter_lemma = Q.store_thm("mem_filter_lemma",
`!P L (x:'a). mem x L = mem x (filter P L) \/ mem x (filter ($~ o P) L)`,
REWRITE_TAC[mem_filter,definition"combin" "o_DEF"] THEN BETA_TAC THEN
 REPEAT GEN_TAC THEN EQ_TAC THEN STRIP_TAC THEN 
 ASM_REWRITE_TAC[REWRITE_RULE[] boolThry.BOOL_CASES_AX]);

val length_filter = Q.store_thm("length_filter",
`!L (P:'a->bool). LENGTH (filter P L) <= (LENGTH L)`,
LIST_INDUCT_TAC THEN REWRITE_TAC[definition"list" "LENGTH", filter_def]
 THENL
 [ MATCH_ACCEPT_TAC(theorem"arithmetic" "LESS_EQ_REFL"),
   REPEAT GEN_TAC THEN COND_CASES_TAC
   THENL
   [ASM_REWRITE_TAC[definition "list" "LENGTH",
               theorem"arithmetic" "LESS_EQ_MONO"],
    MATCH_MP_TAC (theorem "arithmetic" "LESS_IMP_LESS_OR_EQ") THEN
    MATCH_MP_TAC (theorem "arithmetic" "LESS_EQ_LESS_TRANS") THEN 
    Q.EXISTS_TAC`LENGTH (L:'a list)` THEN
    ASM_REWRITE_TAC[theorem"prim_rec" "LESS_SUC_REFL"]]]);


val length_filter_subset = Q.store_thm("length_filter_subset",
`(!y. P y ==> Q y) ==> !L:'a list. LENGTH(filter P L) <= LENGTH (filter Q L)`,
DISCH_TAC THEN LIST_INDUCT_TAC THENL
[ REWRITE_TAC[LENGTH,filter_def,theorem"arithmetic" "ZERO_LESS_EQ"],
  GEN_TAC THEN REWRITE_TAC[filter_def,LENGTH] THEN 
  REPEAT COND_CASES_TAC THEN RES_TAC THEN REWRITE_TAC[LENGTH] THENL
  [REWRITE_TAC[theorem"arithmetic" "LESS_EQ_MONO"] THEN 
   FIRST_ASSUM MATCH_ACCEPT_TAC,
   RES_TAC,
   MATCH_MP_TAC (theorem"arithmetic" "LESS_EQ_TRANS") THEN 
   Q.EXISTS_TAC`LENGTH(filter Q (L:'a list))`
   THEN ASM_REWRITE_TAC[theorem"arithmetic" "LESS_EQ_SUC_REFL"],
   FIRST_ASSUM ACCEPT_TAC]]);


val length_filter_stable = Q.store_thm("length_filter_stable",
`!L (P:'a->bool). (LENGTH(filter P L) = LENGTH L) ==> (filter P L = L)`,
LIST_INDUCT_TAC THEN RW_TAC[filter_def]
  THEN REPEAT GEN_TAC 
  THEN COND_CASES_TAC THEN RW_TAC[LENGTH]
  THEN ASM_RW_TAC[]
  THEN DISCH_THEN (ASSUME_TAC
         o MATCH_MP(EQT_ELIM(ARITH_CONV(Term`(x=SUC y) ==> y<x`))))
  THEN ASSUME_TAC (SPEC_ALL length_filter) 
  THEN IMP_RES_TAC(EQT_ELIM(ARITH_CONV(Term`(x < y) ==> y<=x ==> F`))));

val mem_of_append = Q.store_thm("mem_of_append",
`!(y:'a) L M. mem y (APPEND L M) = mem y L \/ mem y M`,
GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[APPEND,mem_def] THEN
 REPEAT GEN_TAC THEN ASM_REWRITE_TAC[] THEN REWRITE_TAC[DISJ_ASSOC]);

val APPEND = save_thm("APPEND",
CONJ (Q.prove`!L:'a list. APPEND L [] = L`
             (LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[definition"list" "APPEND"]))
     (definition"list" "APPEND"));


val filter_append_distrib = Q.store_thm("filter_append_distrib",
`!P L (M:'a list). filter P (APPEND L M) = APPEND (filter P L) (filter P M)`,
GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[APPEND,filter_def] THEN
REPEAT GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[APPEND]);


val length_append_comm = Q.store_thm("length_append_comm",
`!L (M:'a list). LENGTH (APPEND L M) = LENGTH (APPEND M L)`,
LIST_INDUCT_TAC THEN 
REWRITE_TAC[APPEND,LENGTH,theorem"arithmetic" "ADD_CLAUSES"] THEN 
GEN_TAC THEN LIST_INDUCT_TAC THEN 
REWRITE_TAC[APPEND,LENGTH,theorem"arithmetic" "ADD_CLAUSES", 
            theorem"prim_rec" "INV_SUC_EQ"] THEN 
POP_ASSUM (SUBST1_TAC o SYM) THEN 
ASM_REWRITE_TAC[APPEND,LENGTH,theorem"prim_rec" "INV_SUC_EQ"]);


val length_append_distrib = Q.store_thm("length_append_distrib",
`!L (M:'a list). LENGTH (APPEND L M) = LENGTH L + LENGTH M`,
LIST_INDUCT_TAC THEN 
REWRITE_TAC[APPEND,LENGTH,theorem"arithmetic" "ADD_CLAUSES",
            theorem"prim_rec" "INV_SUC_EQ"] THEN
GEN_TAC THEN POP_ASSUM (SUBST1_TAC o SYM o SPEC_ALL) THEN REFL_TAC);


val append_induction = Q.store_thm("append_induction",
`!P:'a list->bool. 
    P [] /\ 
   (!x.P[x]) /\ 
   (!L1 L2. P L1 /\ P L2 ==> P (APPEND L1 L2)) 
   ==> !L. P L`,
GEN_TAC THEN STRIP_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[] THEN 
ONCE_REWRITE_TAC[Q.prove`CONS h L = APPEND [h] L`(REWRITE_TAC[APPEND])]
THEN GEN_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);


(* The standard HOL version gets "h" and "t" in the reverse order. *)
val list_CASES' = Q.store_thm("list_CASES'",
`!l:'a list. (l=[]) \/ ?h t. l = CONS h t`,
GEN_TAC THEN STRIP_ASSUME_TAC (SPEC_ALL list_CASES) THEN POP_ASSUM SUBST1_TAC
 THENL[ALL_TAC, DISJ2_TAC THEN MAP_EVERY Q.EXISTS_TAC[`h`, `t`]]
 THEN REWRITE_TAC[]);

val length_append_filter = Q.store_thm("length_append_filter",
`!L:'a list. LENGTH L = LENGTH (APPEND (filter P L) (filter (~ o P) L))`,
LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[LENGTH,filter_def,APPEND,
 length_append_distrib,definition"combin" "o_DEF", 
 theorem"arithmetic" "ADD_CLAUSES"] THEN BETA_TAC
 THEN GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[LENGTH] THEN 
 REWRITE_TAC[theorem"arithmetic" "ADD_CLAUSES"]);

val filters_compose = Q.store_thm("filters_compose",
`!P Q (L:'a list). 
    filter P (filter Q L) = filter (\x. P x /\ Q x) L`,
GEN_TAC THEN GEN_TAC THEN 
 INDUCT_THEN (theorem "list" "list_INDUCT") MP_TAC THEN REWRITE_TAC[filter_def]
 THEN DISCH_TAC THEN GEN_TAC THEN BETA_TAC THEN REPEAT COND_CASES_TAC 
 THEN RULE_ASSUM_TAC (REWRITE_RULE[]) THEN REWRITE_TAC[filter_def]
 THENL[ ASM_REWRITE_TAC[], ASM_REWRITE_TAC[],
        IMP_RES_THEN MATCH_ACCEPT_TAC (Q.TAUT_CONV`F ==> ANYTHING`),
        ONCE_ASM_REWRITE_TAC[] THEN REWRITE_TAC[]]);

val filters_commute = Q.store_thm("filters_commute",
`!P Q (L:'a list). filter P (filter Q L) = filter Q (filter P L)`,
GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[filter_def] THEN
GEN_TAC THEN REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[filter_def]);

(*---------------------------------------------------------------------------
 * membership and append
 *---------------------------------------------------------------------------*)
Q.store_thm("mem_append_eq1",
 `!l1 l2 h x. mem x (CONS h (APPEND l1 l2)) = mem x (APPEND (CONS h l1) l2)`,
LIST_INDUCT_TAC THEN RW_TAC[APPEND]);

Q.store_thm("mem_append_eq2",
`!l1 l2 h (x:'a). mem x (APPEND (CONS h l1) l2)
                = mem x (APPEND l1 (CONS h l2))`,
LIST_INDUCT_TAC 
 THEN RW_TAC[APPEND,mem_def,mem_of_append]
 THEN REPEAT STRIP_TAC
 THEN MATCH_ACCEPT_TAC (Q.TAUT_CONV`(A \/ B \/ C) \/ D = (B \/ C) \/ A \/ D`));

html_theory"-";
export_theory();
