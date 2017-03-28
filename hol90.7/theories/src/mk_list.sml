(* ===================================================================== *)
(* FILE          : mk_list.sml                                           *)
(* DESCRIPTION   : The logical definition of the list type operator. The *)
(*                 type is defined and the following "axiomatization" is *)
(*                 proven from the definition of the type:               *)
(*                                                                       *)
(*                    |- !x f. ?!fn. (fn NIL = x) /\                     *)
(*                                  (!h t. fn (CONS h t) = f (fn t) h t) *)
(*                                                                       *)
(*                 Translated from hol88.                                *)
(*                                                                       *)
(* AUTHOR        : (c) Tom Melham, University of Cambridge               *)
(* DATE          : 86.11.24                                              *)
(* REVISED       : 87.03.14                                              *)
(* TRANSLATOR    : Konrad Slind, University of Calgary                   *)
(* DATE          : September 15, 1991                                    *)
(* ===================================================================== *)


(* Parent is arithmetic; current theory on loading is BASIC_HOL.         *)
load_theory "arithmetic";

(* Define the new theory.        *)
new_theory "list";

(* fetch theorems from prim_rec  *)

val NOT_LESS_0 = theorem "prim_rec" "NOT_LESS_0";
val PRIM_REC_THM = theorem "prim_rec" "PRIM_REC_THM";
val PRE = theorem "prim_rec" "PRE";
val LESS_0 = theorem "prim_rec" "LESS_0";


(* Fetch theorems from num       *)

val NOT_SUC = theorem "num" "NOT_SUC";


(* Fetch theorems from arithmetic *)

val ADD_CLAUSES = theorem "arithmetic" "ADD_CLAUSES";
val LESS_ADD_1 = theorem "arithmetic" "LESS_ADD_1";
val LESS_EQ = theorem "arithmetic" "LESS_EQ";
val NOT_LESS = theorem "arithmetic" "NOT_LESS";
val LESS_EQ_ADD = theorem "arithmetic" "LESS_EQ_ADD";
val num_CASES = theorem "arithmetic" "num_CASES";
val LESS_MONO_EQ = theorem "arithmetic" "LESS_MONO_EQ";

(* Fetch a theorem from pair *)
val PAIR_EQ = theorem "pair" "PAIR_EQ";


(* Define the subset predicate for lists.				*)
val IS_list_REP = new_definition("IS_list_REP",
 --`IS_list_REP r = ?f n. r = ((\m.(m<n => (f m) | @(x:'a).T)),n)`--);

(* Show that the representation subset is nonempty.			*)
val EXISTS_list_REP = prove
  (--`?p. IS_list_REP (p:((num->'a) # num))`--,
      EXISTS_TAC (--`((\(n:num).@(e:'a).T),0)`--) THEN
      PURE_REWRITE_TAC [IS_list_REP] THEN
      MAP_EVERY EXISTS_TAC [--`\(n:num).@(e:'a).T`--, --`0`--] THEN
      REWRITE_TAC [NOT_LESS_0]);

(* Define the new type.							*)
val list_TY_DEF = new_type_definition
   {name = "list", 
    pred = --`IS_list_REP:((num->'a) # num) -> bool`--, 
    inhab_thm = EXISTS_list_REP};

(* Define a representation function, REP_list, from the type 'a list to  *)
(* the representing type and the inverse abstraction function ABS_list,  *)
(* and prove some trivial lemmas about them.                             *)
val list_ISO_DEF = define_new_type_bijections
                     {name = "list_ISO_DEF",
                      ABS = "ABS_list",
                      REP = "REP_list",
                      tyax = list_TY_DEF};

val R_ONTO = prove_rep_fn_onto list_ISO_DEF
and A_11   = prove_abs_fn_one_one list_ISO_DEF
and A_R = CONJUNCT1 list_ISO_DEF
and R_A = CONJUNCT2 list_ISO_DEF;

(* --------------------------------------------------------------------- *)
(* Definitions of NIL and CONS.						*)
(* --------------------------------------------------------------------- *)

val NIL_DEF = new_definition("NIL_DEF", 
    --`NIL = ABS_list ((\n:num. @(e:'a). T),0)`--);

val CONS_DEF =new_definition("CONS_DEF",
    --`CONS (h:'a) (t:'a list) = 
        (ABS_list ((\m. ((m=0) => h | (FST(REP_list t)) (PRE m))),
		   (SUC(SND(REP_list t)))))`--);

close_theory();

(* ---------------------------------------------------------------------*)
(* Now, prove the axiomatization of lists.				*)
(* ---------------------------------------------------------------------*)

val lemma1 = 
    TAC_PROOF(([],
    --`!x:'b. !f: 'b -> 'a -> 'a list -> 'b.
       ?fn1: (num -> 'a) # num -> 'b.
	 (!g.   fn1(g,0)   = x) /\
	 (!g n. fn1(g,n+1) = 
	        f (fn1 ((\i.g(i+1)),n)) (g 0) (ABS_list((\i.g(i+1)),n)))`--),
   REPEAT STRIP_TAC 
   THEN EXISTS_TAC 
   (--`\p:(num -> 'a)#num. 
     (PRIM_REC (\g.(x:'b)) 
	       (\b m g. f (b (\i.g(i+1))) (g 0) (ABS_list((\i.g(i+1)),m))))
     (SND p)
     (FST p)`--) 
   THEN
   CONV_TAC (DEPTH_CONV (BETA_CONV ORELSEC num_CONV)) THEN
   REWRITE_TAC [PRIM_REC_THM, ADD_CLAUSES] THEN
   CONV_TAC (DEPTH_CONV BETA_CONV) THEN
   REWRITE_TAC[]);

val NIL_lemma = 
    TAC_PROOF(([], --`REP_list NIL = ((\n:num.@x:'a.T), 0)`--),
              REWRITE_TAC [NIL_DEF, (SYM(SPEC_ALL R_A)), IS_list_REP] THEN
	      MAP_EVERY EXISTS_TAC [--`\n:num.@x:'a.T`--, --`0`--] THEN
	      REWRITE_TAC [NOT_LESS_0]);

val REP_lemma = 
    TAC_PROOF(([], --`IS_list_REP (REP_list (l: 'a list))`--),
              REWRITE_TAC [R_ONTO] THEN
	      EXISTS_TAC (--`l:'a list`--) THEN
	      REFL_TAC);

val CONS_lemma = TAC_PROOF(([], 
   --`REP_list (CONS (h:'a) t) = 
     ((\m.((m=0)=>h|FST(REP_list t)(PRE m))),SUC(SND(REP_list t)))`--),
   REWRITE_TAC [CONS_DEF, (SYM(SPEC_ALL R_A)), IS_list_REP] THEN
   EXISTS_TAC (--`\n.((n=0) => (h:'a) | (FST(REP_list t)(PRE n)))`--) THEN
   EXISTS_TAC (--`SUC(SND(REP_list (t:('a)list)))`--) THEN
   REWRITE_TAC [PAIR_EQ] THEN
   CONV_TAC (REDEPTH_CONV (FUN_EQ_CONV ORELSEC BETA_CONV)) THEN
   STRIP_TAC THEN 
   ASM_CASES_TAC (--`n < (SUC(SND(REP_list (t:('a)list))))`--) THEN
   ASM_REWRITE_TAC [] THEN
   STRIP_ASSUME_TAC (REWRITE_RULE [IS_list_REP] 
                                  (SPEC (--`t:'a list`--)
                                        (GEN_ALL REP_lemma))) THEN
   POP_ASSUM SUBST_ALL_TAC THEN
   POP_ASSUM MP_TAC THEN
   REWRITE_TAC [NOT_LESS, (SYM(SPEC_ALL LESS_EQ))] THEN
   CONV_TAC (DEPTH_CONV BETA_CONV) THEN
   DISCH_THEN ((STRIP_THM_THEN SUBST1_TAC) o MATCH_MP LESS_ADD_1) THEN
   REWRITE_TAC [num_CONV (--`1`--), PRE, ADD_CLAUSES, NOT_SUC] THEN
   REWRITE_TAC[REWRITE_RULE[SYM(SPEC_ALL NOT_LESS)] LESS_EQ_ADD]);

val exists_lemma = TAC_PROOF(([],
 --`!x:'b. !(f :'b->'a->'a list->'b).
    ?fn1:'a list->'b.
       (fn1 NIL = x) /\ 
       (!h t. fn1 (CONS h t) = f (fn1 t) h t)`--),
    REPEAT STRIP_TAC THEN
    STRIP_ASSUME_TAC (REWRITE_RULE [num_CONV (--`1`--), ADD_CLAUSES]
		   (SPECL[--`x:'b`--, --`f:'b->'a->'a list->'b`--] 
                         lemma1)) THEN
    EXISTS_TAC (--`\(x:('a)list).(fn1 (REP_list x):'b)`--) THEN
    CONV_TAC (DEPTH_CONV BETA_CONV) THEN
    ASM_REWRITE_TAC [NIL_lemma, CONS_lemma] THEN
    CONV_TAC (DEPTH_CONV BETA_CONV) THEN
    REWRITE_TAC [NOT_SUC, PRE, ETA_AX, A_R]);

val A_11_lemma = 
    REWRITE_RULE [SYM (ANTE_CONJ_CONV (--`(A /\ B) ==> C`--))]
    (DISCH_ALL(snd(EQ_IMP_RULE (UNDISCH_ALL (SPEC_ALL A_11)))));

val R_A_lemma = 
    TAC_PROOF(([],
	     --`REP_list(ABS_list((\m.((m<n) => f(SUC m) | @(x:'a).T)),n)) = 
	        ((\m.((m<n) => f(SUC m) | @(x:'a).T)),n)`--),
	     REWRITE_TAC [SYM(SPEC_ALL R_A), IS_list_REP] THEN
	     MAP_EVERY EXISTS_TAC [--`\n.f(SUC n):'a`--, --`(n:num)`--] THEN
	     CONV_TAC (DEPTH_CONV BETA_CONV) THEN
	     REFL_TAC);

val cons_lemma = TAC_PROOF(([], 
   --`ABS_list((\m.(m < SUC n) => f m | (@(x:'a).T)), (SUC n)) = 
      (CONS(f 0)(ABS_list ((\m.((m<n) => (f (SUC m)) | (@(x:'a).T))), n)))`--),
   REWRITE_TAC [CONS_DEF] THEN
   MATCH_MP_TAC (GEN_ALL A_11_lemma) THEN
   REPEAT STRIP_TAC THENL
   [REWRITE_TAC [R_ONTO] THEN
   EXISTS_TAC 
   (--`CONS (f 0)(ABS_list((\m.((m<n) => (f (SUC m))| (@(x:'a).T))),n))`--)
   THEN
   REWRITE_TAC [CONS_lemma],
   REWRITE_TAC [IS_list_REP] THEN
   MAP_EVERY EXISTS_TAC [--`(f:num->'a)`--, --`SUC n`--] THEN REFL_TAC,
   REWRITE_TAC [PAIR_EQ, R_A_lemma] THEN 
   CONV_TAC FUN_EQ_CONV THEN CONV_TAC (DEPTH_CONV BETA_CONV) THEN
   STRIP_TAC THEN
   STRIP_ASSUME_TAC (SPEC (--`(n':num)`--) num_CASES) THEN
   POP_ASSUM SUBST1_TAC THENL
   [REWRITE_TAC [PRE, LESS_0],
   REWRITE_TAC [PRE, NOT_SUC, LESS_MONO_EQ]]]);


val list_Axiom = store_thm("list_Axiom",
 --`!x:'b. 
    !f:'b -> 'a -> 'a list -> 'b.
    ?!(fn1: 'a list -> 'b).
        (fn1 NIL = x) /\
        (!h t. fn1 (CONS h t) = f (fn1 t) h t)`--,
    PURE_REWRITE_TAC [EXISTS_UNIQUE_DEF] THEN
    CONV_TAC (REDEPTH_CONV BETA_CONV) THEN
    REWRITE_TAC [exists_lemma] THEN
    REWRITE_TAC [NIL_DEF] THEN
    REPEAT STRIP_TAC THEN
    CONV_TAC FUN_EQ_CONV THEN
    CONV_TAC (ONCE_DEPTH_CONV(REWR_CONV(SYM (SPEC_ALL A_R)))) THEN
    X_GEN_TAC (--`l :'a list`--) THEN
    STRIP_ASSUME_TAC (REWRITE_RULE [IS_list_REP] 
		          (SPEC (--`l :'a list`--) 
                                (GEN_ALL REP_lemma))) THEN
    POP_ASSUM SUBST_ALL_TAC THEN
    SPEC_TAC (--`f':num->'a`--,--`f':num->'a`--) THEN
    SPEC_TAC (--`n:num`--,--`n:num`--) THEN
    INDUCT_TAC THENL
    [ASM_REWRITE_TAC [NOT_LESS_0],
     STRIP_TAC THEN
     POP_ASSUM (ASSUME_TAC o (CONV_RULE (DEPTH_CONV BETA_CONV)) o
                (SPEC (--`\n.f'(SUC n):'a`--))) THEN
     ASM_REWRITE_TAC [cons_lemma]]);

export_theory();
