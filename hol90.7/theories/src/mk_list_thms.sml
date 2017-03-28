(* ===================================================================== *)
(* FILE          : mk_list_thms.sml                                      *)
(* DESCRIPTION   : Theorems about lists. Translated from hol88.          *)
(*                                                                       *)
(* AUTHOR        : (c) Tom Melham, University of Cambridge               *)
(* DATE          : 86.11.24                                              *)
(* TRANSLATOR    : Konrad Slind, University of Calgary                   *)
(* DATE          : September 15, 1991                                    *)
(* ===================================================================== *)


(* Create the theory							*)
load_theory "arithmetic";
extend_theory "list";

(* fetch the axiom for lists.						*)
val list_Axiom = theorem "list" "list_Axiom";

(* Fetch a few theorems from prim_rec.th				*)

val num_Axiom = theorem "prim_rec" "num_Axiom";
val NOT_LESS_0 = theorem "prim_rec" "NOT_LESS_0";
val LESS_0 = theorem "prim_rec" "LESS_0";
val LESS_MONO = theorem "prim_rec" "LESS_MONO";
val INV_SUC_EQ = theorem "prim_rec" "INV_SUC_EQ";

(* Fetch a few things from arithmetic.th				*)

val ADD_CLAUSES = theorem "arithmetic" "ADD_CLAUSES";
val LESS_MONO_EQ = theorem "arithmetic" "LESS_MONO_EQ";
val ADD_EQ_0 = theorem "arithmetic" "ADD_EQ_0";


val INV_SUC = theorem "num" "INV_SUC";
val NOT_SUC = theorem "num" "NOT_SUC";


val NULL_DEF = new_recursive_definition
      {name = "NULL_DEF",
       fixity = Prefix,
       rec_axiom = list_Axiom,
       def = --`(NULL (NIL:'a list) = T) /\ 
                (NULL (CONS (h:'a) t) = F)`--};

val HD = new_recursive_definition
      {name = "HD",
       fixity = Prefix,
       rec_axiom = list_Axiom,
       def = --`HD (CONS (h:'a) t) = h`--};

val TL = new_recursive_definition
      {name = "TL",
       fixity = Prefix,
       rec_axiom = list_Axiom,
       def = --`TL (CONS (h:'a) t) = t`--};

val SUM = new_recursive_definition
      {name = "SUM",
       fixity = Prefix,
       rec_axiom =  list_Axiom,
       def = --`(SUM NIL = 0) /\ 
                (!h t. SUM (CONS h t) = h + (SUM t))`--};

val APPEND = new_recursive_definition
      {name = "APPEND",
       fixity = Prefix,
       rec_axiom = list_Axiom,
       def = --`(!l:'a list. APPEND NIL l = l) /\
                (!l1 l2 h. APPEND (CONS h l1) l2 = CONS h (APPEND l1 l2))`--};

val FLAT = new_recursive_definition
      {name = "FLAT",
       fixity = Prefix,
       rec_axiom = list_Axiom,
       def = --`(FLAT NIL = (NIL:'a list)) /\
                (!h t. FLAT (CONS h t) = APPEND h (FLAT t))`--};

val LENGTH = new_recursive_definition
      {name = "LENGTH",
       fixity = Prefix,
       rec_axiom = list_Axiom,
       def = --`(LENGTH NIL = 0) /\
                (!(h:'a). !t. LENGTH (CONS h t) = SUC (LENGTH t))`--};

val MAP = new_recursive_definition
      {name = "MAP",
       fixity = Prefix,
       rec_axiom = list_Axiom,
       def = --`(!f. MAP f NIL = NIL) /\
                (!f h t. MAP f (CONS (h:'a) t) = CONS (f h:'b) (MAP f t))`--};

(* ---------------------------------------------------------------------*)
(* Definition of a function 						*)
(*									*)
(*   MAP2 : ('a -> 'b -> 'c) -> 'a list ->  'b list ->  'c list		*)
(* 									*)
(*for mapping a curried binary function down a pair of lists:		*)
(* 									*)
(* |- (!f. MAP2 f[][] = []) /\						*)
(*   (!f h1 t1 h2 t2.							*)
(*      MAP2 f(CONS h1 t1)(CONS h2 t2) = CONS(f h1 h2)(MAP2 f t1 t2))	*)
(* 									*)
(* [TFM 92.04.21]							*)
(* ---------------------------------------------------------------------*)

val MAP2 =
  let val lemma = prove
     (--`?fn. 
         (!f:'a -> 'b -> 'c. fn f [] [] = []) /\
         (!f h1 t1 h2 t2.
           fn f (CONS h1 t1) (CONS h2 t2) = CONS (f h1 h2) (fn f t1 t2))`--,
      let val th = prove_rec_fn_exists list_Axiom
           (--`(fn (f:'a -> 'b -> 'c) [] l = []) /\
               (fn f (CONS h t) l = CONS (f h (HD l)) (fn f t (TL l)))`--)
      in
      STRIP_ASSUME_TAC th THEN
      EXISTS_TAC (--`fn:('a -> 'b -> 'c) -> 'a list -> 'b list -> 'c list`--)
      THEN ASM_REWRITE_TAC [HD,TL]
      end)
  in
  new_specification{name = "MAP2", sat_thm = lemma, 
                    consts = [{const_name="MAP2", fixity=Prefix}]}
  end

val EL = new_recursive_definition
      {name = "EL",
       fixity = Prefix, 
       rec_axiom = num_Axiom,
       def = --`(!l. EL 0 l = (HD l:'a)) /\ 
                (!l:'a list. !n. EL (SUC n) l = EL n (TL l))`--};

val EVERY_DEF = new_recursive_definition
      {name = "EVERY_DEF",
       fixity = Prefix, 
       rec_axiom = list_Axiom,
       def = --`(!P:'a->bool. EVERY P NIL = T)  /\
                (!P h t. EVERY P (CONS h t) = (P h /\ EVERY P t))`--};

close_theory();

(* ---------------------------------------------------------------------*)
(* Proofs of some theorems about lists.					*)
(* ---------------------------------------------------------------------*)

val NULL = store_thm ("NULL",
 --`NULL (NIL :'a list) /\ (!h t. ~NULL(CONS (h:'a) t))`--,
   REWRITE_TAC [NULL_DEF]);

(* List induction							*)
(* |- P NIL /\ (!t. P t ==> !h. P(CONS h t)) ==> (!x.P x) 		*)
val list_INDUCT = save_thm("list_INDUCT",prove_induction_thm list_Axiom);

(* Create a tactic.							*)
val LIST_INDUCT_TAC = INDUCT_THEN list_INDUCT ASSUME_TAC;

(* Cases theorem: |- !l. (l = []) \/ (?t h. l = CONS h t)		*)
val list_CASES = save_thm("list_CASES",
   Rec_type_support.prove_cases_thm list_INDUCT);

(* CONS11:  |- !h t h' t'. (CONS h t = CONS h' t') = (h = h') /\ (t = t') *)
val CONS_11 = save_thm("CONS_11",
   Rec_type_support.prove_constructors_one_one list_Axiom);

val NOT_NIL_CONS = save_thm("NOT_NIL_CONS",
   Rec_type_support.prove_constructors_distinct list_Axiom);

val NOT_CONS_NIL = save_thm("NOT_CONS_NIL",
   CONV_RULE(ONCE_DEPTH_CONV SYM_CONV) NOT_NIL_CONS);

val LIST_NOT_EQ = store_thm("LIST_NOT_EQ",
 --`!l1 l2. ~(l1 = l2) ==> !h1:'a. !h2. ~(CONS h1 l1 = CONS h2 l2)`--,
   REPEAT GEN_TAC THEN
   STRIP_TAC THEN
   ASM_REWRITE_TAC [CONS_11]);

val NOT_EQ_LIST = store_thm("NOT_EQ_LIST",
 --`!h1:'a. !h2. ~(h1 = h2) ==> !l1 l2. ~(CONS h1 l1 = CONS h2 l2)`--,
    REPEAT GEN_TAC THEN
    STRIP_TAC THEN
    ASM_REWRITE_TAC [CONS_11]);

val EQ_LIST = store_thm("EQ_LIST",
 --`!h1:'a.!h2.(h1=h2) ==> !l1 l2. (l1 = l2) ==> (CONS h1 l1 = CONS h2 l2)`--,
     REPEAT STRIP_TAC THEN
     ASM_REWRITE_TAC [CONS_11]);


val CONS = store_thm   ("CONS",
  --`!l : 'a list. ~NULL l ==> (CONS (HD l) (TL l) = l)`--,
       STRIP_TAC THEN
       STRIP_ASSUME_TAC (SPEC (--`l:'a list`--) list_CASES) THEN
       POP_ASSUM SUBST1_TAC THEN
       ASM_REWRITE_TAC [HD, TL, NULL]);

val APPEND_ASSOC = store_thm ("APPEND_ASSOC",
 --`!(l1:'a list) l2 l3. 
     APPEND l1 (APPEND l2 l3) = (APPEND (APPEND l1 l2) l3)`--,
     LIST_INDUCT_TAC THEN ASM_REWRITE_TAC [APPEND]);

val LENGTH_APPEND = store_thm ("LENGTH_APPEND",
 --`!(l1:'a list) (l2:'a list). 
     LENGTH (APPEND l1 l2) = (LENGTH l1) + (LENGTH l2)`--,
     LIST_INDUCT_TAC THEN ASM_REWRITE_TAC [LENGTH, APPEND, ADD_CLAUSES]);

val MAP_APPEND = store_thm ("MAP_APPEND",
 --`!(f:'a->'b).!l1 l2. MAP f (APPEND l1 l2) = APPEND (MAP f l1) (MAP f l2)`--,
    STRIP_TAC THEN
    LIST_INDUCT_TAC THEN 
    ASM_REWRITE_TAC [MAP, APPEND]);

val LENGTH_MAP = store_thm ("LENGTH_MAP",
 --`!l. !(f:'a->'b). LENGTH (MAP f l) = LENGTH l`--,
     LIST_INDUCT_TAC THEN ASM_REWRITE_TAC [MAP, LENGTH]);

val EVERY_EL = store_thm ("EVERY_EL",
 --`!(l:'a list) P. EVERY P l = !n. (n < LENGTH l) ==> P (EL n l)`--,
      LIST_INDUCT_TAC THEN
      ASM_REWRITE_TAC [EVERY_DEF, LENGTH, NOT_LESS_0] THEN
      REPEAT STRIP_TAC THEN EQ_TAC THENL
      [STRIP_TAC THEN INDUCT_TAC THENL
       [ASM_REWRITE_TAC [EL, HD],
        ASM_REWRITE_TAC [LESS_MONO_EQ, EL, TL]],
       REPEAT STRIP_TAC THENL
       [POP_ASSUM (MP_TAC o (SPEC (--`0`--))) THEN
        REWRITE_TAC [LESS_0, EL, HD],
	POP_ASSUM ((ANTE_RES_THEN ASSUME_TAC) o (MATCH_MP LESS_MONO)) THEN
	POP_ASSUM MP_TAC THEN REWRITE_TAC [EL, TL]]]);

val EVERY_CONJ = store_thm("EVERY_CONJ",
 --`!l. EVERY (\(x:'a). (P x) /\ (Q x)) l = (EVERY P l /\ EVERY Q l)`--,
     LIST_INDUCT_TAC THEN
     ASM_REWRITE_TAC [EVERY_DEF] THEN
     CONV_TAC (DEPTH_CONV BETA_CONV) THEN
     REPEAT (STRIP_TAC ORELSE EQ_TAC) THEN
     FIRST_ASSUM ACCEPT_TAC);

val LENGTH_NIL = store_thm("LENGTH_NIL",
 --`!l:'a list. (LENGTH l = 0) = (l = NIL)`--,
      LIST_INDUCT_TAC THEN
      REWRITE_TAC [LENGTH, NOT_SUC, NOT_CONS_NIL]);

val LENGTH_CONS = store_thm("LENGTH_CONS",
 --`!l n. (LENGTH l = SUC n) = 
          ?h:'a. ?l'. (LENGTH l' = n) /\ (l = CONS h l')`--, 
    LIST_INDUCT_TAC THENL
    [REWRITE_TAC
       [LENGTH, NOT_EQ_SYM(SPEC_ALL NOT_SUC), NOT_NIL_CONS],
     REWRITE_TAC [LENGTH, INV_SUC_EQ, CONS_11] THEN
     REPEAT (STRIP_TAC ORELSE EQ_TAC) THENL
     [EXISTS_TAC (--`h:'a`--) THEN 
      EXISTS_TAC (--`l:'a list`--) THEN
      ASM_REWRITE_TAC [],
      ASM_REWRITE_TAC []]]);

val LENGTH_EQ_SUC = store_thm("LENGTH_EQ_CONS",
 --`!P:'a list->bool.
    !n:num. 
      (!l. (LENGTH l = SUC n) ==> P l) =  
      (!l. (LENGTH l = n) ==> (\l. !x:'a. P (CONS x l)) l)`--,
    CONV_TAC (ONCE_DEPTH_CONV BETA_CONV) THEN
    REPEAT GEN_TAC THEN EQ_TAC THENL
    [REPEAT STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
     ASM_REWRITE_TAC [LENGTH],
     DISCH_TAC THEN
     INDUCT_THEN list_INDUCT STRIP_ASSUME_TAC THENL
     [REWRITE_TAC [LENGTH,NOT_NIL_CONS,NOT_EQ_SYM(SPEC_ALL NOT_SUC)],
      ASM_REWRITE_TAC [LENGTH,INV_SUC_EQ,CONS_11] THEN
      REPEAT STRIP_TAC THEN RES_THEN MATCH_ACCEPT_TAC]]);

val LENGTH_EQ_NIL = store_thm("LENGTH_EQ_NIL",
 --`!P: 'a list->bool. 
    (!l. (LENGTH l = 0) ==> P l) = P []`--,
   REPEAT GEN_TAC THEN EQ_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC [LENGTH],
    DISCH_TAC THEN
    INDUCT_THEN list_INDUCT STRIP_ASSUME_TAC THENL
    [ASM_REWRITE_TAC [], ASM_REWRITE_TAC [LENGTH,NOT_SUC]]]);;

export_theory();
