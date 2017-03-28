(* A less naive version of Quicksort than that in "qsort.sml". The proofs 
 * seem to become more complicated.
 *---------------------------------------------------------------------------*)

new_theory"fqsort" handle _ => ();

cons_path "../" theory_path;
val _ = new_parent "sorting";;
val _ = new_parent "partition";;

(*---------------------------------------------------------------------------
 * Support for manipulating lets.
 *---------------------------------------------------------------------------*)
use"../utils.sml";

(* Make some abbreviations *)
val TY = ty_antiq o Parse.type_parser;
val order = TY`:'a -> 'a -> bool`;

val transitive_def = definition"TC" "transitive_def";
val tt_relation_trans = Q.prove
`!R:^order. tt_relation R ==> transitive R`
(RW_TAC[definition"sorting" "tt_relation_def",transitive_def]);


(*---------------------------------------------------------------------------
 * The quicksort algorithm
 *---------------------------------------------------------------------------*)
val fqsort_def = 
     Rfunction `measure (LENGTH o SND)`
      `(fqsort(ord:^order,[]) = []) /\
       (fqsort(ord, (x:'a)::rst) = 
           let (l1,l2) = partition((\y. ord y x), rst)
           in
           fqsort(ord,l1)++[x]++fqsort(ord,l2))`;

map add_theory_to_sml["list", "kls_list","sorting","permutation", "partition"];
val LIST_INDUCT_TAC = INDUCT_THEN (theorem "list" "list_INDUCT") MP_TAC;



(*---------------------------------------------------------------------------
 * Termination of fqsort 
 *---------------------------------------------------------------------------*)
val fqsort_terminates = save_thm("fqsort_terminates",
prove_termination fqsort_def
 (RW_TAC[partition_def,LENGTH] THEN 
  CONJ_TAC THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC (theorem"arithmetic" "LESS_EQ_IMP_LESS_SUC") THEN 
  IMP_RES_TAC part_length_lem THEN
  RULE_ASSUM_TAC (RW_RULE[LENGTH, theorem"arithmetic" "ADD_CLAUSES"]) THEN 
  ASM_RW_TAC[]));


(*---------------------------------------------------------------------------
 * Get clean recursion equations and induction rule.
 *---------------------------------------------------------------------------*)
val fqsort_induction = save_thm("fqsort_induction",
  RW_RULE [fqsort_terminates](DISCH_ALL (#induction fqsort_def)));
val fqsort_eqns = save_thm("fqsort_eqns", 
  RW_RULE[fqsort_terminates](#rules fqsort_def));

val FQSORT_TAC = PROGRAM_TAC{rules=fqsort_eqns, induction=fqsort_induction};


(*---------------------------------------------------------------------------
 * Hand instantiation needed, in lieu of higher-order matching in
 * my rewriter.
 *---------------------------------------------------------------------------*)
val let_lem1 = 
 BETA_RULE(Q.ISPECL[`\hole:'a list. permutation (x::rst) hole`,
                    `partition ((\y:'a. ord y (x:'a)),rst)`,
                    `\(l1:'a list) l2. fqsort(ord,l1)++[x]++fqsort(ord,l2)`]
            PULL_LET2);

(*---------------------------------------------------------------------------
 * The result list is a permutation of the input list.
 *---------------------------------------------------------------------------*)
val fqsort_permutation = Q.store_thm
("fqsort_permutation",
`!(R:^order) (L:'a list). permutation L (fqsort(R,L))`,
FQSORT_TAC
 THEN RW_TAC [permutation_refl]
 THEN RW_TAC[let_lem1] THEN LET_INTRO_TAC 
 THEN DISCH_TAC THEN RES_TAC
 THEN RW_TAC[append_infix,APPEND] 
 THEN MATCH_MP_TAC cons_permutation
 THEN MATCH_MP_TAC (PURE_RW_RULE[transitive_def]permutation_trans)
 THEN Q.EXISTS_TAC`APPEND x' y : 'a list` 
 THEN CONJ_TAC
 THENL [ RULE_ASSUM_TAC(RW_RULE[partition_def]) 
           THEN IMP_RES_THEN MP_TAC part_perm_lem,
         ALL_TAC]
 THEN ASM_CRW_TAC[APPEND,permutation_cong]);



(*---------------------------------------------------------------------------
 * Hand instantiation again.
 *---------------------------------------------------------------------------*)
val let_lem2 = 
 BETA_RULE(Q.ISPECL[`\hole:'a list. mem x hole = mem x (x'::rst)`,
                    `partition ((\y:'a. ord y (x':'a)),rst)`,
                    `\(l1:'a list) l2. fqsort(ord,l1)++[x']++fqsort(ord,l2)`]
            PULL_LET2);


(*---------------------------------------------------------------------------
 * This is gross: why does RES_TAC work, but not ANTE_RES_THEN? Or, better
 * yet, conditional rewriting?
 *---------------------------------------------------------------------------*)
val fqsort_mem = Q.store_thm
("fqsort_mem",
 `!(x:'a) R L. mem x (fqsort(R,L)) = mem x L`,
GEN_TAC THEN FQSORT_TAC
 THENL
  [ REFL_TAC,
    RW_TAC[let_lem2] 
      THEN LET_INTRO_TAC
      THEN RULE_ASSUM_TAC(RW_RULE[partition_def])
      THEN RW_TAC[append_infix,mem_of_append,partition_def]
      THEN DISCH_THEN (fn th => MP_TAC (GSYM (MATCH_MP part_mem th)) 
                                THEN ASSUME_TAC th THEN RES_TAC)
      THEN ASM_RW_TAC[APPEND,mem_of_append,mem_def]
      THEN DISCH_THEN (fn th => EQ_TAC THEN STRIP_TAC THEN 
                                MP_TAC (SPEC_ALL th) THEN 
                                ASM_RW_TAC[])
      THEN STRIP_TAC THEN ASM_RW_TAC[]]);


(*---------------------------------------------------------------------------
 * Hand instantiation again.
 *---------------------------------------------------------------------------*)
val let_lem3 = 
 BETA_RULE(Q.ISPECL[`\hole:'a list. finiteRchain(ord, hole)`,
                    `partition ((\y:'a. ord y (x:'a)),rst)`,
                    `\(l1:'a list) l2. fqsort(ord,l1)++[x]++fqsort(ord,l2)`]
            PULL_LET2);

(*---------------------------------------------------------------------------
 * The result list is a finiteRchain.
 *---------------------------------------------------------------------------*)
val fqsort_orders = Q.store_thm
("fqsort_orders",
 `!(R:^order) L. tt_relation R ==> finiteRchain(R, fqsort(R,L))`,
FQSORT_TAC THENL
 [ RW_TAC[finiteRchain_eqns], 
   RW_TAC[let_lem3,append_infix] THEN LET_INTRO_TAC
   THEN POP_ASSUM (fn th => 
     DISCH_TAC THEN MP_TAC (MATCH_MP tt_relation_trans th) THEN ASSUME_TAC th)
   THEN RES_TAC
   THEN DISCH_TAC THEN MATCH_MP_TAC finiteRchain_append
   THEN ASM_RW_TAC[finiteRchain_eq,APPEND,tt_relation_trans,fqsort_mem,mem_def]
   THEN RULE_ASSUM_TAC (RW_RULE[partition_def])
   THEN MP_TAC (RW_RULE[mem_def]
                 (Q.SPECL[`\y. ord y (x:'a)`,`rst`,`x'`,`y`,`[]`,`[]`] 
                         parts_have_prop)) THEN BETA_TAC
   THEN ASM_RW_TAC[]
   THEN STRIP_TAC THEN CONJ_TAC
   THENL
   [ GEN_TAC THEN 
     DISCH_THEN (fn th => POP_ASSUM (fn th1 => MP_TAC(MATCH_MP th1 th)))
       THEN Q.UNDISCH_TAC `tt_relation (ord:'a->'a->bool)` 
       THEN DISCH_THEN (fn th => MP_TAC
              (Q.SPECL[`x`,`y'`](CONJUNCT2 (RW_RULE[tt_relation_def] th))))
       THEN STRIP_TAC THEN ASM_RW_TAC[],
     REPEAT STRIP_TAC THEN ASM_RW_TAC[] 
      THEN Q.UNDISCH_TAC `tt_relation (ord:'a->'a->bool)` 
      THEN DISCH_THEN (fn th => MP_TAC
                (Q.SPECL[`x`,`y'`](CONJUNCT2 (RW_RULE[tt_relation_def] th)))
                THEN ASSUME_TAC th)
      THEN ASM_RW_TAC[]
      THEN DISCH_TAC
      THEN IMP_RES_TAC(RW_RULE[transitive_def] tt_relation_trans)
      THEN RES_TAC THEN RES_TAC]]);

(*---------------------------------------------------------------------------
 * Bring everything together.
 *---------------------------------------------------------------------------*)
val fqsort_correct = 
Q.store_thm("fqsort_correct", 
`performs_sorting (fqsort:^order#'a list -> 'a list)`,
RW_TAC[performs_sorting,  
       fqsort_permutation,  
       fqsort_orders]);



html_theory"-";
