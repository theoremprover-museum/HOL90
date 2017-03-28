new_theory"qsort" handle _ => ();
cons_path "../" theory_path;
map new_parent ["kls_list", "sorting"];
map add_theory_to_sml["list", "kls_list", "sorting", "permutation"];


(* Make some abbreviations *)

val order = ty_antiq(==`:'a -> 'a -> bool`==);
val qsort_ty = ty_antiq(==`:^order#'a list -> 'a list`==);

val o_DEF = definition"combin" "o_DEF";
val transitive_def = definition"TC" "transitive_def";


(*---------------------------------------------------------------------------
 * The quicksort algorithm.
 *---------------------------------------------------------------------------*)

val qsort_def = 
Rfunction `measure (LENGTH o SND)` 
   `(qsort(ord:^order,[]) = []) /\
    (qsort(ord, (x:'a)::rst) = 
      qsort(ord,filter($~ o ord x) rst)
      ++[x]++
      qsort(ord,filter(ord x) rst))`;


(*---------------------------------------------------------------------------
 *  Termination of quicksort.
 *---------------------------------------------------------------------------*)
val qsort_terminates = save_thm("qsort_terminates",
HOL_Tfl.prove_termination qsort_def
(CRW_TAC[definition"list" "LENGTH", length_filter,
         theorem "arithmetic" "LESS_EQ_IMP_LESS_SUC"]));


val qsort_induction = save_thm("qsort_induction",
  RW_RULE [qsort_terminates](DISCH_ALL (#induction qsort_def)));
val qsort_eqns = save_thm("qsort_eqns", 
     RW_RULE[qsort_terminates](#rules qsort_def));
val qsort_eqns = SUBS[append_infix] qsort_eqns;


val tt_relation_trans = Q.prove
`!R:^order. tt_relation R ==> transitive R`
(RW_TAC[definition"sorting" "tt_relation_def",transitive_def]);


val QSORT_TAC = PROGRAM_TAC{induction = qsort_induction,
                                rules = qsort_eqns};

(*----------------------------------------------------------------------------
 *           PROPERTIES OF QSORT
 *---------------------------------------------------------------------------*)

val qsort_mem_stable = 
Q.store_thm
("qsort_mem_stable",
`!(x:'a) R L. mem x (qsort(R,L)) = mem x L`,
GEN_TAC THEN QSORT_TAC THENL
[ REFL_TAC,
  ASM_RW_TAC[o_DEF,mem_of_append,mem_def,mem_filter] 
  THEN BETA_TAC 
  THEN EQ_TAC 
  THEN REPEAT STRIP_TAC 
  THEN ASM_RW_TAC[Q.TAUT_CONV`~P \/ Q \/ P`]]);


val qsort_permutation = 
Q.store_thm
("qsort_permutation",
`!(R:^order) (L:'a list). permutation L (qsort(R,L))`,
QSORT_TAC THENL
 [RW_TAC [permutation_refl],
  RW_TAC[APPEND] THEN MATCH_MP_TAC cons_permutation 
  THEN MATCH_MP_TAC (PURE_RW_RULE[transitive_def]permutation_trans) 
  THEN Q.EXISTS_TAC`APPEND(filter(~ o ord x) rst) (filter((ord:^order) x) rst)`
  THEN CONJ_TAC THENL
  [ MATCH_MP_TAC(ONCE_RW_RULE[permutation_sym] append_permutation_sym) 
     THEN MATCH_ACCEPT_TAC permutation_split,
    ASM_CRW_TAC [permutation_cong]]]);


val qsort_orders = 
Q.store_thm
("qsort_orders",
`!(R:^order) L. tt_relation R ==> finiteRchain(R, qsort(R,L))`,
QSORT_TAC THENL
[ RW_TAC[finiteRchain_eqns],
  MATCH_MP_TAC finiteRchain_append 
    THEN ASM_CRW_TAC[finiteRchain_eq,APPEND,tt_relation_trans,
                     qsort_mem_stable,mem_filter,mem_def,o_DEF] THEN BETA_TAC 
    THEN REPEAT GEN_TAC THEN POP_ASSUM (fn th => STRIP_ASSUME_TAC
         (Q.SPECL[`x`,`x'`](CONJUNCT2 (RW_RULE[tt_relation_def] th)))
    THEN ASSUME_TAC th) THEN ASM_RW_TAC[] THEN STRIP_TAC
    THENL[ ASM_RW_TAC[],
           IMP_RES_TAC(RW_RULE[transitive_def] tt_relation_trans)]]);


(*---------------------------------------------------------------------------
 * Bring everything together.
 *---------------------------------------------------------------------------*)
val qsort_correct = 
Q.store_thm("qsort_correct", `performs_sorting (qsort:^qsort_ty)`,
RW_TAC[performs_sorting,  
       qsort_permutation,  
       qsort_orders]);



(*---------------------------------------------------------------------------
 * For fun, can try something like the following (needs "reduce_lib" to
 * be loaded, and it is)
 *
  (REPEATC (CHANGED_CONV
    (REWRITE_CONV[qsort_eqns, filter_def, o_DEF, APPEND] THENC 
     REDUCE_CONV THENC DEPTH_CONV BETA_CONV)))
  (Term`qsort($>=, [0;3;5;2;2;1;5])`);

 *
 *---------------------------------------------------------------------------*)

html_theory"-";
export_theory();
