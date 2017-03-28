(*---------------------------------------------------------------------------
 *                SPECIFICATION OF SORTING
 *---------------------------------------------------------------------------*)

cons_path "../" theory_path;
new_theory"sorting";
new_parent"kls_list";
new_parent"permutation";

val transitive_def = definition"TC" "transitive_def";

(*---------------------------------------------------------------------------
 * The idea of sortedness is actually a little difficult to nail down. It
 * requires a "permutation" relation for lists, and a "chain" predicate that 
 * holds just when the order relation holds between all adjacent elements of 
 * the list. But what are the requirements on the order relation "R"? At a 
 * minimum, it must be transitive, but it doesn't seem to have to be anything
 * else. Totality is forced on us by the quicksort proof. Should R be 
 * antisymmetric?
 *---------------------------------------------------------------------------*)

val order = ty_antiq(==`:'a -> 'a -> bool`==);

val tt_relation_def = Q.new_definition("tt_relation_def",
`tt_relation (R:^order) = 
   (!x y z. R x y /\ R y z ==> R x z) /\   (* Transitive *)
   (!x y. R x y \/ R y x)`);               (* Total *)



(*----------------------------------------------------------------------------
 * Define the "finiteRchain" function (a.k.a "sorted") via pattern matching. 
 *---------------------------------------------------------------------------*)

val finiteRchain_def = 
Rfunction `inv_image ^list_pred SND`
  `(finiteRchain (R:^order, []) = T) /\
   (finiteRchain (R,       [x]) = T) /\   
   (finiteRchain (R, x::y::rst) = R x y /\ finiteRchain(R, y::rst))`;


(*----------------------------------------------------------------------------
 * The specification that a sorting function must (at least) meet. 
 *---------------------------------------------------------------------------*)

val performs_sorting_def = 
 Q.new_definition
("performs_sorting",
  `performs_sorting f = 
     !R:^order.
        tt_relation R 
         ==> 
         !L. permutation L (f(R,L)) /\ finiteRchain(R, f(R,L))`);




(*----------------------------------------------------------------------------
 *                    THEOREMS ABOUT "FINITE R-CHAINS"
 *---------------------------------------------------------------------------*)
val finiteRchain_eqns = save_thm("finiteRchain_eqns", 
                                 #rules finiteRchain_def);

val finiteRchain_induction = save_thm("finiteRchain_induction", 
                                      #induction finiteRchain_def);

(*----------------------------------------------------------------------------
 *    When consing onto a finiteRchain yields a finiteRchain 
 *---------------------------------------------------------------------------*)
val mem_def = definition"kls_list" "mem_def";
val LIST_INDUCT_TAC = INDUCT_THEN (theorem"list" "list_INDUCT") ASSUME_TAC;


val finiteRchain_eq = Q.store_thm("finiteRchain_eq",
`!R:^order. 
  transitive R
   ==> 
  !L (x:'a). 
     finiteRchain(R, x::L) = finiteRchain(R,L) /\ (!y. mem y L ==> R x y)`,
GEN_TAC THEN DISCH_TAC THEN LIST_INDUCT_TAC 
 THEN ASM_RW_TAC[finiteRchain_eqns,mem_def] 
 THEN REPEAT GEN_TAC 
 THEN EQ_TAC 
 THEN REPEAT STRIP_TAC
 THEN ASM_CRW_TAC[]
 THEN RULE_ASSUM_TAC(PURE_RW_RULE[transitive_def]) 
 THEN RES_TAC);


(*----------------------------------------------------------------------------
 *    Now try it using recursion induction -- the proof seems harder!
 *---------------------------------------------------------------------------*)
val finiteRchain_eq = Q.prove
`!(R:^order) L. 
 transitive R ==> 
 !x:'a. finiteRchain(R, x::L) = finiteRchain(R,L) /\ !y. mem y L ==> R x y`
(REC_INDUCT_TAC finiteRchain_induction THEN REPEAT CONJ_TAC THEN 
REPEAT GEN_TAC THEN TRY (REPEAT DISCH_TAC) THENL
[ RW_TAC[finiteRchain_eqns,mem_def],
  GEN_TAC THEN RW_TAC[finiteRchain_eqns,mem_def] THEN EQ_TAC 
   THENL[RW_TAC[], DISCH_THEN MATCH_MP_TAC THEN RW_TAC[]], 
   PURE_ONCE_RW_TAC[Q.INST[`x`|->`x':'a`, `y`|->`x:'a`,
                           `rst`|->`(y:'a)::rst`] (#rules finiteRchain_def)]
   THEN GEN_TAC THEN EQ_TAC THEN ASM_RW_TAC[] THEN STRIP_TAC 
   THENL 
   [ONCE_RW_TAC[mem_def] THEN GEN_TAC THEN STRIP_TAC 
    THENL [ASM_RW_TAC[],
           Q.UNDISCH_TAC`transitive (R:^order)` 
           THEN ONCE_RW_TAC[transitive_def] THEN DISCH_THEN MATCH_MP_TAC 
           THEN Q.EXISTS_TAC`x` THEN ASM_RW_TAC[]],
    ASM_CRW_TAC[mem_def]]]);


(*----------------------------------------------------------------------------
 *       When appending finiteRchains gives a finiteRchain. 
 *---------------------------------------------------------------------------*)

val mem_of_append = theorem "kls_list" "mem_of_append";
val APPEND = theorem "kls_list" "APPEND";

val finiteRchain_append = Q.store_thm("finiteRchain_append",
`!(R:^order) L1 L2. 
   transitive R         /\
   finiteRchain(R,L1)   /\ 
   finiteRchain (R, L2) /\ 
   (!x y. mem x L1 /\ mem y L2 ==> R x y)
   ==> finiteRchain(R, APPEND L1 L2)`,
REPEAT GEN_TAC THEN DISCH_THEN (fn th => 
 let val (h::t) = CONJUNCTS th
 in ASSUME_TAC h THEN MP_TAC (LIST_CONJ t) THEN 
    Q.ID_SPEC_TAC`L2` THEN Q.ID_SPEC_TAC`L1` end) 
THEN LIST_INDUCT_TAC THEN GEN_TAC 
THEN ASM_RW_TAC[finiteRchain_eqns,APPEND,finiteRchain_eq,mem_def,mem_of_append]
THEN REPEAT STRIP_TAC 
THEN ASM_CRW_TAC[]);


export_theory();
html_theory"-";
