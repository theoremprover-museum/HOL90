new_theory"variant" handle _ => ();
val _ = cons_path "../" theory_path;
map new_parent ["kls_list"];  


(* Reasoning utilities and lemmas. *)

val LIST_INDUCT_TAC = INDUCT_THEN (theorem "list" "list_INDUCT") ASSUME_TAC;
val LENGTH               = definition"list" "LENGTH";
val mem_def              = definition"kls_list" "mem_def";
val filter_def           = definition"kls_list" "filter_def";
val length_filter_subset = theorem "kls_list" "length_filter_subset";

val LESS_IMP_LESS_OR_EQ  = theorem"arithmetic" "LESS_IMP_LESS_OR_EQ";
val LESS_EQ_IMP_LESS_SUC = theorem"arithmetic" "LESS_EQ_IMP_LESS_SUC";
val LESS_EQ1             = GSYM(theorem"arithmetic" "LESS_EQ")
val LESS_REFL            = theorem"prim_rec" "LESS_REFL";
val LESS_EQ_REFL         = theorem"arithmetic" "LESS_EQ_REFL";
val LESS_MONO            = theorem"prim_rec" "LESS_MONO"
val LESS_SUC             = theorem"prim_rec" "LESS_SUC";


(*---------------------------------------------------------------------------
 * The definition of variant.
 *---------------------------------------------------------------------------*)
val variant_def = 
   Rfunction `measure \(x,L). LENGTH(filter (\y. x <= y) L)`
       `variant(x, L) = (mem x L => variant(SUC x, L) | x)`;


(*---------------------------------------------------------------------------
 * The termination argument.
 *---------------------------------------------------------------------------*)
val variant_terminates = Q.store_thm
("variant_terminates",
`!x L. mem x L ==>
       LENGTH (filter (\y. SUC x <= y) L) < LENGTH (filter (\y'. x <= y') L)`,
RW_TAC[EQT_ELIM(ARITH_CONV(Term`SUC a <= b = a<b`)), LESS_EQ1] THEN 
GEN_TAC THEN LIST_INDUCT_TAC THEN RW_TAC[mem_def,filter_def] THEN 
BETA_TAC THEN GEN_TAC THEN STRIP_TAC THENL
[ ASM_RW_TAC[LESS_REFL,LENGTH,LESS_EQ_REFL] THEN 
  MATCH_MP_TAC LESS_EQ_IMP_LESS_SUC THEN 
  MATCH_MP_TAC length_filter_subset THEN BETA_TAC THEN GEN_TAC THEN 
  MATCH_ACCEPT_TAC LESS_IMP_LESS_OR_EQ,
 RES_TAC THEN REPEAT COND_CASES_TAC THEN ASM_RW_TAC[LENGTH]
 THENL[ ASM_RW_TAC[LESS_MONO],
        POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN CONV_TAC ARITH_CONV,
        ASM_RW_TAC[LESS_SUC]]]);


(*---------------------------------------------------------------------------
 * Removal of termination conditions.
 *---------------------------------------------------------------------------*)
val variant_eqn = save_thm("variant_eqn",
    RW_RULE[variant_terminates] (#rules variant_def));
val variant_induction = save_thm("variant_induction",
    PROVE_HYP variant_terminates (#induction variant_def));


(*---------------------------------------------------------------------------
 * Correctness: A variant is not in the list it is supposed to vary from.
 *---------------------------------------------------------------------------*)
val variant_correct = Q.store_thm("variant_correct", 
`!x L. ~mem (variant (x,L)) L`,
PROGRAM_TAC{induction=variant_induction, rules=variant_eqn}
 THEN ASM_RW_TAC[]);

html_theory"-";
