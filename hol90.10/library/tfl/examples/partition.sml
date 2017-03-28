new_theory"partition";
cons_path "../" theory_path;
val _ = new_parent "kls_list";
val _ = new_parent "permutation";

val transitive_def = definition"TC" "transitive_def";
val LENGTH = definition"list" "LENGTH";
val mem_def = definition"kls_list" "mem_def";
val APPEND = theorem"kls_list" "APPEND";
val mem_of_append = theorem"kls_list" "mem_of_append";
val mem_append_eq1 = theorem"kls_list" "mem_append_eq1";
val mem_append_eq2 = theorem"kls_list" "mem_append_eq2";

val permutation_refl = theorem"permutation" "permutation_refl";
val permutation_trans = theorem"permutation" "permutation_trans";
val cons_permutation = theorem"permutation" "cons_permutation";
val permutation_cong = theorem"permutation" "permutation_cong";

val LIST_INDUCT_TAC = INDUCT_THEN (theorem "list" "list_INDUCT") MP_TAC;


(*---------------------------------------------------------------------------
 * Partition a list by a predicate.
 *---------------------------------------------------------------------------*)
val part_def = 
   Rfunction  `inv_image ^list_pred (FST o SND)`
       `(part(P:'a->bool, [], l1,l2) = (l1,l2)) /\
        (part(P, h::rst, l1,l2) =
           (P h => part(P,rst, h::l1, l2)
                |  part(P,rst,  l1,  h::l2)))`;


(*---------------------------------------------------------------------------
 * A packaged version of "part". Most theorems about "partition" will be 
 * instances of theorems about "part". 
 *---------------------------------------------------------------------------*)
val partition_def = 
  Q.new_definition
      ("partition_def", 
      `!(P:'a->bool). partition(P,L) = part(P,L,[],[])`);



(*---------------------------------------------------------------------------
 * Theorems about "part"
 *---------------------------------------------------------------------------*)
val part_length = Q.store_thm
("part_length",
 `!P (L:'a list) l1 l2 p q.
    ((p,q) = part(P,L,l1,l2))
    ==> (LENGTH L + LENGTH l1 + LENGTH l2 = LENGTH p + LENGTH q)`,
PROGRAM_TAC{induction = #induction part_def, rules = #rules part_def}
  THENL [ALL_TAC, RES_TAC, RES_TAC]
  THEN POP_ASSUM MP_TAC 
  THEN RW_TAC[LENGTH,theorem"arithmetic" "ADD_CLAUSES", #rules part_def]);


val part_length_lem = Q.store_thm
("part_length_lem",
`!P (L:'a list) l1 l2 p q. 
    ((p,q) = part(P,L,l1,l2))
    ==>  LENGTH p <= LENGTH L + LENGTH l1 + LENGTH l2 /\
         LENGTH q <= LENGTH L + LENGTH l1 + LENGTH l2`,
RW_TAC[part_length]
  THEN REPEAT STRIP_TAC 
  THEN CONV_TAC ARITH_CONV);


(*---------------------------------------------------------------------------
 * Everything in the partitions occurs in the original list, and vice-versa.
 * The goal has been generalized. The proof could be improved.
 *---------------------------------------------------------------------------*)

val part_mem = Q.store_thm
("part_mem",
 `!P (L:'a list) a1 a2 l1 l2. 
     ((a1,a2) = part(P,L,l1,l2)) 
       ==> 
      !x. mem x (APPEND L (APPEND l1 l2)) = mem x (APPEND a1 a2)`,
GEN_TAC THEN LIST_INDUCT_TAC THEN RW_TAC[APPEND,#rules part_def]
 THEN DISCH_TAC THEN REPEAT GEN_TAC 
 THEN COND_CASES_TAC THEN DISCH_TAC 
 THEN RES_TAC 
 THEN GEN_TAC 
 THEN POP_ASSUM (K ALL_TAC) THEN POP_ASSUM (K ALL_TAC) 
 THEN POP_ASSUM (fn th => PURE_ONCE_RW_TAC[GSYM th]) 
 THEN PURE_ONCE_RW_TAC[mem_append_eq1] 
 THEN PURE_ONCE_RW_TAC[mem_append_eq2] 
 THEN RW_TAC[mem_of_append] 
 THEN PURE_ONCE_RW_TAC[mem_append_eq1]
 THENL [ALL_TAC, PURE_ONCE_RW_TAC[mem_append_eq2]]
 THEN RW_TAC[mem_of_append]);


(*---------------------------------------------------------------------------
 * Appending the two partitions of the original list is a permutation
 * of the original list (generalized).
 *---------------------------------------------------------------------------*)
val part_perm_lem = Q.store_thm
("part_perm_lem",
`!P (L:'a list) a1 a2 l1 l2. 
     ((a1,a2) = part(P,L,l1,l2)) 
       ==> 
      permutation (APPEND L (APPEND l1 l2)) (APPEND a1 a2)`,
GEN_TAC THEN LIST_INDUCT_TAC 
  THEN RW_TAC[APPEND,#rules part_def,permutation_refl]
  THEN DISCH_TAC THEN REPEAT GEN_TAC 
  THEN COND_CASES_TAC THEN DISCH_TAC THEN RES_TAC
  THEN MATCH_MP_TAC (PURE_RW_RULE[transitive_def]permutation_trans)
  THENL [ Q.EXISTS_TAC`APPEND L (APPEND (h::l1) l2)`,
          Q.EXISTS_TAC`APPEND L (APPEND l1 (h::l2))`
        ]
  THEN ASM_RW_TAC[]
  THEN MATCH_MP_TAC (PURE_RW_RULE[transitive_def]permutation_trans)
  THEN Q.EXISTS_TAC`APPEND L (h::APPEND l1 l2)`
  THEN RW_TAC[permutation_refl,APPEND,
              RW_RULE[permutation_refl]
                     (Q.SPECL[`h`,`APPEND L (APPEND l1 l2)`,`L`,`APPEND l1 l2`]
                             cons_permutation)]
  THEN CRW_TAC[permutation_refl,permutation_cong,cons_permutation]);


(*---------------------------------------------------------------------------
 * Each element in the positive and negative partitions has the desired
 * property.
 *---------------------------------------------------------------------------*)
val parts_have_prop = Q.store_thm
("parts_have_prop",
 `!P (L:'a list) A B l1 l2. 
   ((A,B) = part(P,L,l1,l2))
    /\ (!x. mem x l1 ==> P x)
    /\ (!x. mem x l2 ==> ~P x)
    ==> 
      (!z. mem z A ==>  P z) /\
      (!z. mem z B ==> ~P z)`,
GEN_TAC THEN LIST_INDUCT_TAC THEN RW_TAC[#rules part_def]
  THEN STRIP_TAC THEN REPEAT GEN_TAC 
  THEN COND_CASES_TAC THEN STRIP_TAC 
  THEN FIRST_ASSUM MATCH_MP_TAC
  THENL [ MAP_EVERY Q.EXISTS_TAC [`h::l1`, `l2`],
          MAP_EVERY Q.EXISTS_TAC [`l1`, `h::l2`]
        ]
  THEN ASM_RW_TAC[mem_def]
  THEN GEN_TAC THEN STRIP_TAC THEN ASM_RW_TAC[]);

export_theory();
html_theory"-";
