cons_path "../" theory_path;
new_theory"permutation";
new_parent"kls_list";

val NNF_CONV =
   let val DE_MORGAN = REWRITE_CONV
                        [Q.TAUT_CONV`~(x==>y) = (x /\ ~y)`,
                         Q.TAUT_CONV`~x \/ y = (x ==> y)`,DE_MORGAN_THM]
       val QUANT_CONV = NOT_EXISTS_CONV ORELSEC NOT_FORALL_CONV
   in REDEPTH_CONV (QUANT_CONV ORELSEC CHANGED_CONV DE_MORGAN)
   end;


val permutation_def = 
Q.new_definition
 ("permutation_def",
  `permutation L1 L2 = !x:'a. filter ($= x) L1 = filter ($= x) L2`);


(*---------------------------------------------------------------------------
 *                   THEOREMS ABOUT PERMUTATIONS 
 *---------------------------------------------------------------------------*)
map add_theory_to_sml["list", "kls_list"];
val LIST_INDUCT_TAC = INDUCT_THEN (theorem "list" "list_INDUCT") ASSUME_TAC;
val transitive_def = definition"TC" "transitive_def";

val permutation_refl = 
Q.store_thm
("permutation_refl",
    `!L:'a list. permutation L L`,
    RW_TAC[permutation_def]);


val permutation_trans =  
Q.store_thm
("permutation_trans",
  `transitive (permutation:'a list -> 'a list -> bool)`,
 RW_TAC[permutation_def, transitive_def]);


val permutation_sym = 
Q.store_thm
("permutation_sym",
  `!l1 (l2:'a list). permutation l1 l2 = permutation l2 l1`,
RW_TAC[permutation_def] THEN REPEAT GEN_TAC THEN EQ_TAC THEN RW_TAC[]);

val permutation_cong = 
Q.store_thm
("permutation_cong",
`!(L1:'a list) L2 L3 L4. 
     permutation L1 L3 /\ 
     permutation L2 L4
     ==> permutation (APPEND L1 L2) (APPEND L3 L4)`,
REPEAT GEN_TAC
 THEN RW_TAC[permutation_def,filter_append_distrib]);


val cons_append = Q.prove`!L (h:'a). h::L = APPEND [h] L`(RW_TAC[APPEND]);

val permutation_mono = 
Q.store_thm
("permutation_mono",
`!l1 l2 (x:'a). permutation l1 l2 ==> permutation (x::l1) (x::l2)`,
ONCE_RW_TAC[cons_append] 
   THEN CRW_TAC[permutation_cong, permutation_refl]);


val permutation_cons_iff = 
let val lem = 
Q.prove`permutation (x::l1) (x::l2) ==> permutation l1 (l2:'a list)`
(RW_TAC[permutation_def]
 THEN REPEAT GEN_TAC 
 THEN CONV_TAC CONTRAPOS_CONV THEN CONV_TAC NNF_CONV
 THEN STRIP_TAC
 THEN Q.EXISTS_TAC`x'` 
 THEN RW_TAC[filter_def]
 THEN COND_CASES_TAC THEN RW_TAC[]
 THENL [POP_ASSUM SUBST_ALL_TAC, ALL_TAC]
 THEN ASM_RW_TAC[])
in 
  save_thm ("permutation_cons_iff",
            GEN_ALL(IMP_ANTISYM_RULE lem (SPEC_ALL permutation_mono)))
end;


(* Also useful *)
val permutation_nil = 
Q.store_thm
("permutation_nil",
 `!L:'a list. (permutation L [] = (L=[])) /\ 
               (permutation [] L = (L=[]))`,
 GEN_TAC 
   THEN STRUCT_CASES_TAC (Q.SPEC`L` list_CASES') 
   THEN RW_TAC[permutation_def,filter_def]
   THEN CONV_TAC NNF_CONV 
   THEN CONJ_TAC 
   THEN Q.EXISTS_TAC`h` THEN RW_TAC []);


val permutation_append = 
Q.store_thm
("permutation_append",
 `!l1 (l2:'a list). permutation (APPEND l1 l2) (APPEND l2 l1)`,
 RW_TAC[permutation_def] 
    THEN LIST_INDUCT_TAC 
    THEN RW_TAC[APPEND]
    THEN ASM_RW_TAC[filter_def] THEN POP_ASSUM (K ALL_TAC)
    THEN GEN_TAC THEN LIST_INDUCT_TAC
    THEN RW_TAC[APPEND,filter_def] THEN REPEAT GEN_TAC 
    THEN REPEAT COND_CASES_TAC
    THENL
    [ POP_ASSUM (SUBST_ALL_TAC) THEN POP_ASSUM SUBST_ALL_TAC 
       THEN POP_ASSUM SUBST_ALL_TAC
       THEN POP_ASSUM (fn th => RW_TAC[RW_RULE[](Q.SPEC`h'` th)]),
      POP_ASSUM MP_TAC THEN ASM_RW_TAC[],
      POP_ASSUM SUBST_ALL_TAC THEN POP_ASSUM MP_TAC THEN ASM_RW_TAC[],
      ASM_RW_TAC[] THEN POP_ASSUM(fn _ => POP_ASSUM (fn _ => POP_ASSUM (fn _ =>
         POP_ASSUM (fn th => RW_TAC[RW_RULE[] (Q.SPEC`h` th)])))),
      POP_ASSUM SUBST_ALL_TAC THEN POP_ASSUM (fn th0 =>
        POP_ASSUM (fn th => RW_TAC[RW_RULE[th0](Q.SPEC`h'` th)])),
      ASM_RW_TAC[] THEN POP_ASSUM (fn _ => POP_ASSUM (fn th0 => 
        POP_ASSUM (fn th => RW_TAC[RW_RULE[th0](Q.SPEC`x` th)])))]);


val cons_permutation = 
Q.store_thm
("cons_permutation",
`!(x:'a) L M N. permutation L (APPEND M N) 
                ==> 
                permutation (x::L) (APPEND M (x::N))`,
(REPEAT GEN_TAC THEN DISCH_TAC THEN
 MATCH_MP_TAC(PURE_RW_RULE[transitive_def] permutation_trans)
 THEN Q.EXISTS_TAC`x::APPEND M N`
 THEN CONJ_TAC
 THENL [PURE_ASM_RW_TAC[permutation_mono],
        MATCH_MP_TAC(PURE_RW_RULE[transitive_def] permutation_trans)
         THEN Q.EXISTS_TAC`x :: APPEND N M`
         THEN CONJ_TAC
         THENL[MATCH_MP_TAC permutation_mono THEN 
               MATCH_ACCEPT_TAC permutation_append,
               ACCEPT_TAC(PURE_RW_RULE[APPEND] 
                           (Q.SPECL[`x::N`,`M`] permutation_append))]]));

val append_permutation_sym = 
Q.store_thm
("append_permutation_sym",
`!(A:'a list) B C. 
      permutation (APPEND A B) C ==> permutation (APPEND B A) C`,
REPEAT GEN_TAC 
  THEN DISCH_TAC 
  THEN MATCH_MP_TAC(PURE_RW_RULE[transitive_def] permutation_trans)
  THEN Q.EXISTS_TAC`APPEND A B` 
  THEN ASM_RW_TAC[permutation_append]
  THEN RW_TAC[]);

val permutation_split = 
Q.store_thm
("permutation_split",
`!(L:'a list). permutation L (APPEND (filter P L) (filter (~ o P) L))`,
RW_TAC[definition"combin" "o_DEF"] THEN BETA_TAC
 THEN LIST_INDUCT_TAC
 THEN RW_TAC[APPEND,filter_def,permutation_refl] THEN BETA_TAC
 THEN GEN_TAC 
 THEN COND_CASES_TAC
 THEN ASM_RW_TAC[APPEND,permutation_mono,cons_permutation]);

local open RW
      val pss = RW.add_rws (RW.Implicit.implicit_simpls())
            [theorem"arithmetic" "ADD_CLAUSES",
             definition "list" "LENGTH",
             definition"kls_list" "filter_def",
             theorem "permutation"  "permutation_refl",
             theorem"pair" "PAIR_EQ", 
             theorem"kls_list" "APPEND",
             permutation_nil];
      val RWTAC = REWRITE_TAC Fully (Simpls(pss,[]),Context([],ADD),
                                     Congs[],Solver std_solver)
in
val SIMPL = RWTAC THEN TRY(CHANGED_TAC BETA_TAC THEN RWTAC)
end;


val length_filter = theorem"kls_list" "length_filter";
val list_cases = theorem"kls_list" "list_CASES'";
val length_append_filter = theorem"kls_list" "length_append_filter";
val perm_trans = RW_RULE[definition"TC" "transitive_def"] permutation_trans;

(*---------------------------------------------------------------------------
 * Directly performs one "sorting step" between 2 non-empty permutations.
 *---------------------------------------------------------------------------*)
val perm_sort_step = Q.store_thm("perm_sort_step",
`!L (h:'a) t. permutation (h::t) L ==> ?rst. h::rst = filter ($=h) L`,
RW_TAC[permutation_def]
 THEN REPEAT GEN_TAC 
 THEN DISCH_THEN (MP_TAC o Q.SPEC`h`)
 THEN SIMPL
 THEN DISCH_THEN (SUBST1_TAC o SYM)
 THEN Q.EXISTS_TAC`filter ($=h) t` 
 THEN REFL_TAC);


(*---------------------------------------------------------------------------
 * This seems much harder to prove than the preceding facts about
 * permutations. Took me awhile anyway. In other formulations of
 * permutation, this is quite easy to prove.
 *---------------------------------------------------------------------------*)
val permutation_length = Q.store_thm("permutation_length",
`!(l1:'a list) l2. permutation l1 l2 ==> (LENGTH l1 = LENGTH l2)`,
LIST_INDUCT_TAC
 THENL 
 [ALL_TAC,
  REPEAT GEN_TAC 
   THEN STRIP_ASSUME_TAC (Q.SPEC`l2` list_cases) THEN POP_ASSUM SUBST_ALL_TAC]
 THEN SIMPL
 THEN DISCH_THEN (fn th => 
       ASSUME_TAC (MATCH_MP perm_trans 
                    (CONJ th (Q.INST[`P` |-> `$=h:'a->bool`]
                                    (Q.SPEC`h'::t` permutation_split))))
       THEN MP_TAC th)
 THEN DISCH_THEN(CHOOSE_THEN(fn th => SUBST_ALL_TAC(SYM th) THEN ASSUME_TAC th)
                 o MATCH_MP perm_sort_step)
 THEN RULE_ASSUM_TAC (PURE_RW_RULE[APPEND,permutation_cons_iff])
 THEN RES_THEN (MP_TAC o Q.SPECL[`h`,`h`] o
   MATCH_MP
    (Q.prove`!l1 l2. (LENGTH l1 = LENGTH l2)
               ==> !(h1:'a) (h2:'a). LENGTH(h1::l1) = LENGTH(h2::l2)` SIMPL))
 THEN PURE_ONCE_RW_TAC[GSYM(CONJUNCT2(CONJUNCT2 APPEND))]
 THEN POP_ASSUM SUBST1_TAC
 THEN PURE_ONCE_RW_TAC[GSYM length_append_filter]
 THEN SIMPL);


(*---------------------------------------------------------------------------
 * Unused lemmas about permutations
 *
 * val papp1 = Q.prove`!(h:'a) A B C. 
 *                      permutation (APPEND (h::A) (APPEND B C)) 
 *                                  (APPEND A (APPEND (h::B) C))`
 * (RW_TAC[APPEND] THEN REPEAT GEN_TAC 
 *   THEN MATCH_MP_TAC cons_permutation 
 *   THEN RW_TAC[permutation_refl]);
 * 
 * 
 * val papp2 = Q.prove
 * `!(h:'a) A B C. permutation (APPEND (h::A) (APPEND B C)) 
 *                             (APPEND A (APPEND B (h::C)))`
 * (RW_TAC[APPEND] THEN REPEAT GEN_TAC 
 *   THEN RW_TAC[APPEND_ASSOC]
 *   THEN MATCH_MP_TAC cons_permutation
 *   THEN RW_TAC[permutation_refl]);
 * 
 * 
 * val papp3 = Q.prove
 * `!(h:'a) A B C L. permutation (APPEND (h::A) (APPEND B C)) L 
 *                    =
 *                    permutation (APPEND A (APPEND (h::B) C)) L`
 * (REPEAT GEN_TAC THEN EQ_TAC THEN DISCH_TAC THEN 
 *   MATCH_MP_TAC (ONCE_RW_RULE[transitive_def] permutation_trans) THEN
 *   POP_ASSUM (fn th => EXISTS_TAC(rand(rator(concl th))) THEN RW_TAC[th])
 *   THENL[ONCE_RW_TAC[permutation_sym],ALL_TAC] THEN MATCH_ACCEPT_TAC papp1);
 * 
 * 
 * val papp4 = Q.prove
 * `!(h:'a) A B C L. permutation (APPEND (h::A) (APPEND B C)) L 
 *                    =
 *                    permutation (APPEND A (APPEND B (h::C))) L`
 * (REPEAT GEN_TAC THEN EQ_TAC THEN DISCH_TAC THEN 
 *  MATCH_MP_TAC (ONCE_RW_RULE[transitive_def] permutation_trans) THEN
 *   POP_ASSUM (fn th => EXISTS_TAC(rand(rator(concl th))) THEN RW_TAC[th])
 *   THENL[ONCE_RW_TAC[permutation_sym],ALL_TAC] THEN MATCH_ACCEPT_TAC papp2);
 *
 *
 *---------------------------------------------------------------------------*)

export_theory();
html_theory"-";
