(*---------------------------------------------------------------------------
 * Select the nth smallest element in a list. The following algorithm does 
 * it in (worst case) time proportional to the length of the list. Due to
 * Blum, Floyd, Pratt, Rivest, and Tarjan.
 *---------------------------------------------------------------------------*)

new_theory"select";
cons_path "../" theory_path;
new_parent"qsort";
new_parent"nth";
new_parent"div";
use"../utils.sml";


(*---------------------------------------------------------------------------
 * Import theory bindings 
 *---------------------------------------------------------------------------*)
val PAIR_EQ = theorem"pair" "PAIR_EQ";
val CURRY_DEF = definition"pair" "CURRY_DEF";
val SND = theorem"pair" "SND";

val o_DEF = definition"combin" "o_DEF";

val transitive_def = definition"TC" "transitive_def";

val less_trans = theorem"arithmetic" "LESS_TRANS";
val num_CASES = theorem"arithmetic" "num_CASES";

val LENGTH = definition"list" "LENGTH";
val MAP = definition"list" "MAP";
val HD = definition"list" "HD";
val TL = definition"list" "TL";
val FLAT = definition"list" "FLAT";
val LENGTH_CONS = theorem"list" "LENGTH_CONS";
val LENGTH_MAP = theorem"list" "LENGTH_MAP";
val list_CASES = theorem"list" "list_CASES";

val mem_def = definition"kls_list" "mem_def";
val filter_def = definition"kls_list" "filter_def";
val APPEND = theorem"kls_list" "APPEND";
val append_infix = definition"kls_list" "append_infix";
val length_append_distrib = theorem"kls_list" "length_append_distrib";
val mem_of_append = theorem"kls_list" "mem_of_append";

val permutation_def = definition"permutation" "permutation_def";
val permutation_refl = theorem"permutation" "permutation_refl";
val permutation_sym = theorem "permutation" "permutation_sym";
val permutation_trans = theorem"permutation" "permutation_trans";
val permutation_append = theorem"permutation" "permutation_append";
val cons_permutation = theorem"permutation" "cons_permutation";
val permutation_cons_iff = theorem "permutation" "permutation_cons_iff";
val cons_permutation = theorem "permutation" "cons_permutation";
val permutation_cong = theorem"permutation" "permutation_cong";
val permutation_split = Q.GEN`P`(theorem"permutation" "permutation_split");
val permutation_length = theorem"permutation" "permutation_length";
val append_permutation_sym = theorem"permutation" "append_permutation_sym";

val mem_nth = theorem"nth" "mem_nth";

val quotient_less = theorem"div" "quotient_less";
val slash_eq0_numerator = theorem"div" "slash_eq0_numerator";
val slash_numerator_pos = theorem"div" "slash_numerator_pos";

val qsort_mem_stable = theorem"qsort" "qsort_mem_stable";
val qsort_permutation = theorem"qsort" "qsort_permutation";

(*---------------------------------------------------------------------------
 * Useful tactics
 *---------------------------------------------------------------------------*)
fun Rdefine thml = 
rfunction (Prim.postprocess{WFtac = WF_TAC[],
                       terminator = terminator, 
                       simplifier = tc_simplifier thml}) RW_RULE;

val LIST_INDUCT_TAC = INDUCT_THEN (theorem"list" "list_INDUCT") MP_TAC;

fun TRANS_TAC trans_thm = MATCH_MP_TAC(PURE_RW_RULE[transitive_def] trans_thm);
fun NTAC n tac = funpow n (curry (op THEN) tac) ALL_TAC;
val ARITH = EQT_ELIM o ARITH_CONV o Term;
val ARITH_TAC = CONV_TAC ARITH_CONV;
val LET_TAC = CONV_TAC (DEPTH_CONV let_CONV);

local open RW
      val pss = RW.add_rws (RW.Implicit.implicit_simpls())
            [definition "list" "LENGTH",
             definition"list" "TL",
             definition"list" "HD",
             definition"kls_list" "filter_def",
             theorem"kls_list" "APPEND",
             permutation_refl,
             theorem"pair" "PAIR_EQ", 
             theorem"arithmetic" "ADD_CLAUSES",
             theorem"arithmetic" "MULT_CLAUSES",
             theorem "arithmetic" "LEFT_ADD_DISTRIB",
             theorem "arithmetic" "RIGHT_ADD_DISTRIB",
             theorem"arithmetic" "LESS_EQ_REFL",
             theorem"arithmetic" "LESS_MONO_EQ",
             theorem"prim_rec" "LESS_REFL", 
             theorem"prim_rec" "NOT_LESS_0", 
             theorem"prim_rec" "LESS_SUC_REFL",
             theorem"prim_rec" "INV_SUC_EQ",
             theorem"num" "NOT_SUC",
             theorem"prim_rec" "LESS_0"]
      val RWTAC = REWRITE_TAC Fully (Simpls(pss,[]),Context([],ADD),
                                     Congs[],Solver std_solver)
in
val SIMPL = RWTAC THEN TRY(CHANGED_TAC BETA_TAC THEN RWTAC)
end;


(* An arithmetic solver *)
fun ARW_TAC thms = 
REWRITE_TAC Fully 
  (Simpls(std_simpls,thms), Context([],ADD),
    Congs[IMP_CONG],
    Solver (fn _ => fn _ => fn tm => 
            let val th = RW_CONV[LENGTH] tm
                val rhs = #rhs(dest_eq(concl th))
            in EQT_ELIM(TRANS th (ARITH_CONV rhs)) end));

(*---------------------------------------------------------------------------
 * Useful theorems. These are less ad hoc than the lemmas that are also 
 * scattered about, and are candidates for including in the system.
 *---------------------------------------------------------------------------*)

val ABS_PAIR_THM = 
   GSYM(GEN_ALL
    (EXISTS(Term`?(q:'a) (r:'b). (q,r) = (x:'a#'b)`, Term`FST(x:'a#'b)`)
      (EXISTS(Term`?r:'b. (FST x,r) = (x:'a#'b)`, Term`SND(x:'a#'b)`) 
             (SPEC_ALL (theorem"pair" "PAIR")))));

val not_cons_nil_eq = Q.prove`!l:'a list. (!h t. ~(l=h::t)) = (l=[])`
(GEN_CASES_TAC (theorem"list" "list_CASES") THEN SIMPL
 THEN CONV_TAC NNF_CONV THEN MAP_EVERY Q.EXISTS_TAC[`h`,`t`] THEN SIMPL);

val list_lem0 = Q.prove
`!l (f:'a list->'b list). 
  0<LENGTH l ==>
  (!l1. LENGTH (f l1) = LENGTH l1) ==> (LENGTH(HD(MAP f l)) = LENGTH(HD l))`
(LIST_INDUCT_TAC THEN RW_TAC[definition"list" "MAP"] THEN SIMPL);

val mem_flat = Q.prove
`!l (x:'a). 0<LENGTH l /\ mem x (HD l) ==> mem x (FLAT l)`
(GEN_CASES_TAC list_CASES THEN SIMPL THEN RW_TAC[FLAT,mem_of_append]);

val MAPtwice = Q.prove
`!l (f:'b->'c) (g:'a->'b). MAP f (MAP g l) = MAP (f o g) l`
(LIST_INDUCT_TAC THEN RW_TAC[MAP,o_DEF] THEN SIMPL);

val mem_map_flat = Q.prove
`!L (f:'a list->'a) (x:'a). 
    (!l. mem (f l) l) /\ mem x (MAP f L) ==> mem x (FLAT L)`
(LIST_INDUCT_TAC THEN RW_TAC[FLAT,MAP,mem_of_append,mem_def]
  THEN REPEAT STRIP_TAC THENL[ALL_TAC, RES_TAC] THEN ASM_RW_TAC[]);

(*---------------------------------------------------------------------------
 * Let's go! First of all, something to divide a list into chunks of length 5.
 *---------------------------------------------------------------------------*)
val quints_def =
 Rdefine[definition"list" "LENGTH"]
   `measure LENGTH`
    `(quints(a::b::c::d::e::f::rst) = [a;b;c;d;e]::quints(f::rst)) /\
     (quints (x:'a list) = [x])`;


val lem = Q.prove
`!L:'a list. 1 < LENGTH L ==> ?h1 h2 l1. L = h1::h2::l1`
(GEN_CASES_TAC (theorem"list" "list_CASES")
 THEN RW_TAC[LENGTH]
 THENL[ CONV_TAC ARITH_CONV, 
        Q.ID_SPEC_TAC`t` 
         THEN GEN_CASES_TAC (theorem"list" "list_CASES")
         THEN RW_TAC[LENGTH]
         THENL [CONV_TAC ARITH_CONV,
                DISCH_THEN (fn _ => MAP_EVERY Q.EXISTS_TAC [`h`,`h'`,`t'`])
                 THEN RW_TAC[]]]);


val quints_length = Q.prove
`!L:'a list. 1 < LENGTH L ==> LENGTH(quints L) < LENGTH L`
(GEN_TAC THEN DISCH_THEN (STRIP_ASSUME_TAC o MATCH_MP lem)
  THEN POP_ASSUM SUBST1_TAC
  THEN MAP_EVERY Q.ID_SPEC_TAC[`h1`,`h2`,`l1`]
  THEN REC_INDUCT_TAC (#induction quints_def)
  THEN RW_TAC[LENGTH, #rules quints_def]
  THEN REPEAT CONJ_TAC
  THEN TRY (CONV_TAC ARITH_CONV)
  THEN RW_TAC[theorem"arithmetic" "LESS_MONO_EQ"]
  THEN REPEAT STRIP_TAC
  THEN funpow 4 (curry (op THEN) 
          (MATCH_MP_TAC (EQT_ELIM(ARITH_CONV(Term`x<y ==> x < SUC y`)))))
           ALL_TAC
  THEN ASM_RW_TAC[]);


val quints_length_nonzero = Q.prove
`!L:'a list. 0 < LENGTH(quints L)`
(PROGRAM_TAC{induction = #induction quints_def, rules = #rules quints_def}
  THEN RW_TAC[LENGTH]
  THEN CONV_TAC ARITH_CONV);


val slash_eq0 = theorem"div" "slash_eq0";
val slash_plus = theorem"div" "slash_plus";

val length_quints0 = Q.prove
`!L:'a list. 
   LENGTH(quints L) = list_case 1 (\h t. SUC(LENGTH t/5)) L`
(PROGRAM_TAC{induction = #induction quints_def, rules = #rules quints_def}
  THEN SIMPL THEN ARW_TAC(slash_eq0::map Q.num_CONV [`1`,`5`])
  THEN ASM_RW_TAC[] THEN BETA_TAC
  THEN RW_TAC(GSYM slash_plus::map Q.num_CONV[`1`,`2`,`3`,`4`,`5`])
  THEN SIMPL);

val length_quints = Q.prove
`(LENGTH(quints []:'a list list)        = 1) /\ 
  !(h:'a) t. LENGTH(quints(h::t)) = 1+ LENGTH t/5`
(RW_TAC[length_quints0,Q.num_CONV`1`] THEN SIMPL);

val quints_base = Q.prove
`!l:'a list. 0<LENGTH l /\ LENGTH l<6 ==> (LENGTH(HD(quints l)) = LENGTH l)`
(PROGRAM_TAC{induction = #induction quints_def, rules = #rules quints_def}
  THEN SIMPL THEN NTAC 2 (POP_ASSUM MP_TAC) THEN SIMPL THEN ARITH_TAC);

val mem_quints_length = Q.prove
`!L (l:'a list). mem l (quints L) ==> LENGTH l< 6`
(PROG_TAC{induction = #induction quints_def, rules = #rules quints_def}
  THEN RULE_ASSUM_TAC (RW_RULE[mem_def]) 
  THEN ASM_RW_TAC[LENGTH] THEN TRY ARITH_TAC
  THEN POP_ASSUM (DISJ_CASES_THEN ASSUME_TAC)
  THENL[ASM_RW_TAC[LENGTH] THEN ARITH_TAC, RES_TAC]);

val mem_quints_length0 = Q.prove
`!L (l:'a list). mem l (quints L) /\ 0<LENGTH L ==> 0<LENGTH l`
(PROG_TAC{induction = #induction quints_def, rules = #rules quints_def}
  THEN RULE_ASSUM_TAC (RW_RULE[mem_def]) 
  THEN ASM_RW_TAC[LENGTH] THEN TRY ARITH_TAC
  THENL[ASSUM_LIST (fn [_,disj,_] => DISJ_CASES_THEN ASSUME_TAC disj) THENL
         [ASM_RW_TAC[],FIRST_ASSUM MATCH_MP_TAC THEN ASM_RW_TAC[]] THEN SIMPL,
        RULE_ASSUM_TAC(RW_RULE[LENGTH]) THEN ASM_RW_TAC[]]);

val flatten_quints = Q.prove
`!l:'a list. FLAT(quints l) = l`
(PROGRAM_TAC{induction = #induction quints_def, rules = #rules quints_def}
  THEN RW_TAC[FLAT] THEN SIMPL THEN ASM_RW_TAC[]);

val mem_quints_lem = Q.prove
`!l2 l1. mem l1 (quints l2) ==> !x:'a. mem x l1 ==> mem x l2`
(PROG_TAC{induction = #induction quints_def, rules = #rules quints_def}
   THEN REPEAT (POP_ASSUM MP_TAC) THEN RW_TAC[mem_def]
 THEN DISCH_TAC THEN DISCH_THEN (DISJ_CASES_THEN2 SUBST1_TAC ASSUME_TAC)
 THEN RW_TAC[mem_def]
 THENL[MATCH_ACCEPT_TAC(Q.TAUT_CONV`v1 \/ v2 \/ v3 \/ v4 \/ v5 
                                   ==> v1 \/ v2 \/ v3 \/ v4 \/ v5 \/ v6`),
       DISCH_TAC THEN RES_TAC THEN ASM_RW_TAC[]]);

(*---------------------------------------------------------------------------
 * Special purpose median: in the context that we call it, we know that the 
 * list is sorted and has length at least 1 and at most 5. Wildcards would
 * be nice here.
 *---------------------------------------------------------------------------*)
val median5_def =
 Rfunction`Empty`
   `(median5[a;b;m;d;e] = m) /\
    (median5[a;b;m;d] = m) /\
    (median5[a;m;c] = m) /\
    (median5[a;m] = m) /\
    (median5[m:'a] = m)`;
    
val mem_median = Q.prove
`!l:'a list. 0<LENGTH l /\ LENGTH l<6 ==> mem (median5 l) l`
(PROG_TAC{induction = #induction median5_def, rules = #rules median5_def}
 THEN RW_TAC[mem_def] THENL
 [ RULE_ASSUM_TAC(RW_RULE[LENGTH]) THEN IMP_RES_TAC(ARITH`~(x<x)`),
   POP_ASSUM MP_TAC 
    THEN RW_TAC(LENGTH::map Q.num_CONV[`1`,`2`,`3`,`4`,`5`,`6`]) THEN SIMPL]);

val mem_median5_qsort = Q.prove
`!l. 0 < LENGTH l /\ LENGTH l < 6 ==> mem ((median5 o CURRY qsort $<=) l) l`
(REPEAT STRIP_TAC THEN RW_TAC[o_DEF,CURRY_DEF] THEN BETA_TAC THEN
 MATCH_MP_TAC(RW_RULE[qsort_mem_stable](Q.ISPECL[`qsort($<=,l)`]mem_median))
 THEN SUBST1_TAC(GSYM(MATCH_MP permutation_length 
                    (Q.ISPECL[`$<=`,`l:num list`]qsort_permutation)))
 THEN ASM_RW_TAC[]);



(*---------------------------------------------------------------------------
 * Split a list into 3: those smaller than "m", those greater, and those
 * equal. Keep track of the multiplicities of each of these lists.
 *---------------------------------------------------------------------------*)
val part3_def =
 Rdefine[definition"list" "LENGTH"]
   `measure (LENGTH o FST o SND)`
     `(part3(m:num,[],p1,p2,p3) = (p1,p2,p3)) /\
      (part3(m,h::t,(l1,n1),(l2,n2),(l3,n3)) =
         ((h<m) => part3(m,t,(h::l1,n1+1),(l2,n2),(l3,n3)) 
        | (m<h) => part3(m,t,(l1,n1),(h::l2,n2+1),(l3,n3)) 
        |          part3(m,t,(l1,n1),(l2,n2),(h::l3,n3+1))))`;



(*---------------------------------------------------------------------------
 * Now 3 boring lemmas about part3. They could be mushed into one 
 * boring lemma.
 * 
 *                          One.
 *---------------------------------------------------------------------------*)
val part3_lower = Q.prove
`!m l l1 n1 l2 n2 l3 n3 lower m1 upper m2 middle m3.
  (((lower,m1), (upper,m2), (middle,m3)) = part3(m,l,(l1,n1),(l2,n2),(l3,n3)))
  ==>
  permutation lower (APPEND l1 (filter (\y.y<m) l)) /\
  (m1 = n1 + LENGTH (filter (\y.y<m) l))`
(PROG_TAC{induction = #induction part3_def, rules = #rules part3_def}
THENL
 [ POP_ASSUM MP_TAC THEN SIMPL
     THEN DISCH_THEN (CONJUNCTS_THEN2 (SUBST1_TAC o SYM) (K ALL_TAC))
     THEN SIMPL,

   POP_ASSUM MP_TAC THEN SIMPL
     THEN DISCH_THEN (CONJUNCTS_THEN2 (SUBST1_TAC o SYM) (K ALL_TAC))
     THEN SIMPL,

   SIMPL 
     THEN Q.UNDISCH_TAC`h<m` THEN SIMPL THEN DISCH_TAC (* ASM_RW_TAC bug *)
     THEN TRANS_TAC permutation_trans
     THEN Q.EXISTS_TAC`h::APPEND l1 (filter (\y. y < m) t)`
     THEN CONJ_TAC
     THENL [ RES_THEN MP_TAC,  MATCH_MP_TAC cons_permutation]
     THEN SIMPL,

   RES_THEN (TRY o SUBST1_TAC)
     THEN SIMPL
     THEN Q.UNDISCH_TAC`h<m` THEN SIMPL (* ASM_RW_TAC bug *)
     THEN CONV_TAC ARITH_CONV,

   SIMPL
     THEN Q.UNDISCH_TAC`~(h<m)` THEN SIMPL (* ASM_RW_TAC bug *)
     THEN ASM_RW_TAC[],

   RES_THEN (TRY o SUBST1_TAC)
     THEN SIMPL
     THEN Q.UNDISCH_TAC`~(h<m)` THEN SIMPL, (* ASM_RW_TAC bug *)

   SIMPL
     THEN Q.UNDISCH_TAC`~(h<m)` THEN SIMPL (* ASM_RW_TAC bug *)
     THEN ASM_RW_TAC[],

   RES_THEN (TRY o SUBST1_TAC)
     THEN SIMPL
     THEN Q.UNDISCH_TAC`~(h<m)` THEN SIMPL (* ASM_RW_TAC bug *)
 ]);



(*---------------------------------------------------------------------------
 * 
 *                            Two.
 * 
 *---------------------------------------------------------------------------*)
val part3_upper = Q.prove
`!m l l1 n1 l2 n2 l3 n3 lower m1 upper m2 middle m3.
  (((lower,m1), (upper,m2), (middle,m3)) = part3(m,l,(l1,n1),(l2,n2),(l3,n3)))
  ==>
  permutation upper (APPEND l2 (filter (\y.y>m) l)) /\
  (m2 = n2 + LENGTH (filter (\y.y>m) l))`
(PROG_TAC{induction = #induction part3_def, rules = #rules part3_def}
THENL
 [ POP_ASSUM MP_TAC THEN SIMPL
     THEN DISCH_THEN(CONJUNCTS_THEN2(K ALL_TAC) (SUBST1_TAC o SYM o CONJUNCT1))
     THEN SIMPL,

   POP_ASSUM MP_TAC THEN SIMPL
     THEN DISCH_THEN(CONJUNCTS_THEN2(K ALL_TAC) (SUBST1_TAC o SYM o CONJUNCT1))
     THEN SIMPL,

   SIMPL
     THEN RES_THEN MP_TAC THEN DISCH_THEN (K ALL_TAC)
     THEN DISCH_THEN (fn th => TRANS_TAC permutation_trans THEN 
            Q.EXISTS_TAC`APPEND l2 (filter (\y. y > m) t)` THEN RW_TAC[th])
     THEN MATCH_MP_TAC permutation_cong THEN SIMPL
     THEN COND_CASES_TAC
     THENL [ IMP_RES_TAC(EQT_ELIM(ARITH_CONV(Term`x<y ==> x>y ==> F`))),
             SIMPL
           ],

   RES_THEN (TRY o SUBST1_TAC)
     THEN SIMPL
     THEN IMP_RES_THEN (fn th => RW_TAC[th])
           (EQT_ELIM(ARITH_CONV(Term`h<m ==> ~(h>m)`))),

   SIMPL
     THEN IMP_RES_THEN (fn th => RW_TAC[th])
           (EQT_ELIM(ARITH_CONV(Term`m<h ==> h>m`)))
     THEN RES_THEN MP_TAC THEN DISCH_THEN (K ALL_TAC)
     THEN DISCH_THEN (fn th => TRANS_TAC permutation_trans THEN 
          Q.EXISTS_TAC`APPEND (h::l2) (filter (\y.y>m) t)` THEN RW_TAC[th])
     THEN SIMPL
     THEN MATCH_MP_TAC cons_permutation THEN SIMPL,

   RES_THEN (TRY o SUBST1_TAC)
     THEN SIMPL
     THEN IMP_RES_THEN (fn th => RW_TAC[th] THEN SIMPL)
           (EQT_ELIM(ARITH_CONV(Term`m<h ==> h>m`)))
     THEN CONV_TAC ARITH_CONV,

   SIMPL
     THEN IMP_RES_THEN (fn th => RW_TAC[th])
           (EQT_ELIM(ARITH_CONV(Term`~(m<h) ==> ~(h>m)`)))
     THEN ASM_RW_TAC[],

   RES_THEN (TRY o SUBST1_TAC)
     THEN SIMPL
     THEN IMP_RES_THEN (fn th => RW_TAC[th])
           (EQT_ELIM(ARITH_CONV(Term`~(m<h) ==> ~(h>m)`)))
     THEN ASM_RW_TAC[]
 ]);


(*---------------------------------------------------------------------------
 * 
 *                              Three.
 * 
 *---------------------------------------------------------------------------*)
val part3_middle = Q.prove
`!m l l1 n1 l2 n2 l3 n3 lower m1 upper m2 middle m3.
  (((lower,m1), (upper,m2), (middle,m3)) = part3(m,l,(l1,n1),(l2,n2),(l3,n3)))
  ==>
  permutation middle (APPEND l3 (filter ($=m) l)) /\
  (m3 = n3 + LENGTH (filter ($=m) l))`
(PROG_TAC{induction = #induction part3_def, rules = #rules part3_def}
THENL
 [ POP_ASSUM MP_TAC THEN SIMPL
     THEN DISCH_THEN(CONJUNCTS_THEN2(K ALL_TAC) (SUBST1_TAC o SYM o CONJUNCT2))
     THEN SIMPL,

   POP_ASSUM MP_TAC THEN SIMPL
     THEN DISCH_THEN(CONJUNCTS_THEN2(K ALL_TAC) (SUBST1_TAC o SYM o CONJUNCT2))
     THEN SIMPL,

   SIMPL
     THEN IMP_RES_THEN (fn th => RW_TAC[th])
           (EQT_ELIM(ARITH_CONV(Term`h<m ==> ~(m=h)`)))
     THEN RES_THEN ACCEPT_TAC,

   RES_THEN (TRY o SUBST1_TAC)
     THEN SIMPL
     THEN IMP_RES_THEN (fn th => RW_TAC[th])
           (EQT_ELIM(ARITH_CONV(Term`h<m ==> ~(m=h)`))),

   SIMPL
     THEN IMP_RES_THEN (fn th => RW_TAC[th])
           (EQT_ELIM(ARITH_CONV(Term`m<h ==> ~(m=h)`)))
     THEN RES_THEN ACCEPT_TAC,

   RES_THEN (TRY o SUBST1_TAC)
     THEN SIMPL
     THEN IMP_RES_THEN (fn th => RW_TAC[th])
           (EQT_ELIM(ARITH_CONV(Term`m<h ==> ~(m=h)`))),

   SIMPL
     THEN IMP_RES_TAC (EQT_ELIM(ARITH_CONV(Term`~(h<m) ==> ~(m<h) ==> (m=h)`)))
     THEN POP_ASSUM SUBST1_TAC
     THEN SIMPL
     THEN RES_THEN MP_TAC THEN DISCH_THEN (K ALL_TAC)
     THEN DISCH_THEN (fn th => TRANS_TAC permutation_trans THEN 
          Q.EXISTS_TAC`APPEND (h::l3) (filter ($= m) t)` THEN RW_TAC[th])
     THEN SIMPL
     THEN MATCH_MP_TAC cons_permutation 
     THEN POP_ASSUM SUBST1_TAC 
     THEN SIMPL,

   RES_THEN (TRY o SUBST1_TAC)
     THEN SIMPL
     THEN IMP_RES_TAC (EQT_ELIM(ARITH_CONV(Term`~(h<m) ==> ~(m<h) ==> (m=h)`)))
     THEN POP_ASSUM SUBST1_TAC THEN SIMPL
     THEN CONV_TAC ARITH_CONV
 ]);

(* Slightly ad hoc theorem *)
val goofy = Q.prove
 `!P Q l. (!x:'a. P x ==> ~Q x) /\ (!x. Q x ==> ~P x)
           ==>
            permutation (APPEND (filter P l) (filter Q l))
                        (filter (\x. P x \/ Q x) l)`
(NTAC 2 GEN_TAC THEN LIST_INDUCT_TAC THEN STRIP_TAC THENL
 [RW_TAC[filter_def,APPEND,permutation_refl],
  GEN_TAC THEN STRIP_TAC THEN RES_TAC THEN RW_TAC[filter_def] THEN BETA_TAC
    THEN REPEAT COND_CASES_TAC THEN RULE_ASSUM_TAC (RW_RULE[])
    THEN ASM_RW_TAC[APPEND,permutation_cons_iff] THEN RES_TAC
    THEN TRY (IMP_RES_THEN MATCH_ACCEPT_TAC (Q.TAUT_CONV`F ==> ANYTHING`))
    THEN ONCE_RW_TAC[permutation_sym] THEN MATCH_MP_TAC cons_permutation
    THEN ONCE_RW_TAC[permutation_sym] THEN ASM_RW_TAC[]]);

(*---------------------------------------------------------------------------
 * Everything one needs to know about part3. The proof would be a lot shorter 
 * using a rewriter that understood equivalence classes.
 *---------------------------------------------------------------------------*)
val part3_correctness = Q.prove
`!m l l1 n1 l2 n2 l3 n3 lower m1 upper m2 middle m3.
  (((lower,m1), (upper,m2), (middle,m3)) = part3(m,l,(l1,n1),(l2,n2),(l3,n3)))
  ==>
  permutation (lower++middle++upper) (l++l1++l2++l3) /\
  (m1+m2+m3 = LENGTH l+n1+n2+n3)`
(REPEAT GEN_TAC THEN DISCH_TAC THEN
  IMP_RES_TAC part3_lower THEN 
   IMP_RES_TAC part3_upper THEN
   IMP_RES_TAC part3_middle 
   THEN Q.SUBGOAL_THEN `permutation l (APPEND (filter (\y. y < m) l)
                                 (APPEND (filter ($= m) l)
                                        (filter (\y. y > m) l)))`ASSUME_TAC
 THENL
 [TRANS_TAC permutation_trans
   THEN Q.EXISTS_TAC`APPEND (filter (\y.y<m) l) (filter (~ o \y.y<m) l)`
   THEN RW_TAC[permutation_split]
   THEN MATCH_MP_TAC permutation_cong
   THEN RW_TAC[permutation_refl]
   THEN RW_TAC[definition"combin" "o_DEF"] THEN BETA_TAC
   THEN ONCE_RW_TAC[permutation_sym]
   THEN RW_TAC[ARITH`~(x<y) = (x=y) \/ x>y`]
   THEN MATCH_MP_TAC (RW_RULE[Q.prove`(\x:'a.x=m) = $=m` 
   (CONV_TAC FUN_EQ_CONV THEN BETA_TAC THEN GEN_TAC THEN EQ_TAC THEN RW_TAC[])]
    (BETA_RULE(Q.ISPECL[`\y:num.y=m`,`\y.y>m`] goofy)))
   THEN ARITH_TAC,
 CONJ_TAC THENL
 [(* Get rid of equalities, since they were only used in other half of proof *)
  ASSUM_LIST (fn [_,b,_,d,_,f,_,_] => MAP_EVERY 
    (fn th => UNDISCH_TAC (concl th) THEN DISCH_THEN (K ALL_TAC)) [b,d,f])
   THEN TRANS_TAC permutation_trans
   THEN Q.EXISTS_TAC`(APPEND (filter (\y. y < m) l)
                     (APPEND (filter ($= m) l) 
                             (filter (\y. y > m) l))) ++l1++l2++l3`
   THEN RW_TAC[append_infix] THEN CONJ_TAC
  THENL
  [(*2.1.1*)
   TRANS_TAC permutation_trans
   THEN Q.EXISTS_TAC`APPEND (APPEND l1 (filter (\y. y < m) l))
                       (APPEND (APPEND l2 (filter (\y. y > m) l))
                               (APPEND l3 (filter ($= m) l)))` THEN CONJ_TAC
   THENL(*2.1.1.1*)
   [ MATCH_MP_TAC permutation_cong THEN ASM_RW_TAC[] 
      THEN MATCH_MP_TAC append_permutation_sym 
      THEN ASM_CRW_TAC[permutation_cong],
     (*2.1.1.2*)
     ONCE_RW_TAC[permutation_sym] THEN MATCH_MP_TAC append_permutation_sym
      THEN RW_TAC[GSYM (theorem"list" "APPEND_ASSOC")]
      THEN MATCH_MP_TAC permutation_cong THEN RW_TAC[permutation_refl]
      THEN ONCE_RW_TAC[permutation_sym]THEN MATCH_MP_TAC append_permutation_sym
      THEN RW_TAC[GSYM (theorem"list" "APPEND_ASSOC")]
      THEN MATCH_MP_TAC permutation_cong THEN RW_TAC[permutation_refl]
      THEN MATCH_MP_TAC append_permutation_sym 
      THEN RW_TAC[GSYM (theorem"list" "APPEND_ASSOC")]
      THEN MATCH_MP_TAC permutation_cong THEN RW_TAC[permutation_refl]
      THEN ONCE_RW_TAC[permutation_sym]THEN MATCH_MP_TAC append_permutation_sym
      THEN RW_TAC[GSYM (theorem"list" "APPEND_ASSOC")] 
      THEN MATCH_MP_TAC permutation_cong THEN RW_TAC[permutation_refl]
      THEN MATCH_MP_TAC append_permutation_sym THEN RW_TAC[permutation_refl]],
  (*2.1.2*)
  MATCH_MP_TAC permutation_cong THEN RW_TAC[permutation_refl] 
    THEN ONCE_RW_TAC[permutation_sym] THEN ASM_RW_TAC[]],
 (*2.2*)
 IMP_RES_THEN SUBST1_TAC permutation_length
  THEN ASM_RW_TAC[length_append_distrib]
  THEN ARITH_TAC]]);

val mem_length = Q.prove
`!l (x:'a). mem x l ==> ?y. LENGTH l = SUC y`
(LIST_INDUCT_TAC THEN SIMPL THEN RW_TAC[definition"kls_list" "mem_def"]);


(*---------------------------------------------------------------------------
 * Seems like the proof should be simpler, with the lemmas we've already 
 * got...
 *---------------------------------------------------------------------------*)
val mem_part3 = Q.prove
`!x l lower m1 upper m2 middle m3.
 mem x l /\
 (((lower,m1), (upper,m2), (middle,m3)) = part3(x,l,([],0),([],0),([],0)))
 ==> LENGTH lower < LENGTH l /\
     LENGTH upper < LENGTH l`
(REPEAT GEN_TAC THEN STRIP_TAC 
  THEN IMP_RES_THEN MP_TAC part3_correctness THEN DISCH_THEN (K ALL_TAC)
  THEN RW_TAC[append_infix] THEN SIMPL
  THEN DISCH_THEN (MP_TAC o MATCH_MP permutation_length)
  THEN RW_TAC[length_append_distrib]
  THEN DISCH_THEN (SUBST1_TAC o SYM)
  THEN RW_TAC[ARITH`x<x+z = 0<z`, ARITH`x<y+z+x = 0<y+z`]
  THEN IMP_RES_THEN MP_TAC part3_middle THEN SIMPL
  THEN DISCH_THEN (K ALL_TAC) 
  THEN DISCH_THEN (MP_TAC o MATCH_MP permutation_length)
  THEN DISCH_THEN SUBST1_TAC
  THEN Q.SUBGOAL_THEN`!l (x:num). mem x l ==> ?h t. filter ($=x) l = h::t`
         (IMP_RES_THEN (REPEAT_TCL CHOOSE_THEN SUBST1_TAC)) THENL
  [REPEAT GEN_TAC THEN DISCH_THEN (fn th =>
     MAP_EVERY Q.EXISTS_TAC[`x'`,`TL(filter ($=x') l')`] 
    THEN SIMPL THEN MP_TAC th) THEN MAP_EVERY Q.ID_SPEC_TAC[`x'`,`l'`]
    THEN REPEAT (POP_ASSUM (K ALL_TAC))
    THEN LIST_INDUCT_TAC THEN RW_TAC[definition"kls_list" "mem_def"] 
    THEN SIMPL THEN REPEAT STRIP_TAC THENL
    [ASM_RW_TAC[], COND_CASES_TAC THENL [ASM_RW_TAC[], ONCE_ASM_RW_TAC[]]]
    THEN SIMPL,
   SIMPL THEN ARITH_TAC]);



(*---------------------------------------------------------------------------
 * The "select" algorithm. It's underspecified: it can't be applied to 
 * empty lists, and the first argument has to be less than the length of 
 * the list. It's zero-based: selecting the zeroth element gives the smallest
 * element in the list.
 *---------------------------------------------------------------------------*)

val select_def =
 Rfunction  `measure (LENGTH o SND)`
  `select (n,l) =
      let Q = quints l in 
      let Qlen = LENGTH Q in 
      let sQ = MAP (CURRY qsort $<=) Q 
      in 
      (Qlen = 1) => nth(n, HD sQ)
       | let mom = select(Qlen/2, MAP median5 sQ) in 
         let ((lower,n1),
              (upper,n2),
              (middle,n3)) = part3(mom,l,([],0),([],0),([],0))
         in
            (n1 >= n)    => select(n, lower)
          | (n1+n3 >= n) => mom
          | (* else *)      select(n-(n1+n3), upper)`;


(*---------------------------------------------------------------------------
 * Non-nested termination condition.
 *---------------------------------------------------------------------------*)

val innerTC = Q.prove
`!Q l Qlen sQ.
     (Q = quints l) /\
     (Qlen = LENGTH Q) /\
     (sQ = MAP (CURRY qsort $<=) Q) /\
     ~(Qlen = 1) ==>
     LENGTH (MAP median5 sQ) < LENGTH l`
(RW_TAC[LENGTH_MAP] THEN GEN_TAC THEN GEN_CASES_TAC(theorem"list" "list_CASES")
 THEN REPEAT GEN_TAC THEN SIMPL THENL
 [CONV_TAC NNF_CONV THEN RW_TAC[#rules quints_def,Q.num_CONV`1`] THEN SIMPL,
  RW_TAC[length_quints,Q.num_CONV`1`,Q.num_CONV`5`] THEN 
  DISCH_THEN(fn th => SIMPL THEN MATCH_MP_TAC(theorem"div" "quotient_less")
  THEN CONJ_TAC THEN MP_TAC th) THENL
  [DISCH_THEN (fn th => CCONTR_TAC THEN 
    IMP_RES_THEN(fn th1 => MP_TAC th THEN MP_TAC th1) (ARITH`~(0<x)==>(x=0)`))
    THEN RW_TAC[theorem"list" "LENGTH_NIL",Q.TAUT_CONV`x/\y==>z = x==>y==>z`,
                #rules quints_def] THEN SIMPL,
   DISCH_TAC THEN ARITH_TAC]]);



val select_def1 = RW_RULE[innerTC] (#rules select_def);
val select_ind1 = PROVE_HYP innerTC (#induction select_def);

val th = ISPEC (Term`measure (LENGTH o (SND:num#'a list->'a list))`) 
               (theorem"WF" "WF_INDUCTION_THM");


val ind = CONV_RULE (tc_simplifier[])
                    (RW_RULE[theorem"WF" "WF_measure"] th);

val ind1 = Q.GEN`Q`
(CONV_RULE(DEPTH_CONV GEN_BETA_CONV)
 (DISCH_ALL
   (itlist Q.GEN[`n`,`l`]
     (CONV_RULE(DEPTH_CONV GEN_BETA_CONV)
       (Q.SPEC`(n,l)`
         (UNDISCH(Q.ISPECL[`\(n,l):num#'a list. Q(n,l):bool`] ind)))))));

val ind2 = RW_RULE [] ind1;

val let_lem0 = BETA_RULE(Q.ISPECL
[`\hole:num. (mom=hole) ==> LENGTH(lower:num list)<LENGTH(l:num list)`,
 `quints(MAP median5 sQ):num list list`,
  `\Q:num list list. let Qlen' = LENGTH Q in
     let sQ' = MAP (CURRY qsort $<=) Q in
     (Qlen' = 1) => (nth (Qlen / 2,HD sQ'))
      | (let mom = select (Qlen' / 2,MAP median5 sQ') in
        let ((lower,n1),(upper,n2),middle,n3) =
            part3 (mom,MAP median5 sQ,([],0),([],0),[],0)
        in (n1 >= Qlen / 2)
        => ((measure(LENGTH o SND) (Qlen/2,lower) (Qlen/2,MAP median5 sQ))
            => (select (Qlen / 2,lower)) | (@v. T))
        | ((n1 + n3 >= Qlen / 2) => mom
        | ((measure(LENGTH o SND)(Qlen/2-(n1+n3),upper)(Qlen/2,MAP median5 sQ))
            => (select (Qlen / 2 - (n1 + n3),upper)) | (@v. T))))`]
 PULL_LET);


val let_lem1 = BETA_RULE(Q.ISPECL
[`\hole:num. (mom=hole) ==> LENGTH(lower:num list)<LENGTH(l:num list)`,
 `LENGTH (Q1:num list list)`,
  `\Qlen'. let sQ' = MAP (CURRY qsort $<=) Q1 in
     (Qlen' = 1) => (nth (Qlen / 2,HD sQ'))
      | (let mom = select (Qlen' / 2,MAP median5 sQ') in
        let ((lower,n1),(upper,n2),middle,n3) =
            part3 (mom,MAP median5 sQ,([],0),([],0),[],0)
        in (n1 >= Qlen / 2)
        => ((measure(LENGTH o SND) (Qlen/2,lower) (Qlen/2,MAP median5 sQ))
            => (select (Qlen / 2,lower)) | (@v. T))
        | ((n1 + n3 >= Qlen / 2) => mom
        | ((measure(LENGTH o SND)(Qlen/2-(n1+n3),upper)(Qlen/2,MAP median5 sQ))
            => (select (Qlen / 2 - (n1 + n3),upper)) | (@v. T))))`]
 PULL_LET);


val let_lem2 = BETA_RULE(Q.ISPECL
[`\hole:num. (mom=hole) ==> LENGTH(lower:num list)<LENGTH(l:num list)`,
 `MAP (CURRY qsort $<=) (Q1:num list list)`,
  `\sQ1. (Qlen1 = 1) => (nth (Qlen / 2,HD sQ1))
      | (let mom = select (Qlen1 / 2,MAP median5 sQ1) in
        let ((lower,n1),(upper,n2),middle,n3) =
            part3 (mom,MAP median5 sQ,([],0),([],0),[],0)
        in (n1 >= Qlen / 2)
        => ((measure(LENGTH o SND) (Qlen/2,lower) (Qlen/2,MAP median5 sQ))
            => (select (Qlen / 2,lower)) | (@v. T))
        | ((n1 + n3 >= Qlen / 2) => mom
        | ((measure(LENGTH o SND)(Qlen/2-(n1+n3),upper)(Qlen/2,MAP median5 sQ))
            => (select (Qlen / 2 - (n1 + n3),upper)) | (@v. T))))`]
 PULL_LET);


val let_lem3 = BETA_RULE(Q.ISPECL
[`\hole:num. (mom=hole) ==> LENGTH(lower:num list)<LENGTH(l:num list)`,
 `select (Qlen1 / 2,MAP median5 sQ1)`,
  `\mom. let ((lower,n1),(upper,n2),middle,n3) =
            part3 (mom,MAP median5 sQ,([],0),([],0),[],0)
        in (n1 >= Qlen / 2)
        => ((measure(LENGTH o SND) (Qlen/2,lower) (Qlen/2,MAP median5 sQ))
            => (select (Qlen / 2,lower)) | (@v. T))
        | ((n1 + n3 >= Qlen / 2) => mom
        | ((measure(LENGTH o SND)(Qlen/2-(n1+n3),upper)(Qlen/2,MAP median5 sQ))
            => (select (Qlen / 2 - (n1 + n3),upper)) | (@v. T)))`]
 PULL_LET);

val let_lem4 = BETA_RULE 
(Q.ISPECL
[`\hole:num. (mom=hole) ==> LENGTH(lower:num list)<LENGTH(l:num list)`,
 `part3 (mom1,MAP median5 sQ,([],0),([],0),[],0)`,
  `\(lower:num list) n1 (upper:num list) (n2:num) (middle:num list) n3. 
       (n1 >= Qlen / 2)
        => ((measure(LENGTH o SND) (Qlen/2,lower) (Qlen/2,MAP median5 sQ))
            => (select (Qlen / 2,lower)) | (@v. T))
        | ((n1 + n3 >= Qlen / 2) => mom1
        | ((measure(LENGTH o SND)(Qlen/2-(n1+n3),upper)(Qlen/2,MAP median5 sQ))
            => (select (Qlen / 2 - (n1 + n3),upper)) | (@v. T)))`]
 PULL_LET3X2);

val mem_map_exists = Q.prove
`!L x (f:'a->'b). mem x (MAP f L) ==> ?list. mem list L /\ (x = f list)`
(LIST_INDUCT_TAC THEN RW_TAC[MAP,mem_def] THEN REPEAT STRIP_TAC
 THENL[ASM_RW_TAC[] THEN Q.EXISTS_TAC`h` THEN SIMPL,
       RES_TAC THEN Q.EXISTS_TAC`list` THEN ASM_RW_TAC[]]);
DIE;

g`!Q l Qlen sQ mom lower n1 upper n2 middle n3 n.
    n<LENGTH l /\
    (Q = quints l) /\
    (Qlen = LENGTH Q) /\
    (sQ = MAP (CURRY qsort $<=) Q) /\
    ~(Qlen = 1) /\
    (mom = select (Qlen/2,MAP median5 sQ)) /\
    (((lower,n1),(upper,n2),middle,n3) = part3 (mom,l,([],0),([],0),[],0)) /\
    n1 >= n ==>
    LENGTH lower < LENGTH l`;
  
e(Q.SUBGOAL_THEN`!n l Q Qlen sQ mom lower n1 upper n2 middle n3.
    n<LENGTH l /\
    (Q = quints l) /\
    (Qlen = LENGTH Q) /\
    (sQ = MAP (CURRY qsort $<=) Q) /\
    ~(Qlen = 1) /\
    (mom = select (Qlen/2,MAP median5 sQ)) /\
    (((lower,n1),(upper,n2),middle,n3) =part3 (mom,l,([],0),([],0),[],0)) /\
     n1 >= n ==>
     LENGTH lower < LENGTH l` (fn th => MP_TAC th THEN SIMPL));

e (REC_INDUCT_TAC select_ind1);
e (NTAC 2 GEN_TAC);
e (REPEAT CONJ_TAC);
e (GEN_CASES_TAC ABS_PAIR_THM);
e (PURE_RW_TAC[theorem"pair" "SND", theorem"pair" "FST"]);
e (Q.SPEC_TAC(`r:num list`,`l`)); e (Q.SPEC_TAC(`q:num`,`n`)); 
e (REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC);
e (STRIP_TAC THEN REPEAT GEN_TAC);
e (ONCE_RW_TAC[select_def1]);
e (DISCH_THEN (CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC));

(* let bindings *)
e (RW_TAC[let_lem0] THEN LET_INTRO_TAC);
e (Q.SPEC_TAC(`x:num list list`,`Q1`) THEN GEN_TAC);
e (DISCH_TAC);

e (RW_TAC[let_lem1] THEN LET_INTRO_TAC);
e (Q.SPEC_TAC(`x:num`,`Qlen1`) THEN GEN_TAC);
e (DISCH_TAC);

e (RW_TAC[let_lem2] THEN LET_INTRO_TAC);
e (Q.SPEC_TAC(`x:num list list`,`sQ1`) THEN GEN_TAC);
e (DISCH_TAC);

e COND_CASES_TAC;
(*2.1*)
e (DISCH_THEN SUBST_ALL_TAC);
e (MATCH_MP_TAC (GEN_ALL(DISCH_ALL(CONJUNCT1(UNDISCH(SPEC_ALL mem_part3))))));
e(MAP_EVERY Q.EXISTS_TAC
           [`n3`,`middle`,`n2`,`upper`,`n1`,`nth(Qlen/2,HD sQ1)`]);
e (CONJ_TAC);
(*2.1.1*)
e (Q.SUBGOAL_THEN`!x:num. mem x (HD sQ1) ==> mem x l` MATCH_MP_TAC);
(*2.1.1.1*)
e (GEN_TAC THEN ONCE_ASM_RW_TAC[]);
e (Q.UNDISCH_TAC`Qlen1 = LENGTH (Q1:num list list)` 
   THEN DISCH_THEN SUBST_ALL_TAC);
e(Q.SUBGOAL_THEN`0<LENGTH (Q1:num list list)`(fn th => 
 RW_TAC[MATCH_MP(Q.prove`!l (f:'a->'b). 0<LENGTH l ==> (HD(MAP f l) = f(HD l))`
                   (LIST_INDUCT_TAC THEN SIMPL THEN RW_TAC[MAP,HD])) th]));
(*2.1.1.1*)
e (ASM_RW_TAC[] THEN ARITH_TAC);
(*2.1.1.2*)
e (RW_TAC[CURRY_DEF,qsort_mem_stable]);
e (ONCE_ASM_RW_TAC[]);
e (DISCH_THEN(MP_TAC o MP
      (RW_RULE[quints_length_nonzero]
        (Q.ISPECL[`quints(MAP median5 sQ):num list list`,`x:num`] mem_flat))));
e (RW_TAC[flatten_quints]);
e (ASM_RW_TAC[MAPtwice]);
e (DISCH_THEN ((CHOOSE_THEN MP_TAC) o MATCH_MP mem_map_exists));
e (SIMPL);
e (DISCH_THEN (CONJUNCTS_THEN2 MP_TAC (K ALL_TAC)));
e (DISCH_TAC);
e (IMP_RES_THEN MP_TAC mem_quints_length0);
e (IMP_RES_THEN (fn th => RW_TAC[th]) (ARITH`x<y ==> 0<y`));
e (IMP_RES_TAC mem_quints_length);
e (DISCH_TAC);
e (IMP_RES_THEN MATCH_MP_TAC mem_quints_lem);
e (IMP_RES_TAC mem_median5_qsort);
(*2.1.1.2*)
e (MATCH_MP_TAC mem_nth);
e (Q.SUBGOAL_THEN`LENGTH(HD (sQ1:num list list)) = Qlen` SUBST1_TAC);
(*2.1.1.2.1*)
e (ONCE_ASM_RW_TAC[]);
e (Q.SUBGOAL_THEN`0<LENGTH(Q1:num list list) /\ 
                 !l1. LENGTH(CURRY qsort $<= l1) = LENGTH l1`
(SUBST1_TAC o MATCH_MP(RW_RULE[Q.TAUT_CONV`x==>y==>z = x/\y==>z`] list_lem0)));
(*2.1.1.2.1.1*)
e (ASM_RW_TAC[quints_length_nonzero]);
e (GEN_TAC THEN RW_TAC[CURRY_DEF]);
e (SUBST_TAC[MATCH_MP permutation_length
             (Q.ISPECL[`$<=`,`l1:num list`] qsort_permutation)] THEN REFL_TAC);
(*2.1.1.2.1.2*)
e (ONCE_ASM_RW_TAC[]);
e (Q.SUBGOAL_THEN`0<LENGTH(MAP median5 sQ)/\LENGTH(MAP median5 sQ:num list)<6`
                 (SUBST1_TAC o MATCH_MP quints_base));
(*2.1.1.2.1.2.1*)
e (ASM_RW_TAC[LENGTH_MAP,quints_length_nonzero]);
e (Q.SUBGOAL_THEN
     `LENGTH(quints(l:num list)) = LENGTH(MAP median5 (sQ:num list list))`
     SUBST1_TAC);
(*2.1.1.2.1.2.1.1*)
e (ASM_RW_TAC[LENGTH_MAP]);
(*2.1.1.2.1.2.1.2*)
e (DISJ_CASES_THEN (REPEAT_TCL CHOOSE_THEN SUBST_ALL_TAC)
    (Q.ISPECL[`MAP median5 sQ:num list`] list_CASES)
   THEN RW_TAC[LENGTH] THEN TRY ARITH_TAC);
e (RW_TAC[Q.num_CONV`6`] THEN SIMPL);
e (MATCH_MP_TAC slash_eq0_numerator THEN CONJ_TAC THEN TRY ARITH_TAC);
e (MATCH_MP_TAC(ARITH`!x y.(x+y=x) ==> (y=0)`));
e (Q.EXISTS_TAC`1`);
e (MATCH_MP_TAC(ARITH`!x y z. (x:num = z) /\ (y=z) ==> (x=y)`));
e (Q.EXISTS_TAC`LENGTH(quints(h::t:num list))`);
e (CONJ_TAC);
(*2.1.1.2.1.2.1.2.1*)
e (RW_TAC[length_quints]);
(*2.1.1.2.1.2.1.2.2*)
e (POP_ASSUM (SUBST1_TAC o SYM));
e (ASM_RW_TAC[]);
(*2.1.1.2.1.2.2*)
e (ASM_RW_TAC[LENGTH_MAP]);
(*2.1.1.2.2*)
e (RW_TAC[Q.num_CONV`2`] THEN MATCH_MP_TAC quotient_less);
e (CONJ_TAC THEN TRY ARITH_TAC);
e (ASM_RW_TAC[quints_length_nonzero]);
(*2.1.2*)
e (FIRST_ASSUM ACCEPT_TAC);

(*2.2*) 
(* Now the recursive cases *)
e (RW_TAC[let_lem3] THEN LET_INTRO_TAC);
e (Q.SPEC_TAC(`x:num`,`mom1`) THEN GEN_TAC);
e (DISCH_TAC);
e (RW_TAC[let_lem4] THEN LET_INTRO_TAC);
e (Q.SPEC_TAC(`v1:num list`,`lower1`) THEN GEN_TAC);
e (Q.SPEC_TAC(`v2:num`,`nlower1`) THEN GEN_TAC);
e (Q.SPEC_TAC(`v3:num list`,`upper1`) THEN GEN_TAC);
e (Q.SPEC_TAC(`v4:num`,`nupper1`) THEN GEN_TAC);
e (Q.SPEC_TAC(`v5:num list`,`middle1`) THEN GEN_TAC);
e (Q.SPEC_TAC(`v6:num`,`nmiddle1`) THEN GEN_TAC);
e (DISCH_TAC);

e (CONV_TAC (tc_simplifier[]));
e (COND_CASES_TAC);

(*2.2.1*)
e (Q.SUBGOAL_THEN`LENGTH (lower1:num list) < LENGTH (MAP median5 sQ:num list)`
  (fn th => RW_TAC[th] THEN ASSUME_TAC th));
(*2.2.1.1*)
e (RULE_ASSUM_TAC (RW_RULE[Q.TAUT_CONV`x==>y==>z = x/\y==>z`]
                   o CONV_RULE (REDEPTH_CONV RIGHT_IMP_FORALL_CONV)));

e (SUBST_TAC[SYM(Q.ISPECL[`Qlen/2`,`MAP median5 (sQ:num list list)`] SND)]);
e (FIRST_ASSUM MATCH_MP_TAC);
e SIMPL;
e (MAP_EVERY Q.EXISTS_TAC[`Q1`,`Qlen1`,`sQ1`,`mom1`,
                          `nlower1`,`upper1`,`nupper1`,`middle1`,`nmiddle1`]);
e (ASM_RW_TAC[LENGTH_MAP]);
e (CONJ_TAC);
(*2.2.1.1.1*)
e (Q.SUBGOAL_THEN`1<Qlen`MP_TAC);
(*2.2.1.1.1.1*)
e (Q.UNDISCH_TAC`~(Qlen=1)`);
e (ASM_RW_TAC[]);
e (MP_TAC (Q.ISPECL[`l:num list`] quints_length_nonzero));
e ARITH_TAC;
(*2.2.1.1.1.2*)
e (ASM_RW_TAC[]);
e (DISJ_CASES_THEN2 SUBST1_TAC (REPEAT_TCL CHOOSE_THEN SUBST1_TAC)
    (Q.ISPECL[`l:num list`] list_CASES) THEN RW_TAC[length_quints]);
(*2.2.1.1.1.2.1*)
e SIMPL;
(*2.2.1.1.1.2.2*)
e (RW_TAC[Q.num_CONV`1`,Q.num_CONV`5`] THEN SIMPL);
e (DISCH_THEN (fn th => MATCH_MP_TAC quotient_less THEN 
  CONJ_TAC THEN TRY ARITH_TAC THEN 
  MATCH_MP_TAC slash_numerator_pos THEN Q.EXISTS_TAC`SUC 4` THEN MP_TAC th)
  THEN ARITH_TAC);
(*2.2.1.1.2*)
e (SUBST_TAC[Q.num_CONV`2`] THEN MATCH_MP_TAC quotient_less);
e (RW_TAC[quints_length_nonzero] THEN ARITH_TAC);
(*2.2.1.2*)
e (DISCH_THEN SUBST_ALL_TAC);
(*2.2.2*)

(*2.2.3*)
(*2.2.4*)
(*2.2.5*)

Q.E.D.
(*----------------------------------------------------------------------------
g`!Q l Qlen sQ mom lower n1 upper n2 middle n3 n.
     (Q = quints l) /\
     (Qlen = LENGTH Q) /\
     (sQ = MAP (CURRY qsort $<=) Q) /\
     ~(Qlen = 1) /\
     (mom = select (Qlen DIV 2,MAP median5 sQ)) /\
     (((lower,n1),(upper,n2),middle,n3) = part3 (mom,l,([],0),([],0),[],0)) /\
     ~(n1 >= n) /\
     ~(n1 + n3 >= n) ==>
     LENGTH upper < LENGTH l`;
  

tgoal select_def;
e (RW_TAC[innerTC]);;



(**
g`(!Q:num#'a list -> bool.(!x.
         (!y. LENGTH (SND y) < LENGTH (SND x) ==> Q (FST y,SND y)) ==>
         Q (FST x,SND x)) ==>
       !n l. Q (n,l))
  =
 (!Q:num#'a list -> bool.
   (!n l. (!n1 l1. LENGTH l1 < LENGTH l ==> Q (n1,l1)) ==> Q (n,l)) 
    ==> !n l. Q (n,l))`;
e (EQ_TAC);
(*1*)
e STRIP_TAC;
e (GEN_TAC THEN STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC);
e (GEN_TAC THEN STRIP_ASSUME_TAC (Q.ISPECL[`x:num#'a list`]ABS_PAIR_THM));
e (POP_ASSUM SUBST_ALL_TAC);
e SIMPL;
e (DISCH_THEN (fn th => POP_ASSUM MATCH_MP_TAC THEN MP_TAC th));
e (DISCH_THEN (MP_TAC o GEN_ALL o Q.SPEC`n1,l1:num#'a list`));
e (SIMPL);
(*2*)
e STRIP_TAC;
e (GEN_TAC THEN DISCH_THEN (MP_TAC o Q.SPEC`n,l`));;
e (SIMPL);
e (DISCH_THEN (fn th => FIRST_ASSUM MATCH_MP_TAC THEN MP_TAC th));

e (DISCH_THEN (fn th => REPEAT GEN_TAC THEN DISCH_TAC THEN 
                        MATCH_MP_TAC th));
*)

(*---------------------------------------------------------------------------
 *  Approximate specification of select:
 *
 *   (n < length L /\ 0<length L) ==> (nth(n, sort L) = select(n+1,L)).
 *
 *---------------------------------------------------------------------------*)

(*---------------------------------------------------------------------------
 *
 *        ML version.
 *
 *---------------------------------------------------------------------------*)
fun curry f x y = f (x,y);


fun filter P = 
 let fun itr [] = []
       | itr (h::t) = (if P h then [h] else [])@ itr t
   in itr
   end;

fun qsort(R,[]) = []
  | qsort(R, x::rst) = 
      qsort(R,filter(not o R x) rst)
      @[x]@
      qsort(R,filter(R x) rst);

fun quints (h1::h2::h3::h4::h5::h6::rst) = [h1,h2,h3,h4,h5]::quints(h6::rst)
  | quints l = [l];

fun rup_div(x,d) = x div d + (if (x mod d = 0) then 0 else 1);

fun median5[_,_,m,_,_] = m
  | median5[_,_,m,_] = m
  | median5[_,m,_] = m
  | median5[_,m] = m
  | median5[m] = m;

fun part3(m:real,[],l1,l2,l3) = (l1,l2,l3)
  | part3(m,h::t,(l1,n1),(l2,n2),(l3,n3)) =
      if (h<m) then part3(m,t,(h::l1,n1+1),(l2,n2),(l3,n3)) else 
      if (m<h) then part3(m,t,(l1,n1),(h::l2,n2+1),(l3,n3)) 
               else part3(m,t,(l1,n1),(l2,n2),(h::l3,n3+1));

exception INDEX_TOO_LARGE;
exception NTH

fun nth(0,h::t) = h
  | nth(n,h::t) = nth(n-1,t)
  | nth(_,[]) = raise NTH;


(*---------------------------------------------------------------------------
 * The algorithm - it's zero-based, so selecting the 0th element will 
 * return the smallest one in the list.
 *---------------------------------------------------------------------------*)
local val sort = curry qsort (curry(op<=):real->real->bool)
in
fun select n l =
    let val Q = quints l
        val Qlen = length Q
        val sQ = map sort Q
    in 
    if (Qlen = 1) then nth(n,hd sQ)
    else let val m = select(rup_div(Qlen+1,2)) (map median5 sQ)
             val ((lower,n1),
                  (upper,n2),
                  (middle,n3)) = part3(m,L,([],0),([],0),([],0))
         in
         if (n1 >= n) then select n lower
         else if (n1+n3 >= n) then m
              else select(n-(n1+n3)) upper
         end
     end
end;

(*---------------------------------------------------------------------------
 *  Testing (this wouldn't be necessary with a verified "select"!). We use
 * a random number generator due to Park&Miller, by way of Paulson, p.96, in
 * order to build random lists of numbers.
 *---------------------------------------------------------------------------*)

local val A = 16807.0    and    M = 2147483647.0
in
fun random n =
   let fun nextrand seed =
          let val t = A*seed
          in t-M * real(floor(t/M))
          end
       fun randlist(0,seed,tail) = (seed,tail)
         | randlist(n,seed,tail) = randlist(n-1,nextrand seed, seed::tail)
  in #2(randlist(n,1.0,[]))
  end
end;

(*---------------------------------------------------------------------------
 * Tests.
 *---------------------------------------------------------------------------*)
select(13, random 113);

nth(12, qsort(curry(op<):real->real->bool, random 113));
