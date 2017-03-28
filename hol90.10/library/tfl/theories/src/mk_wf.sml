(* Set the path to write the theory to. *)
local
    val path = (!HOLdir)^"library/tfl/theories/"^
               SysParams.theory_file_type^"/"
in
    val _ =  theory_path := path::(!theory_path)
end;


use"../../examples/Q.sig"; 
use"../../examples/Q.sml"; 
use"../../examples/utils.sml"; 


val USE_TAC = IMP_RES_THEN(fn th => ONCE_REWRITE_TAC[th]);

(* Use a theory about transitive closure *)
load_theory"TC"; add_theory_to_sml"TC";

(* Start a theory of wellfounded relations *)
new_theory "WF";


(*---------------------------------------------------------------------------
 * No infinite descending chains in 'a. Conceptually simpler (to some)
 * than the next (equivalent) definition, which is solely in terms of
 * predicates (and therefore logically simpler).
 *---------------------------------------------------------------------------*)
val wellfounded_def = Q.new_definition("wellfounded_def",
   `wellfounded (R:'a->'a->bool) = ~?f. !n. R (f (n+1)) (f n)`);


val WF_DEF = Q.new_definition("WF_DEF",
  `WF R = !B. (?w:'a. B w) ==> ?min. B min /\ !b. R b min ==> ~B b`);


(*---------------------------------------------------------------------------
 * First half of showing that the two definitions of wellfounded agree.
 *---------------------------------------------------------------------------*)
val WF_IMP_WELLFOUNDED = Q.prove
`!(R:'a->'a->bool). WF R ==> wellfounded R`
(GEN_TAC THEN CONV_TAC CONTRAPOS_CONV THEN REWRITE_TAC[wellfounded_def,WF_DEF]
 THEN STRIP_TAC THEN NNF_TAC
 THEN Q.EXISTS_TAC`\p:'a. ?n:num. p = f n`
 THEN BETA_TAC THEN CONJ_TAC THENL
  [MAP_EVERY Q.EXISTS_TAC [`(f:num->'a) n`,  `n`] THEN REFL_TAC,
   GEN_TAC THEN DISCH_THEN (CHOOSE_THEN SUBST1_TAC)
    THEN Q.EXISTS_TAC`f(n+1)` THEN ASM_REWRITE_TAC[]
    THEN Q.EXISTS_TAC`n+1` THEN REFL_TAC]);

(*---------------------------------------------------------------------------
 * Second half.
 *---------------------------------------------------------------------------*)
local val RW_TAC = Rewrite.REWRITE_TAC
      val ASM_RW_TAC = Rewrite.ASM_REWRITE_TAC
in
val WELLFOUNDED_IMP_WF = Q.prove
`!(R:'a->'a->bool). wellfounded R ==> WF R`
(RW_TAC[wellfounded_def,WF_DEF,Q.num_CONV`1`,theorem"arithmetic" "ADD_CLAUSES"]
  THEN GEN_TAC THEN CONV_TAC CONTRAPOS_CONV THEN RW_TAC[] 
  THEN NNF_TAC THEN REPEAT STRIP_TAC
  THEN Q.EXISTS_TAC`SIMP_REC w (\x. @q. R q x /\ B q)` THEN GEN_TAC
  THEN Q.SUBGOAL_THEN `!n. B(SIMP_REC w (\x. @q. R q x /\ B q) n)`
                      (ASSUME_TAC o SPEC_ALL) 
  THENL [INDUCT_TAC,ALL_TAC] THEN ASM_RW_TAC[theorem"prim_rec" "SIMP_REC_THM"]
  THEN BETA_TAC THEN RES_TAC 
  THEN IMP_RES_TAC(BETA_RULE
     (Q.SPEC`\q. R q (SIMP_REC w (\x. @q. R q x /\ B q) n) /\ B q` SELECT_AX)))
end;


val WF_IFF_WELLFOUNDED = Q.store_thm("WF_IFF_WELLFOUNDED",
`!(R:'a->'a->bool). WF R = wellfounded R`,
GEN_TAC THEN EQ_TAC THEN STRIP_TAC
  THENL [IMP_RES_TAC WF_IMP_WELLFOUNDED,
         IMP_RES_TAC WELLFOUNDED_IMP_WF]);




(*---------------------------------------------------------------------------
 * Polymorphic variables stand for non-empty sets and thus the standard 
 * definition can be used in a simple form in polymorphic settings.
 *---------------------------------------------------------------------------*)
val WF_POLY = 
Q.store_thm("WF_POLY",  `!R:'a->'a->bool. WF R ==> ?min. !b. ~R b min`,
 REWRITE_TAC[WF_DEF]
  THEN GEN_TAC
  THEN DISCH_THEN (MP_TAC o Q.SPEC`\x:'a. T`) THEN BETA_TAC
  THEN REWRITE_TAC[]);

(*---------------------------------------------------------------------------
 *
 * WELL FOUNDED INDUCTION
 *
 * Proof: For RAA, assume there's a z s.t. ~P z. By wellfoundedness, there's a
 * minimal object w s.t. ~P w. (P holds of all objects "less" than w.)
 * By the other assumption, i.e.,
 * 
 *   !x. (!y. R y x ==> P y) ==> P x,
 *
 * P w holds, QEA.
 *
 *---------------------------------------------------------------------------*)
val WF_INDUCTION_THM = 
Q.store_thm("WF_INDUCTION_THM",
`!(R:'a->'a->bool). 
   WF R  ==> !P. (!x. (!y. R y x ==> P y) ==> P x)  ==> !x. P x`,
GEN_TAC THEN REWRITE_TAC[WF_DEF]
 THEN DISCH_THEN (fn th => GEN_TAC THEN (MP_TAC (Q.SPEC `\x:'a. ~P x` th)))
 THEN BETA_TAC THEN REWRITE_TAC[] THEN STRIP_TAC THEN CONV_TAC CONTRAPOS_CONV
 THEN NNF_TAC THEN STRIP_TAC THEN RES_TAC
 THEN Q.EXISTS_TAC`min` THEN ASM_REWRITE_TAC[]);


val INDUCTION_WF_THM = Q.prove
`!R:'a->'a->bool. (!P. (!x. (!y. R y x ==> P y) ==> P x) ==> !x. P x) ==> WF R`
(GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[WF_DEF] THEN GEN_TAC THEN 
 CONV_TAC CONTRAPOS_CONV THEN NNF_TAC THEN 
 DISCH_THEN (fn th => POP_ASSUM (MATCH_MP_TAC o BETA_RULE o Q.SPEC`\w. ~B w`)
                      THEN ASSUME_TAC th) THEN GEN_TAC THEN 
 CONV_TAC CONTRAPOS_CONV THEN NNF_TAC
 THEN POP_ASSUM MATCH_ACCEPT_TAC);


(*---------------------------------------------------------------------------
 * A tactic for doing wellfounded induction. Lifted and adapted from 
 * John Harrison's definition of WO_INDUCT_TAC in the wellordering library. 
 *---------------------------------------------------------------------------*)
val WF_INDUCT_TAC =
 let val wf_thm0 = CONV_RULE (ONCE_DEPTH_CONV ETA_CONV)
                   (REWRITE_RULE [Q.TAUT_CONV`A==>B==>C = A/\B==>C`]
                      (CONV_RULE (ONCE_DEPTH_CONV RIGHT_IMP_FORALL_CONV) 
                          WF_INDUCTION_THM))
      val [R,P] = fst(strip_forall(concl wf_thm0))
      val wf_thm1 = GENL [P,R](SPEC_ALL wf_thm0)
   fun tac (asl,w) =
    let val {Rator,Rand} = dest_comb w
        val {Name = "!",...} = dest_const Rator
        val thi = ISPEC Rand wf_thm1
        val thf = CONV_RULE(ONCE_DEPTH_CONV 
                            (BETA_CONV o assert (curry(op=) Rand o rator))) thi
    in MATCH_MP_TAC thf (asl,w)
    end
    handle _ => raise HOL_ERR{origin_structure = "<top-level>",
                               origin_function = "WF_INDUCT_TAC", 
                                      message = "Unanticipated term structure"}
 in tac
 end;



(*---------------------------------------------------------------------------
 * Now some combinators for wellfounded relations. 
 *---------------------------------------------------------------------------*)



(*---------------------------------------------------------------------------
 * Subset: if R is a WF relation and P is a subrelation of R, then 
 * P is a wellfounded relation.
 *---------------------------------------------------------------------------*)
val WF_SUBSET = Q.store_thm("WF_SUBSET",
`!(R:'a->'a->bool) P. 
  WF R /\ (!x y. P x y ==> R x y) ==> WF P`,
REWRITE_TAC[WF_DEF] 
 THEN REPEAT STRIP_TAC 
 THEN RES_TAC 
 THEN Q.EXISTS_TAC`min` 
 THEN ASM_REWRITE_TAC[] 
 THEN GEN_TAC 
 THEN DISCH_TAC 
 THEN REPEAT RES_TAC);



(*---------------------------------------------------------------------------
 * The transitive closure of a wellfounded relation is wellfounded. 
 * I got the clue about the witness from Peter Johnstone's book:
 * "Notes on Logic and Set Theory". An alternative proof that Bernhard
 * Schaetz showed me uses well-founded induction then case analysis. In that 
 * approach, the IH must be quantified over all sets, so that we can
 * specialize it later to an extension of B.
 *---------------------------------------------------------------------------*)
val WF_TC = Q.store_thm("WF_TC",
`!R:'a->'a->bool. WF R ==> WF(TC R)`,
GEN_TAC THEN CONV_TAC CONTRAPOS_CONV THEN REWRITE_TAC[WF_DEF] 
 THEN NNF_TAC THEN DISCH_THEN (Q.X_CHOOSE_THEN `B` MP_TAC)
 THEN DISCH_THEN (fn th => 
       Q.EXISTS_TAC`\m:'a. ?a z. B a /\ TC R a m /\ TC R m z /\ B z` 
       THEN BETA_TAC THEN CONJ_TAC THEN STRIP_ASSUME_TAC th)
 THENL
 [RES_TAC THEN RES_TAC THEN MAP_EVERY Q.EXISTS_TAC[`b`,  `b'`,  `w`]
   THEN ASM_REWRITE_TAC[],
  Q.X_GEN_TAC`m` THEN STRIP_TAC THEN Q.UNDISCH_TAC`TC R (a:'a) m`
   THEN DISCH_THEN(fn th => STRIP_ASSUME_TAC (CONJ th (MATCH_MP TC_CASES2 th)))
   THENL
   [ Q.EXISTS_TAC`a` THEN ASM_REWRITE_TAC[] THEN RES_TAC
     THEN MAP_EVERY Q.EXISTS_TAC [`b'`, `z`] THEN ASM_REWRITE_TAC[],
     Q.EXISTS_TAC`y` THEN ASM_REWRITE_TAC[] 
     THEN MAP_EVERY Q.EXISTS_TAC[`a`,`z`] THEN ASM_REWRITE_TAC[] 
     THEN IMP_RES_TAC TC_SUBSET]
   THEN 
   IMP_RES_TAC (REWRITE_RULE[transitive_def] TC_TRANSITIVE)]);


(*---------------------------------------------------------------------------
 * Inverse image theorem: mapping into a wellfounded relation gives a 
 * derived well founded relation. A "size" mapping, like "length" for 
 * lists is such a relation.
 *
 * Proof.
 * f is total and maps from one n.e. set (Alpha) into another (Beta which is
 * "\y. ?x:'a. Alpha x /\ (f x = y)"). Since the latter is n.e. 
 * and has a wellfounded relation R on it, it has an R-minimal element 
 * (call it "min"). There exists an x:'a s.t. f x = min. Such an x is an 
 * R1-minimal element of Alpha (R1 is our derived ordering.) Why is x 
 * R1-minimal in Alpha? Well, if there was a y:'a s.t. R1 y x, then f y 
 * would not be in Beta (being less than f x, i.e., min). If f y wasn't in 
 * Beta, then y couldn't be in Alpha. 
 *---------------------------------------------------------------------------*)

val inv_image_def = 
Q.new_definition
("inv_image_def",
   `inv_image R (f:'a->'b) = \x y. R (f x) (f y):bool`);


val WF_inv_image = Q.store_thm("WF_inv_image",
`!R (f:'a->'b). WF R ==> WF (inv_image R f)`,
REPEAT GEN_TAC 
  THEN REWRITE_TAC[inv_image_def,WF_DEF] THEN BETA_TAC
  THEN DISCH_THEN (fn th => Q.X_GEN_TAC`Alpha` THEN STRIP_TAC THEN MP_TAC th)
  THEN Q.SUBGOAL_THEN`?w:'b. (\y. ?x:'a. Alpha x /\ (f x = y)) w` MP_TAC
  THENL
  [ BETA_TAC 
     THEN MAP_EVERY Q.EXISTS_TAC[`f(w:'a)`,`w`] 
     THEN ASM_REWRITE_TAC[],
    DISCH_THEN (fn th => DISCH_THEN (MP_TAC o C MATCH_MP th)) THEN BETA_TAC 
     THEN NNF_TAC 
     THEN REPEAT STRIP_TAC
     THEN Q.EXISTS_TAC`x`
     THEN ASM_REWRITE_TAC[]
     THEN GEN_TAC 
     THEN DISCH_THEN (ANTE_RES_THEN (MP_TAC o Q.SPEC`b`))
     THEN REWRITE_TAC[]]);

(*---------------------------------------------------------------------------
 * The lexicographic combination of two wellfounded orderings is wellfounded.
 * The minimal element of this relation is found by 
 * 
 *    1. Finding the set of first elements of the pairs in B
 *    2. That set is non-empty, so it has an R-minimal element, call it min
 *    3. Find the set of second elements of those pairs in B whose first
 *       element is min.
 *    4. This set is non-empty, so it has a Q-minimal element, call it min'.
 *    5. A minimal element is (min,min').
 *---------------------------------------------------------------------------*)


val X_DEF = 
Q.new_infix_definition
("X_DEF", 
  `X (R1:'a->'a->bool) 
     (R2:'b->'b->bool) = \(s,t) (u,v). R1 s u \/ (s=u) /\ R2 t v`, 450);

val WF_X = Q.store_thm("WF_X",
`!(R:'a->'a->bool) (Q:'b->'b->bool). WF R /\ WF Q  ==>  WF(R X Q)`,
REPEAT GEN_TAC THEN 
DISCH_THEN (fn th => REWRITE_TAC[X_DEF,WF_DEF] THEN GEN_TAC THEN 
 DISCH_THEN (CHOOSE_THEN (fn th1 =>
  Q.SUBGOAL_THEN `(?w1:'a. (\v. ?y:'b. B(v,y)) w1)` MP_TAC 
  THENL [BETA_TAC THEN MAP_EVERY Q.EXISTS_TAC[`FST (w:'a#'b)`,`SND (w:'a#'b)`]
         THEN ASM_REWRITE_TAC[th1],ALL_TAC])) THEN MP_TAC th) THEN 
DISCH_THEN (CONJUNCTS_THEN2 (fn th => DISCH_THEN(CHOOSE_THEN 
  (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) o (CONV_RULE NNF_CONV o BETA_RULE) o 
  MATCH_MP(REWRITE_RULE[WF_DEF] th))) MP_TAC) THEN
DISCH_THEN(fn th => DISCH_THEN(CHOOSE_THEN (CONJUNCTS_THEN ASSUME_TAC) o 
   (CONV_RULE NNF_CONV o BETA_RULE) o MATCH_MP (REWRITE_RULE[WF_DEF]th) o 
   EQ_MP(SYM(DEPTH_CONV BETA_CONV(--`?y.(\y:'b. B(min:'a,y))y`--))))) THEN 
Q.EXISTS_TAC`(min,min')` THEN ASM_REWRITE_TAC[] THEN 
CONV_TAC (DEPTH_CONV GEN_BETA_CONV) THEN GEN_TAC THEN 
DISCH_THEN (DISJ_CASES_THEN2 (ANTE_RES_THEN (MP_TAC o Q.SPEC`SND (b:'a#'b)`))
      (CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM) (ANTE_RES_THEN MP_TAC))) THEN 
REWRITE_TAC[]);


(*---------------------------------------------------------------------------
 * The relational product of two wellfounded relations is wellfounded. This
 * is a consequence of WF_X.
 *---------------------------------------------------------------------------*)
val RPROD_DEF = 
Q.new_definition
("RPROD_DEF", 
   `RPROD (R1:'a->'a->bool) 
          (R2:'b->'b->bool) = \(s,t) (u,v). R1 s u /\ R2 t v`);


val WF_RPROD = 
Q.store_thm("WF_RPROD",
 `!(R:'a->'a->bool) (Q:'b->'b->bool). WF R /\ WF Q  ==>  WF(RPROD R Q)`,
REPEAT STRIP_TAC THEN MATCH_MP_TAC WF_SUBSET
 THEN Q.EXISTS_TAC`R X Q`
 THEN CONJ_TAC 
 THENL [MATCH_MP_TAC WF_X THEN ASM_REWRITE_TAC[],
        REWRITE_TAC[X_DEF,RPROD_DEF] 
         THEN TUPLE_TAC(Term`(s,t):'a#'b`) THEN GEN_TAC THEN GEN_TAC
         THEN TUPLE_TAC(Term`(u,v):'a#'b`) THEN GEN_TAC THEN GEN_TAC
         THEN CONV_TAC (DEPTH_CONV PAIRED_BETA_CONV)
         THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[]]);



(*---------------------------------------------------------------------------
 * The empty order is wellfounded.
 *---------------------------------------------------------------------------*)
val Empty_def = 
Q.new_definition
        ("Empty_def", `Empty (x:'a) (y:'a) = F`);


val WF_Empty = 
Q.store_thm
  ("WF_Empty", 
   `WF (Empty:'a -> 'a -> bool)`, 
REWRITE_TAC[Empty_def,WF_DEF]);


(*---------------------------------------------------------------------------
 * Predecessor and "<" for "num" are wellfounded relations.
 *---------------------------------------------------------------------------*)
val NOT_LESS_0 = theorem "prim_rec" "NOT_LESS_0";
val LESS_THM = theorem "prim_rec" "LESS_THM";
val LESS_SUC_REFL = theorem "prim_rec" "LESS_SUC_REFL";
val INV_SUC_EQ = theorem "prim_rec" "INV_SUC_EQ";
val NOT_SUC = theorem "num" "NOT_SUC";


val WF_PRED = 
Q.store_thm
("WF_PRED",
  `WF \x y. y = SUC x`,
REWRITE_TAC[WF_DEF] THEN BETA_TAC THEN GEN_TAC 
THEN CONV_TAC(CONTRAPOS_CONV THENC NNF_CONV) THEN DISCH_TAC THEN 
INDUCT_TAC THEN CCONTR_TAC THEN RULE_ASSUM_TAC (REWRITE_RULE[]) THEN
RES_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[INV_SUC_EQ, GSYM NOT_SUC])
THENL (map FIRST_ASSUM [ACCEPT_TAC, MATCH_MP_TAC]) THEN
FILTER_ASM_REWRITE_TAC is_eq [] THEN ASM_REWRITE_TAC[]);


(*----------------------------------------------------------------------------
 * This theorem would be a lot nicer if < was defined as the transitive
 * closure of predecessor.
 *---------------------------------------------------------------------------*)
val WF_LESS = Q.store_thm("WF_LESS", `WF $<`,
REWRITE_TAC[WF_DEF]
 THEN GEN_TAC THEN CONV_TAC CONTRAPOS_CONV
 THEN DISCH_THEN (fn th1 => 
       SUBGOAL_THEN (--`^(concl th1) ==> !i j. j<i ==> ~B j`--)
                    (fn th => MP_TAC (MP th th1)))
 THEN CONV_TAC (DEPTH_CONV NOT_EXISTS_CONV) THEN DISCH_TAC THENL
  [INDUCT_TAC THEN GEN_TAC THEN 
    REWRITE_TAC[NOT_LESS_0,LESS_THM]
    THEN DISCH_THEN (DISJ_CASES_THENL[SUBST1_TAC, ASSUME_TAC])
    THEN STRIP_TAC THEN RES_TAC,
   GEN_TAC THEN FIRST_ASSUM MATCH_MP_TAC 
    THEN Q.EXISTS_TAC`SUC w`
    THEN MATCH_ACCEPT_TAC LESS_SUC_REFL]);


(*---------------------------------------------------------------------------
 * Measure functions are definable as inverse image into (<). Every relation
 * arising from a measure function is wellfounded, which is really great!
 *---------------------------------------------------------------------------*)
val measure_def = 
Q.new_definition
("measure_def",
  `measure:('a->num)->'a->'a->bool = inv_image $<`);


val WF_measure = 
Q.store_thm
("WF_measure",
  `!m:'a->num. WF (measure m)`,
REWRITE_TAC[measure_def] 
 THEN MATCH_MP_TAC WF_inv_image 
 THEN ACCEPT_TAC WF_LESS);


(* For lists *)

val LIST_INDUCT_TAC = INDUCT_THEN (theorem "list" "list_INDUCT") ASSUME_TAC;

val WF_LIST_PRED = Q.store_thm("WF_LIST_PRED",
`WF \L1 L2. ?h:'a. L2 = CONS h L1`,
REWRITE_TAC[WF_DEF] THEN BETA_TAC THEN GEN_TAC 
  THEN CONV_TAC(CONTRAPOS_CONV THENC NNF_CONV) THEN DISCH_TAC THEN 
  LIST_INDUCT_TAC THENL [ALL_TAC,GEN_TAC] THEN CCONTR_TAC THEN
  RULE_ASSUM_TAC (REWRITE_RULE[])  THEN RES_TAC
  THEN RULE_ASSUM_TAC(REWRITE_RULE[theorem"list" "NOT_NIL_CONS", 
                                   theorem"list" "CONS_11"])
  THENL (map FIRST_ASSUM [ACCEPT_TAC, MATCH_MP_TAC]) THEN
  FILTER_ASM_REWRITE_TAC is_conj [] THEN ASM_REWRITE_TAC[]);



(*---------------------------------------------------------------------------
 * Now the WF recursion theorem. Based on Tobias Nipkow's Isabelle development
 * of wellfounded recursion, which itself is a generalization of Mike 
 * Gordon's HOL development of the primitive recursion theorem.
 *---------------------------------------------------------------------------*)

val RESTRICT_DEF = 
Q.new_infix_definition
("RESTRICT_DEF",
   `$% (f:'a->'b) (R,(x:'a)) = \(y:'a). R y x => f y | @v:'b.T`, 25);


(*---------------------------------------------------------------------------
 * Obvious, but crucially useful. Unary case. Handling the n-ary case might 
 * be messy!
 *---------------------------------------------------------------------------*)
val RESTRICT_LEMMA = Q.store_thm("RESTRICT_LEMMA",
`!(f:'a->'b) R (y:'a) (z:'a).   R y z ==> ((f%R,z) y = f y)`,
REWRITE_TAC [RESTRICT_DEF] THEN BETA_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC
THEN ASM_REWRITE_TAC[]);


(*---------------------------------------------------------------------------
 * Two restricted functions are equal just when they are equal on each
 * element of their domain.
 *---------------------------------------------------------------------------*)
val CUTS_EQ = Q.prove
`!R f g (x:'a). ((f%R,x) = (g%R,x)) = !y:'a. R y x ==> (f y:'b = g y)`
(REPEAT GEN_TAC THEN REWRITE_TAC[RESTRICT_DEF]
 THEN CONV_TAC (DEPTH_CONV FUN_EQ_CONV) THEN BETA_TAC THEN EQ_TAC
 THENL
 [ CONV_TAC RIGHT_IMP_FORALL_CONV THEN GEN_TAC 
   THEN DISCH_THEN (MP_TAC o Q.SPEC`y`) THEN COND_CASES_TAC THEN REWRITE_TAC[],
   DISCH_TAC THEN GEN_TAC THEN COND_CASES_TAC THEN RES_TAC 
   THEN ASM_REWRITE_TAC[]]);


local val FUNC_EQ_TAC = BETA_TAC THEN AP_THM_TAC THEN AP_TERM_TAC
in
val EXPOSE_CUTS_TAC = FUNC_EQ_TAC THEN 
                      REWRITE_TAC[CUTS_EQ] THEN 
                      REPEAT STRIP_TAC
end;

(*---------------------------------------------------------------------------
 * The set of approximations to the function being defined, restricted to 
 * being R-parents of x. This has the consequence (approx_ext):
 *
 *    approx R M x f = (!w. f w = ((R w x) => (M (f % R,w) w) | (@v. T)))
 *
 *---------------------------------------------------------------------------*)
val approx_def = 
Q.new_definition
  ("approx_def",
   `approx R M x (f:'a->'b) = (f = ((\y. M (f%R,y) y)%R,x))`);

(* This could, in fact, be the definition. *)
val approx_ext = 
BETA_RULE(ONCE_REWRITE_RULE[RESTRICT_DEF]
    (CONV_RULE (ONCE_DEPTH_CONV (Q.X_FUN_EQ_CONV`w`)) approx_def));

val approx_SELECT0 = 
  Q.GEN`g`
   (Q.SPEC`g`(BETA_RULE(Q.ISPECL[`\f:'a->'b. approx R M x f`] SELECT_AX)));
val approx_SELECT1 = CONV_RULE FORALL_IMP_CONV  approx_SELECT0;


(*---------------------------------------------------------------------------
 * Choose an approximation for R and M at x. Thus it is a 
 * kind of "lookup" function, associating partial functions with arguments.
 * One can easily prove
 *  (?g. approx R M x g) ==>
 *    (!w. the_fun R M x w = ((R w x) => (M (the_fun R M x % R,w) w)
 *                                    |  (@v. T)))
 *---------------------------------------------------------------------------*)
val the_fun_def = 
Q.new_definition
("the_fun_def",
  `the_fun R M x = @f:'a->'b. approx R M x f`);

val approx_the_fun0 = ONCE_REWRITE_RULE [GSYM the_fun_def] approx_SELECT0;
val approx_the_fun1 = ONCE_REWRITE_RULE [GSYM the_fun_def] approx_SELECT1;
val approx_the_fun2 = SUBS [Q.SPECL[`R`,`M`,`x`,`the_fun R M x`] approx_ext]
                           approx_the_fun1;

val the_fun_rw1 = Q.prove
    `(?g:'a->'b. approx R M x g) 
      ==> !w. R w x ==> (the_fun R M x w = M (the_fun R M x % R,w) w)`
(DISCH_THEN (MP_TAC o MP approx_the_fun2) THEN
 DISCH_THEN (fn th => GEN_TAC THEN MP_TAC (SPEC_ALL th)) 
 THEN COND_CASES_TAC 
 THEN ASM_REWRITE_TAC[]);

val the_fun_rw2 = Q.prove
    `(?g:'a->'b. approx R M x g)  ==> !w. ~R w x ==> (the_fun R M x w = @v.T)`
(DISCH_THEN (MP_TAC o MP approx_the_fun2) THEN
 DISCH_THEN (fn th => GEN_TAC THEN MP_TAC (SPEC_ALL th)) 
 THEN COND_CASES_TAC 
 THEN ASM_REWRITE_TAC[]);

(*---------------------------------------------------------------------------
 * Define a recursion operator for wellfounded relations. This takes the
 * (canonical) function obeying the recursion for all R-ancestors of x:
 *
 *    \p. R p x => the_fun (TC R) (\f v. M (f%R,v) v) x p | Arb
 *
 * as the function made available for M to use, along with x. Notice that the
 * function unrolls properly for each R-ancestor, but only gets applied
 * "parentwise", i.e., you can't apply it to any old ancestor, just to a 
 * parent. This holds recursively, which is what the theorem we eventually
 * prove is all about.
 *---------------------------------------------------------------------------*)

val WFREC_DEF = 
Q.new_definition
("WFREC_DEF",
  `WFREC R (M:('a->'b)->'a->'b) = 
         \x. M (the_fun (TC R) (\f v. M (f%R,v) v) x % R,x)  x`);



(*---------------------------------------------------------------------------
 * Two approximations agree on their common domain.
 *---------------------------------------------------------------------------*)
val APPROX_EQUAL_BELOW = Q.prove
`!R M f g u v. 
  WF R /\ transitive R /\
  approx R M u f /\ approx R M v g 
  ==> !x:'a. R x u ==> R x v 
             ==> (f x:'b = g x)`
(REWRITE_TAC[approx_ext] THEN REPEAT GEN_TAC THEN STRIP_TAC
  THEN WF_INDUCT_TAC THEN Q.EXISTS_TAC`R` 
  THEN ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC
  THEN REPEAT COND_CASES_TAC THEN RES_TAC
  THEN EXPOSE_CUTS_TAC
  THEN ASM_REWRITE_TAC[]
  THEN RULE_ASSUM_TAC
        (REWRITE_RULE[Q.TAUT_CONV`A==>B==>C==>D = A/\B/\C==>D`,transitive_def])
  THEN FIRST_ASSUM MATCH_MP_TAC
  THEN RES_TAC THEN ASM_REWRITE_TAC[]);

val AGREE_BELOW = 
   REWRITE_RULE[Q.TAUT_CONV`A==>B==>C==>D = B/\C/\A==>D`]
    (CONV_RULE (DEPTH_CONV RIGHT_IMP_FORALL_CONV) APPROX_EQUAL_BELOW);


(*---------------------------------------------------------------------------
 * A specialization of AGREE_BELOW
 *---------------------------------------------------------------------------*)
val RESTRICT_FUN_EQ = Q.prove
`!R M f (g:'a->'b) u v.
     WF R /\
     transitive R   /\
     approx R M u f /\
     approx R M v g /\
     R v u
     ==> ((f%R,v) = g)`
(REWRITE_TAC[RESTRICT_DEF,transitive_def] THEN REPEAT STRIP_TAC
  THEN CONV_TAC (Q.X_FUN_EQ_CONV`w`) THEN BETA_TAC THEN GEN_TAC 
  THEN COND_CASES_TAC (* on R w v *)
  THENL [ MATCH_MP_TAC AGREE_BELOW THEN REPEAT Q.ID_EX_TAC 
            THEN RES_TAC THEN ASM_REWRITE_TAC[transitive_def],
          Q.UNDISCH_TAC`approx R M v (g:'a->'b)` 
            THEN DISCH_THEN(fn th => 
                   ASM_REWRITE_TAC[REWRITE_RULE[approx_ext]th])]);

(*---------------------------------------------------------------------------
 * Any function chosen to be an approximation is an approximation. Sounds
 * simple enough. This version is a little opaque, because it's phrased
 * in terms of witnesses, rather than the other one, which is phrased
 * in terms of existence. This theorem is not used in the sequel.
 *---------------------------------------------------------------------------*)
Q.prove
`!R M x. WF R /\ transitive R ==> approx R M x (the_fun R M x:'a->'b)`
(GEN_TAC THEN GEN_TAC 
 THEN CONV_TAC FORALL_IMP_CONV THEN STRIP_TAC
 THEN WF_INDUCT_TAC THEN Q.EXISTS_TAC`R` 
 THEN ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC
 THEN Lib.C Q.SUBGOAL_THEN MATCH_MP_TAC
          `(?f:'a->'b. approx R M x f) ==> approx R M x (the_fun R M x)` 
 THENL
 [ ACCEPT_TAC approx_the_fun1,
   Q.EXISTS_TAC`(\z. M (the_fun R M z) z)%R,x` THEN REWRITE_TAC[approx_ext]
    THEN GEN_TAC THEN COND_CASES_TAC
    THENL 
    [ USE_TAC RESTRICT_LEMMA 
       THEN EXPOSE_CUTS_TAC 
       THEN RES_THEN (SUBST1_TAC o REWRITE_RULE[approx_def]) 
       THEN REWRITE_TAC[CUTS_EQ] 
       THEN Q.X_GEN_TAC`v` THEN BETA_TAC THEN DISCH_TAC
       THEN RULE_ASSUM_TAC(REWRITE_RULE[transitive_def]) 
       THEN RES_TAC
       THEN USE_TAC RESTRICT_LEMMA 
       THEN EXPOSE_CUTS_TAC
       THEN MATCH_MP_TAC RESTRICT_FUN_EQ
       THEN MAP_EVERY Q.EXISTS_TAC[`M`,`w`]THEN ASM_REWRITE_TAC[transitive_def]
       THEN RES_TAC,
      REWRITE_TAC[RESTRICT_DEF] THEN BETA_TAC THEN 
      ASM_REWRITE_TAC[]]]);


(*---------------------------------------------------------------------------
 * Every x has an approximation. This is the crucial theorem.
 *---------------------------------------------------------------------------*)

val EXISTS_LEMMA = Q.prove
`!R M. WF R /\ transitive R ==> !x. ?f:'a->'b. approx R M x f`
(REPEAT GEN_TAC THEN STRIP_TAC
  THEN WF_INDUCT_TAC 
  THEN Q.EXISTS_TAC`R` THEN ASM_REWRITE_TAC[] THEN GEN_TAC
  THEN DISCH_THEN  (* Adjust IH by applying Choice *)
    (ASSUME_TAC o Q.GEN`y` o Q.DISCH`R (y:'a) (x:'a)` 
                o (fn th => REWRITE_RULE[GSYM the_fun_def] th)
                o SELECT_RULE o UNDISCH o Q.ID_SPEC)
  THEN Q.EXISTS_TAC`\p. R p x => M (the_fun R M p) p | ARB` (* witness *)
  THEN REWRITE_TAC[approx_ext] THEN BETA_TAC THEN GEN_TAC 
  THEN COND_CASES_TAC
  THEN ASM_REWRITE_TAC[definition"restr_binder" "ARB"]
  THEN EXPOSE_CUTS_TAC
  THEN RES_THEN (SUBST1_TAC o REWRITE_RULE[approx_def])     (* use IH *)
  THEN REWRITE_TAC[CUTS_EQ] 
  THEN Q.X_GEN_TAC`v` THEN BETA_TAC THEN DISCH_TAC
  THEN RULE_ASSUM_TAC(REWRITE_RULE[transitive_def]) THEN RES_TAC 
  THEN ASM_REWRITE_TAC[]
  THEN EXPOSE_CUTS_TAC
  THEN MATCH_MP_TAC RESTRICT_FUN_EQ
  THEN MAP_EVERY Q.EXISTS_TAC[`M`,`w`] 
  THEN ASM_REWRITE_TAC[transitive_def]
  THEN RES_TAC);

 

val the_fun_unroll = Q.prove
 `!R M x (w:'a).
     WF R /\ transitive R 
       ==> R w x 
        ==> (the_fun R M x w:'b = M (the_fun R M x%R,w) w)`
(REPEAT GEN_TAC THEN DISCH_TAC 
  THEN Q.ID_SPEC_TAC`w`
  THEN MATCH_MP_TAC the_fun_rw1 
  THEN MATCH_MP_TAC EXISTS_LEMMA
  THEN POP_ASSUM ACCEPT_TAC);

(*---------------------------------------------------------------------------
 * Unrolling works for any R M and x, hence it works for "TC R" and
 * "\f v. M (f % R,v) v". 
 *---------------------------------------------------------------------------*)
val the_fun_TC0 = 
  BETA_RULE
   (REWRITE_RULE[MATCH_MP WF_TC (Q.ASSUME`WF (R:'a->'a->bool)`),TC_TRANSITIVE]
     (Q.SPECL[`TC R`,`\f v. M (f % R,v) v`,`x`] the_fun_unroll));


(*---------------------------------------------------------------------------
 * There's a rewrite rule that simplifies this mess.
 *---------------------------------------------------------------------------*)
val TC_RESTRICT_LEMMA = 
Q.prove`!(f:'a->'b) R w. ((f%TC R,w)%R,w) = (f%R,w)`
(REPEAT GEN_TAC 
  THEN REWRITE_TAC[RESTRICT_DEF]
  THEN CONV_TAC (Q.X_FUN_EQ_CONV`p`) 
  THEN BETA_TAC THEN GEN_TAC 
  THEN COND_CASES_TAC
  THENL [IMP_RES_TAC TC_SUBSET, ALL_TAC] 
  THEN ASM_REWRITE_TAC[]);

val the_fun_TC = REWRITE_RULE[TC_RESTRICT_LEMMA] the_fun_TC0;


(*---------------------------------------------------------------------------
 * How does it look Skolemised?
 *---------------------------------------------------------------------------*)
val _ = CONV_RULE (ONCE_DEPTH_CONV SKOLEM_CONV) EXISTS_LEMMA;;


(*---------------------------------------------------------------------------
 * WFREC R M behaves as a fixpoint operator should.
 *---------------------------------------------------------------------------*)
val WFREC_THM = Q.store_thm
("WFREC_THM",
  `!R. !M:('a -> 'b) -> ('a -> 'b). 
      WF R ==> !x. WFREC R M x = M (WFREC R M%R,x) x`,
REPEAT STRIP_TAC THEN REWRITE_TAC[WFREC_DEF] 
  THEN EXPOSE_CUTS_TAC THEN BETA_TAC
  THEN IMP_RES_TAC TC_SUBSET 
  THEN USE_TAC the_fun_TC
  THEN EXPOSE_CUTS_TAC
  THEN MATCH_MP_TAC AGREE_BELOW
  THEN MAP_EVERY Q.EXISTS_TAC [`TC R`, `\f v. M (f % R,v) v`, `x`, `y`]
  THEN IMP_RES_TAC WF_TC 
  THEN ASSUME_TAC(SPEC_ALL TC_TRANSITIVE)
  THEN IMP_RES_TAC TC_SUBSET THEN POP_ASSUM (K ALL_TAC)
  THEN ASM_REWRITE_TAC[] 
  THEN REPEAT CONJ_TAC
  THENL [ RULE_ASSUM_TAC(REWRITE_RULE[transitive_def]) THEN RES_TAC, 
          ALL_TAC,ALL_TAC]
  THEN MATCH_MP_TAC approx_the_fun1
  THEN MATCH_MP_TAC EXISTS_LEMMA
  THEN ASM_REWRITE_TAC[]);


(*---------------------------------------------------------------------------
 * This is what is used by TFL. In a sense, the antecedent shows how 
 * some notion of definition can be moved into the object logic.
 *---------------------------------------------------------------------------*)
val WFREC_COROLLARY = 
 Q.store_thm("WFREC_COROLLARY",
  `!M R (f:'a->'b). (f = WFREC R M) ==> WF R ==> !x. f x = M (f%R,x) x`,
REPEAT GEN_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[WFREC_THM]);


(*---------------------------------------------------------------------------
 * The usual phrasing of the wellfounded recursion theorem.
 *---------------------------------------------------------------------------*)
val WF_RECURSION_THM = Q.store_thm("WF_RECURSION_THM",
`!R. WF R ==> !M. ?!f:'a->'b. !x. f x = M (f%R,x) x`,
GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN CONV_TAC EXISTS_UNIQUE_CONV 
THEN CONJ_TAC THENL
[Q.EXISTS_TAC`WFREC R M` THEN MATCH_MP_TAC WFREC_THM THEN POP_ASSUM ACCEPT_TAC,
 REPEAT STRIP_TAC THEN CONV_TAC (Q.X_FUN_EQ_CONV`w`) THEN WF_INDUCT_TAC
 THEN Q.EXISTS_TAC`R` THEN CONJ_TAC THENL
 [ FIRST_ASSUM ACCEPT_TAC, 
   GEN_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN AP_THM_TAC THEN 
   AP_TERM_TAC THEN REWRITE_TAC[CUTS_EQ] THEN GEN_TAC THEN 
   FIRST_ASSUM MATCH_ACCEPT_TAC]]);



(*---------------------------------------------------------------------------
 * For TFL termination condition extraction. It is equal to UNCURRY.
 *---------------------------------------------------------------------------*)
val PAIR_CASE_DEF = 
new_definition("PAIR_CASE_DEF", --`PAIR_CASE(f:'a->'b->'c) (x,y) = f x y`--);

export_theory();

html_theory"-";
