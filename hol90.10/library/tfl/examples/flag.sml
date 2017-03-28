(*----------------------------------------------------------------------------
 *
 *       The Dutch National Flag - Term Rewriting Emulation
 *
 *
 *         ML version 
 *      ---------------
 *
 *   datatype colour = R | W | B;
 *
 *   val cons = curry (op ::);
 *   infix 3 ##;
 *   fun (f##g) (x,y) = (f x, g y);
 *
 *   fun dnf []  = ([],false)
 *     | dnf (W::R::rst) = (R::W::rst, true)
 *     | dnf (B::R::rst) = (R::B::rst, true)
 *     | dnf (B::W::rst) = (W::B::rst, true)
 *     | dnf (x::rst)    = (cons x##I)(dnf rst);
 *  
 *  fun flag L = let val (alist,changed) = dnf L
 *               in if changed then flag alist else alist
 *               end;
 *
 *  flag [R,W,W,B,R,W,W,R,B,B];
 *---------------------------------------------------------------------------*)

new_theory"flag";
cons_path "../" theory_path;
map new_parent ["kls_list","permutation"];
map add_theory_to_sml ["kls_list","permutation"];
use"../utils.sml";

Thm.counting_thms true;

(*---------------------------------------------------------------------------
 * Some miscellaneous stuff.
 *---------------------------------------------------------------------------*)
val prop_lem = Q.prove`(((A,T) = C) ==> D) ==> (((A:'a,x) = C) /\ x ==> D)`
(BOOL_CASES_TAC(Term`x:bool`) THEN RW_TAC[]);

val Ithm = theorem"combin" "I_THM";

(*---------------------------------------------------------------------------
 * Define the type of colours and some syntax support.
 *---------------------------------------------------------------------------*)
local open Hol_datatype
in
  val colour_ty_info = hol_datatype `colour = R | W | B`

  val func_prod_def = 
         define (Infix 400)  `## (f:'a->'b) (g:'c->'d) (x,y) = (f x, g y)`

  val Cons_def =
          new_definition("Cons_def",Term`Cons:'a->'a list->'a list = $::`)
end;


(*---------------------------------------------------------------------------
 * More product hassle.
 *---------------------------------------------------------------------------*)
val func_to_prod_lem = Q.prove
`!(x:'a) (y:'b) (z:'a#'b). 
   ((x,y) = (f##g) z) 
    ==> 
   ?p0 p1. (z = (p0,p1)) /\ (x = f p0) /\ (y = g p1)`
(GEN_TAC THEN GEN_TAC 
  THEN TUPLE_TAC(Term`p:'a,(q:'b)`)
  THEN RW_TAC[func_prod_def]
  THEN REPEAT STRIP_TAC 
  THEN MAP_EVERY Q.EXISTS_TAC[`p`, `q`]
  THEN RW_TAC[]);

(*---------------------------------------------------------------------------
 * The engine: it searches for a rewrite and, if one is possible, it 
 * performs it and returns true (plus the changed list). If it can't find one, 
 * it returns false (plus the unchanged list).
 *---------------------------------------------------------------------------*)
val Dnf_def = 
Rfunction `\l1 l2. ?h:colour. l2 = h::l1`   (* prim. rec. on lists *)

          `(Dnf []          = ([], F))        /\ 
           (Dnf (W::R::rst) = (R::W::rst, T)) /\ 
           (Dnf (B::R::rst) = (R::B::rst, T)) /\ 
           (Dnf (B::W::rst) = (W::B::rst, T)) /\ 
           (Dnf (x::rst)    = (Cons x##I) (Dnf rst))`;

(* Program optimization, in a way *)
val Dnf_eqns = save_thm("Dnf",
let val [dnf_nil,a,b,c,d,e,f,g,h,i] = CONJUNCTS(#rules Dnf_def)
    val simpl = RW_RULE [dnf_nil,func_prod_def,theorem"combin" "I_THM"]
in LIST_CONJ [dnf_nil, simpl e, simpl h, a,b,c,d,f,g,i]
end);

val Dnf_induction = save_thm("Dnf_induction",
let val taut = Q.TAUT_CONV
        `^(#ant(dest_imp(#Body(dest_forall((concl (#induction Dnf_def))))))) = 
         P [] /\
         P [B] /\
         P [W] /\
         (!rst. P (W::R::rst)) /\
         (!rst. P (B::R::rst)) /\
         (!rst. P (B::W::rst)) /\
         (!rst. P (B::rst) ==> P (B::B::rst)) /\
         (!rst. P (B::rst) ==> P (W::B::rst)) /\
         (!rst. P (W::rst) ==> P (W::W::rst)) /\
        (!rst. P rst ==> P (R::rst))`
 in RW_RULE[taut] (#induction Dnf_def)
 end);


(*---------------------------------------------------------------------------
 * Repeatedly rewrite until no more are possible. 
 *---------------------------------------------------------------------------*)

val flag_def = 
    function  `flag L = let (alist, changed) = Dnf L
                        in changed => flag alist 
                                   |  alist`;


(*---------------------------------------------------------------------------
 * Termination (suggestion of jrh). Earlier I was banging my head 
 * against counting the total number of swaps that take place. This way
 * is much simpler.
 *---------------------------------------------------------------------------*)

val Weight_def = 
  Rfunction `\L1 L2. ?h:colour. L2 = h::L1` 
     `(Weight (R::rst) = 3 + 2*Weight rst) /\
      (Weight (W::rst) = 2 + 2*Weight rst)  /\
      (Weight (B::rst) = 1 + 2*Weight rst)`;


val Weight_mono = Q.prove
`!l1 l2 x. Weight l1 < Weight l2 ==> Weight (x::l1) < Weight (x::l2)`
(REPEAT GEN_TAC 
  THEN STRUCT_CASES_TAC (Q.SPEC`x` (#nchotomy (#2 colour_ty_info)))
  THEN RW_TAC[#rules Weight_def]
  THEN CONV_TAC ARITH_CONV);


(*---------------------------------------------------------------------------
 * Instantiate the definition with the termination relation.
 *---------------------------------------------------------------------------*)
local val tflag = Q.INST [`R'` |-> `measure Weight`] 
                         (DISCH_ALL flag_def)
in val flag_def1 = 
  UNDISCH (Rewrite.REWRITE_RULE[theorem"WF" "WF_measure"] tflag)
end;


val total_flips_tac = RW_TAC[#rules Weight_def] THEN CONV_TAC ARITH_CONV;

val flag_terminates = Q.prove
`^(hd(#1(dest_thm(flag_def1))))`
(REPEAT GEN_TAC
   THEN MATCH_MP_TAC prop_lem
   THEN Q.ID_SPEC_TAC`alist` THEN Q.ID_SPEC_TAC`L`
   THEN REC_INDUCT_TAC Dnf_induction
   THEN RW_TAC[Dnf_eqns] 
   THEN CONV_TAC (HOL_Tfl.tc_simplifier[]) 
   THEN REPEAT STRIP_TAC
   THEN (total_flips_tac (* base cases *)
         ORELSE          (* recursive cases *)
         (IMP_RES_TAC func_to_prod_lem
           THEN POP_ASSUM (SUBST_ALL_TAC o EQT_INTRO o RW_RULE[Ithm])
           THEN POP_ASSUM SUBST_ALL_TAC
           THEN POP_ASSUM SUBST_ALL_TAC
           THEN POP_ASSUM (K ALL_TAC) 
           THEN POP_ASSUM (MP_TAC o Q.SPEC`p0`) 
           THEN RW_TAC[Cons_def,Weight_mono])));


val [flag_eqn,flag_induction] = CONJUNCTS(PROVE_HYP flag_terminates flag_def1);
 

(*---------------------------------------------------------------------------
 * Dnf permutes its input.
 *---------------------------------------------------------------------------*)
val prod_fg_var = Q.prove
`!(f:'a->'b) (g:'c->'d) x. (f##g) x = (f(FST x), g(SND x))`
(GEN_TAC THEN GEN_TAC 
  THEN TUPLE_TAC(Term`(p0:'a, (p1:'c))`)
  THEN RW_TAC[func_prod_def]);


val dnf_permutation = Q.prove
`!L. permutation L (FST (Dnf L))`
(PROGRAM_TAC{rules = Dnf_eqns, induction = Dnf_induction}
  THEN RW_TAC[permutation_refl,Cons_def]
  THEN ((RW_TAC[permutation_def,filter_def] THEN GEN_TAC 
           THEN REPEAT (COND_CASES_TAC THEN POP_ASSUM MP_TAC) THEN RW_TAC[]
           THEN NO_TAC)
        ORELSE
         ASM_RW_TAC[prod_fg_var,permutation_mono]));

val Cons_pair_lem = Q.prove
`!(x:'a) y z (p1:'b) p2.
   ((Cons x y, p1) = (Cons x z,p2)) = ((y,p1) = (z,p2))`
(RW_TAC[Cons_def]);

val cons_pair_lem = Q.prove
`!(x:'a) y z (p1:'b) p2.
   ((x::y, p1) = (x::z,p2)) = ((y,p1) = (z,p2))`
(RW_TAC[Cons_def]);


val Dnf_no_swaps = Q.prove
`!L alist. ((alist,F) = Dnf L) ==> (alist=L)`
(REC_INDUCT_TAC(Dnf_induction) 
   THEN RW_TAC[Dnf_eqns,Cons_def]
   THEN REPEAT STRIP_TAC
   THEN IMP_RES_TAC func_to_prod_lem
   THEN POP_ASSUM(SUBST_ALL_TAC o PURE_RW_RULE[theorem"combin" "I_THM"])
   THEN POP_ASSUM SUBST_ALL_TAC
   THEN POP_ASSUM (ASSUME_TAC o SYM)
   THEN ASM_RW_TAC[]);


val append_cong = Q.prove
`!l1 l2 l3 (l4:'a list). 
  (l1 = l2) /\ (l3 = l4) ==> (APPEND l1 l3 = APPEND l2 l4)`
(RW_TAC[]);

val app_prod_eq = Q.prove
`!(f:'a->'b#'c) a b x. ((a,b) = f x) ==> (FST(f x) = a) /\ (SND(f x) = b)`
(REPEAT GEN_TAC THEN DISCH_THEN (fn th => RW_TAC[GSYM th]));

val LIST_INDUCT_TAC = INDUCT_THEN (theorem "list" "list_INDUCT") MP_TAC;

val filter_eq_cons = Q.prove
`!L l1 (x:'a) y. ~(x=y) ==> ~(x::l1 = filter ($=y) L)`
(LIST_INDUCT_TAC THEN RW_TAC[filter_def]
  THEN DISCH_TAC THEN REPEAT GEN_TAC THEN COND_CASES_TAC
  THEN ASM_RW_TAC[]);

val cons_list_neq = Q.prove
`!(h:'a) l1. ~(h :: l1 = l1)`
(GEN_TAC THEN LIST_INDUCT_TAC THEN RW_TAC[]
   THEN CONV_TAC NNF_CONV
   THEN DISCH_TAC THEN GEN_TAC 
   THEN DISCH_THEN SUBST_ALL_TAC THEN ASM_RW_TAC[]);

val append_nil_lem = Q.prove
`!L (l1:'a list). (l1 = APPEND L l1) ==> (L = [])`
(CCONTR_TAC THEN RULE_ASSUM_TAC (CONV_RULE NNF_CONV)
 THEN POP_ASSUM STRIP_ASSUME_TAC
 THEN POP_ASSUM(fn th => STRIP_ASSUME_TAC(RW_RULE[th] (Q.SPEC`L` list_CASES')))
 THEN POP_ASSUM SUBST_ALL_TAC
 THEN POP_ASSUM (MP_TAC o Q.AP_TERM`LENGTH`)
 THEN RW_TAC[definition"list" "LENGTH",APPEND,length_append_distrib]
 THEN CONV_TAC ARITH_CONV);

val append_nil_eq = Q.prove
`!L (l1:'a list). (l1 = APPEND L l1) = (L = [])`
(REPEAT GEN_TAC THEN EQ_TAC THEN RW_TAC[append_nil_lem,APPEND]);

val cons_append_inj = Q.prove
`!L (h:'a) l1. (h::l1 = APPEND L l1) = ([h] = L)`
(LIST_INDUCT_TAC THEN RW_TAC[APPEND]
 THENL [RW_TAC[cons_list_neq],
        RW_TAC[append_nil_eq] 
        THEN REPEAT STRIP_TAC THEN EQ_TAC THEN RW_TAC[]]);

val taut = EQT_ELIM(RW_CONV[](Term`((b:'a)=c) ==> ((a=b) = (a=c))`));

val mem_filter_imp = Q.prove
`!L P (x:'a). mem x (filter P L) ==> P x`
(RW_TAC[mem_filter]);

val filter_lem = Q.prove
`!P l (h:'a) t. (filter P l = h::t) ==> P h`
(REPEAT GEN_TAC THEN 
  DISCH_THEN (fn th => MATCH_MP_TAC mem_filter_imp 
                       THEN Q.EXISTS_TAC`l` THEN MP_TAC th)
  THEN RW_TAC[mem_def]);

val filter_lem1 = GSYM(CONV_RULE (ONCE_DEPTH_CONV CONTRAPOS_CONV) filter_lem);
    
val append_nil_squeeze = Q.prove
`!L l0 l1 (x:'a). ~mem x L ==> (x::l0 = APPEND L l1) ==> (L=[])`
(GEN_CASES_TAC list_CASES' THEN RW_TAC[APPEND,mem_def]
 THEN CONV_TAC NNF_CONV THEN RW_TAC[]);


val drop_empty_filter = Q.prove
`!P x l l1 (l2:'a list).
   (~P x) ==> ((x::l1 = filter P l ++ l2) ==> (x::l1 = l2))`
(REPEAT GEN_TAC THEN DISCH_TAC
 THEN IMP_RES_TAC (GEN_ALL(CONV_RULE CONTRAPOS_CONV
                     (DISCH_ALL(CONJUNCT1(UNDISCH
                       (#1(EQ_IMP_RULE (SPEC_ALL mem_filter))))))))
 THEN RW_TAC[append_infix]
 THEN POP_ASSUM (ASSUME_TAC o Q.SPEC`l`)
 THEN IMP_RES_TAC append_nil_squeeze
 THEN DISCH_TAC THEN  RES_TAC THEN ASM_RW_TAC[APPEND]);


val thm = 
   Q.GEN`P`(Q.GEN`x`
     (DISCH_ALL(MATCH_MP (Q.SPEC`filter P l` append_nil_squeeze)
       (UNDISCH (CONV_RULE CONTRAPOS_CONV
           (DISCH_ALL(CONJUNCT1(UNDISCH
                 (#1(EQ_IMP_RULE (SPEC_ALL mem_filter)))))))))));

val th0 = RW_RULE[GSYM append_infix] (Q.ISPECL[`$=R`,`B`] thm);
val th1 = RW_RULE[GSYM append_infix] (Q.ISPECL[`$=W`,`B`] thm);
val th2 = RW_RULE[GSYM append_infix] (Q.ISPECL[`$=R`,`W`] thm);

val lem = Q.prove`[]++l = (l:'a list)`(RW_TAC[append_infix,APPEND]);

(*---------------------------------------------------------------------------
 * When no swaps get made, the arrangement of the list is correct.
 *---------------------------------------------------------------------------*)
val final_step_correct = Q.prove
`!L. ((L,F) = Dnf L)
      ==>
     (L = filter ($= R) L ++ filter ($= W) L ++ filter ($= B) L)`
(PROGRAM_TAC{rules = Dnf_eqns, induction = Dnf_induction}
  THEN RW_TAC[filter_def, append_infix, APPEND]
  THEN POP_ASSUM MP_TAC THEN RW_TAC[Dnf_eqns]
  THEN PURE_RW_TAC[prod_fg_var,Cons_def,cons_pair_lem,
                   Ithm,theorem"pair" "PAIR"]
  THEN DISCH_THEN (ANTE_RES_THEN MP_TAC)
  THEN DISCH_THEN (MP_TAC o RW_RULE[filter_def])
  THEN DISCH_THEN (fn th => RW_TAC[filter_def] THEN MP_TAC th)
  THENL
  [DISCH_THEN (fn th => MP_TAC th THEN RW_TAC[MATCH_MP th0 th,lem])
    THEN DISCH_THEN (fn th => MP_TAC th THEN PURE_RW_TAC[MATCH_MP th1 th,lem])
    THEN DISCH_THEN (fn th => RW_TAC[APPEND]),

   DISCH_THEN (fn th => MP_TAC th THEN RW_TAC[MATCH_MP th0 th,lem])
    THEN DISCH_THEN (fn th => MP_TAC th THEN PURE_RW_TAC[MATCH_MP th1 th,lem])
    THEN DISCH_THEN (fn th => RW_TAC[APPEND]),

   DISCH_THEN (fn th => MP_TAC th THEN PURE_RW_TAC[MATCH_MP th2 th,lem])
    THEN DISCH_THEN (fn th => RW_TAC[APPEND] THEN 
                              MP_TAC (RW_RULE[APPEND,append_infix] th))
    THEN RW_TAC[],

   PURE_RW_TAC[APPEND,append_infix] 
     THEN DISCH_THEN (fn th => RW_TAC[] THEN ACCEPT_TAC th)]);


val let_lem = BETA_RULE(Q.ISPECL 
 [`\h. h = filter ($= R) L ++ filter ($= W) L ++ filter ($= B) L`,
  `Dnf L`,
  `\alist changed. changed => (flag alist) | alist`]
PULL_LET2);

(*---------------------------------------------------------------------------
 * Correctness: All occurrences of R in "flag L" are before all 
 * occurrences of W, which are before all occurrences of B. This is
 * expressible in terms of append: 
 *
 *    !L. ?l1 l2 l3. (flag L = l1++l2++l3)    /\
 *                   (!x. mem x l1 ==> (x=R)) /\
 *                   (!x. mem x l2 ==> (x=W)) /\
 *                   (!x. mem x l3 ==> (x=B))
 *
 * Witnesses for l1, l2, and l3 can be given explicitly by filtering L
 * for the particular colour.
 *
 *---------------------------------------------------------------------------*)

val flag_correct = Q.store_thm
("flag_correct",
`!L. ?l1 l2 l3. (flag L = l1++l2++l3)  /\
                 (!x. mem x l1 ==> (x=R)) /\
                 (!x. mem x l2 ==> (x=W)) /\
                 (!x. mem x l3 ==> (x=B))`,
CONV_TAC SKOLEM_CONV THEN  Q.EXISTS_TAC`filter ($=R)` THEN
CONV_TAC SKOLEM_CONV THEN  Q.EXISTS_TAC`filter ($=W)` THEN
CONV_TAC SKOLEM_CONV THEN  Q.EXISTS_TAC`filter ($=B)` 
 THEN RW_TAC[mem_filter]
 THEN PROGRAM_TAC{induction = flag_induction, rules=flag_eqn}
 THEN RW_TAC[let_lem] THEN LET_INTRO_TAC
 THEN MAP_EVERY Q.SPEC_TAC [(`x:colour list`,`alist`), (`y:bool`,`changed`)]
 THEN REPEAT GEN_TAC
 THEN COND_CASES_TAC
 THENL
  [ POP_ASSUM (fn changed => 
    POP_ASSUM (fn th => 
      let val th1 = RW_RULE[changed](Q.SPECL[`alist`,`changed`] th)
      in DISCH_THEN (fn th2 => STRIP_ASSUME_TAC (MP th1 th2) 
                               THEN MP_TAC th2) 
      end)) THEN
    DISCH_THEN (fn th => MP_TAC(RW_RULE[GSYM th] (SPEC_ALL dnf_permutation)))
    THEN ASM_RW_TAC[permutation_def],

    DISCH_THEN (fn th => MP_TAC th THEN RW_TAC[MATCH_MP Dnf_no_swaps th])
    THEN RW_TAC[final_step_correct]]);

let val {ABS,ASSUME,BETA_CONV,DISCH,INST_TYPE,MP,
            REFL,SUBST,drule,other,...} = thm_count()
in output(std_out,"theorems proved: "^
          Lib.int_to_string(ABS + ASSUME + BETA_CONV + DISCH + INST_TYPE + 
              MP + REFL + SUBST + drule + other)^".\n")
end;

html_theory"-";
