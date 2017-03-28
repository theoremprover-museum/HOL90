(*---------------------------------------------------------------------------
 * CONDITIONAL EXPRESSIONS AND THEIR NORMALIZATION (Boyer and Moore).
 *---------------------------------------------------------------------------*)

new_theory"cond" handle _ => ();


(*---------------------------------------------------------------------------
 * Define the datatype of conditional expressions.
 *---------------------------------------------------------------------------*)
local open Hol_datatype
in
val cond_ty_def = 
     hol_datatype `cond = A of ind
                        | IF of cond => cond => cond`
end;



(*---------------------------------------------------------------------------
 * Now a measure function for termination, due to Robert Shostak. 
 *---------------------------------------------------------------------------*)
val M_DEF = 
  define Prefix
        `(M (A i) = 1) /\
         (M (IF x y z) = M x + (M x * M y) + (M x * M z))`;



(*---------------------------------------------------------------------------
 * The definition of a normalization function
 *---------------------------------------------------------------------------*)
val norm_def = Rfunction 
  `measure M`
  `(norm (A i) = A i) /\
   (norm (IF (A x) y z) = IF (A x) (norm y) (norm z)) /\
   (norm (IF (IF u v w) y z) = norm (IF u (IF v y z) (IF w y z)))`;



(*---------------------------------------------------------------------------
 *  Required lemma for termination.  
 *---------------------------------------------------------------------------*)
val M_POSITIVE = BETA_RULE
 (Q.prove`!c. (\v. 0 < M v) c`
  (MATCH_MP_TAC (#induction (snd cond_ty_def)) THEN BETA_TAC THEN 
   RW_TAC[M_DEF] THEN CONV_TAC ARITH_CONV));


val distribs = [theorem"arithmetic" "LEFT_ADD_DISTRIB",
                theorem"arithmetic" "RIGHT_ADD_DISTRIB"];
val assocs = [GSYM(theorem"arithmetic" "ADD_ASSOC"),
              GSYM(theorem"arithmetic" "MULT_ASSOC")];
val LESS_MULT2 = theorem"arithmetic" "LESS_MULT2";


val norm_terminates = save_thm("norm_terminates", 
TflLib.prove_termination norm_def
(RW_TAC(M_DEF::(assocs@distribs))
  THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC
  THENL
    [ ALL_TAC, ALL_TAC,
      let val [Pu,Py,Pz] = map (Lib.C Q.SPEC M_POSITIVE) [`u`,`y`,`z`]
      in MP_TAC(LIST_CONJ(map (MATCH_MP LESS_MULT2 o LIST_CONJ) 
                              [[Pu,Py],[Pu,Pz]])) end]
  THEN CONV_TAC ARITH_CONV));


val norm_eqns = save_thm("norm_eqns",
  RW_RULE [norm_terminates] (#rules norm_def));

val norm_induction = save_thm("norm_induction",
  RW_RULE [norm_terminates] (DISCH_ALL (#induction norm_def)));


(*---------------------------------------------------------------------------
 * Define it again, using a lexicographic combination of relations. This is 
 * the version given in the Boyer-Moore book.
 *---------------------------------------------------------------------------*)
val TDEPTH_DEF = 
  define Prefix
     `(TDEPTH (A i) = 0) /\
      (TDEPTH (IF x y z) = TDEPTH x + 1)`;

val Weight_def = 
  define Prefix
     `(Weight (A i) = 1) /\
      (Weight (IF x y z) = Weight x * (Weight y + Weight z))`;

val Weight_positive = BETA_RULE
 (Q.prove`!c. (\v. 0 < Weight v) c`
  (MATCH_MP_TAC (#induction (snd cond_ty_def)) THEN BETA_TAC THEN 
   RW_TAC(Weight_def::distribs) THEN CONJ_TAC 
   THENL
   [CONV_TAC ARITH_CONV,
   REPEAT GEN_TAC THEN DISCH_THEN 
    (fn th => MATCH_MP_TAC(theorem"arithmetic" "LESS_IMP_LESS_ADD") THEN 
              MATCH_MP_TAC LESS_MULT2 THEN MP_TAC th)
   THEN RW_TAC[]]));


val point_to_prod_def = 
  define (Infix 400)   `## (f:'a->'b) (g:'a->'c) x = (f x, g x)`;

(*---------------------------------------------------------------------------
 * Notice how the lexicographic combination of measure functions gets made.
 * It gets proved wellfounded automatically, which is nice!
 * It might be handy to have a combinator for this case; something like
 *
 *    f1 XX f2 XX ... XX fn = inv_image ($< X ...X ($< X $<))
 *                                      (f1## ... ##fn)
 *---------------------------------------------------------------------------*)

fun Rdefine thml = 
rfunction (Prim.postprocess{WFtac = WF_TAC[],
                       terminator = terminator, 
                       simplifier = tc_simplifier thml})
          RW_RULE;


val Ndef = Rdefine[point_to_prod_def]
  `inv_image ($< X $<) (Weight##TDEPTH)`
  `(N(A i) = A i) /\
   (N(IF(A x) y z) = IF(A x) (N y) (N z)) /\
   (N(IF(IF u v w) y z) = N(IF u (IF v y z) (IF w y z)))`;


val MULTS = theorem"arithmetic" "MULT_CLAUSES";
val ADDS = theorem"arithmetic" "ADD_CLAUSES";

val Nterminates = save_thm("Nterminates",
TflLib.prove_termination Ndef
(REPEAT CONJ_TAC
 THENL
 [ REPEAT GEN_TAC THEN DISJ1_TAC THEN RW_TAC[Weight_def,MULTS,ADDS] 
    THEN MP_TAC (Q.SPEC`y` Weight_positive) THEN CONV_TAC ARITH_CONV,
   REPEAT GEN_TAC THEN DISJ1_TAC THEN RW_TAC[Weight_def,MULTS,ADDS] 
    THEN MP_TAC (Q.SPEC`z` Weight_positive) THEN CONV_TAC ARITH_CONV,
   REPEAT GEN_TAC THEN DISJ2_TAC 
    THEN RW_TAC([Weight_def,MULTS,ADDS]@distribs@assocs) THEN CONJ_TAC
    THENL[CONV_TAC ARITH_CONV, RW_TAC[TDEPTH_DEF]] THEN CONV_TAC ARITH_CONV]));


val Neqns = save_thm("Neqns",  RW_RULE [Nterminates] (#rules Ndef));

val Ninduction = save_thm("Ninduction",
  RW_RULE [Nterminates] (DISCH_ALL (#induction Ndef)));

(* Commented out

(*---------------------------------------------------------------------------
 * A nested version.  
 *---------------------------------------------------------------------------*)
val Norm_def = Rfunction `measure M`
  `(Norm (A i) = A i) /\
   (Norm (IF (A x) y z) = IF (A x) (Norm y) (Norm z)) /\
   (Norm (IF (IF u v w) y z) = Norm (IF u (Norm(IF v y z))
                                          (Norm(IF w y z))))`;


val mult_lem = Q.prove`!m. 0<m ==> !n. n <= m*n`
(GEN_TAC THEN DISCH_TAC 
   THEN INDUCT_TAC 
   THEN RW_TAC[theorem "arithmetic" "MULT_CLAUSES"]
   THENL [ALL_TAC, REPEAT (POP_ASSUM MP_TAC)]
         THEN CONV_TAC ARITH_CONV);


val [Pu,Pv,Pw] = map (Lib.C Q.SPEC M_POSITIVE) [`u`,`v`,`w`];
val Puw = MATCH_MP LESS_MULT2 (CONJ Pu Pw);
val uprod = MATCH_MP mult_lm Pu;
val uprods = [Q.SPEC`M w` uprod,
              Q.SPEC`M w * M z` uprod,
              Q.SPEC`M w * M y` uprod];


val vprods = [Q.SPEC`M v` uprod,
              Q.SPEC`M v * M z` uprod,
              Q.SPEC`M v * M y` uprod];



val basic = 
  let val [g1,g2,g3,g4,g5] = #tcs Norm_def
  in Q.prove`^g1 /\ ^g2 /\ ^g3 /\ ^g4`
     (RW_TAC[M_DEF]
       THEN REPEAT (CONJ_TAC ORELSE GEN_TAC) 
       THEN TRY (CONV_TAC ARITH_CONV)
       THEN RW_TAC(assocs@distribs)
       THENL (map (MP_TAC  o LIST_CONJ) [Pu::uprods, Pu::vprods])
       THEN CONV_TAC ARITH_CONV)
  end;

val rules = RW_RULE[basic] (#rules Norm_def);
val induction = RW_RULE[basic] (DISCH_ALL (#induction Norm_def));

g`^g5`;
e (PROGRAM_TAC{rules = rules, induction=induction});
&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&

val cond_size_def = 
  efine Prefix
     `(cond_size (A i) = 0) /\
      (cond_size (IF x y z) = cond_size x + cond_size y + cond_size z + 1)`;

val all_tdepth_def = 
  Rdefine[cond_size_def] `measure cond_size`
     `(all_tdepth (A i) = 0) /\
      (all_tdepth (IF (A i) y z) = all_tdepth y + all_tdepth z) /\
      (all_tdepth (IF (IF x y z) u v) = 
           all_tdepth (IF x y z) + all_tdepth u + all_tdepth v + 1)`;


val Norm_def = Rdefine[point_to_prod_def,cond_size_def, #rules all_tdepth_def]
  `inv_image ($< X $<) (all_tdepth##cond_size)`
  `(Norm (A i) = A i) /\
   (Norm (IF (A x) y z) = IF (A x) (Norm y) (Norm z)) /\
   (Norm (IF (IF u v w) y z) = Norm (IF u (Norm(IF v y z))
                                          (Norm(IF w y z))))`;

(*
tgoal Norm_def;
e (REPEAT CONJ_TAC THEN REPEAT GEN_TAC);
1.
e (REPEAT GEN_TAC THEN Q.ASM_CASES_TAC`all_tdepth y = 0`);
1.1
e (DISJ2_TAC THEN ASM_RW_TAC[all_tdepth_eqns]);
e (CONJ_TAC THEN TRY(CONV_TAC ARITH_CONV));
e (RW_TAC[cond_size_def] THEN CONV_TAC ARITH_CONV);
1.2
e (DISJ1_TAC THEN ASM_RW_TAC[all_tdepth_eqns]);
e (POP_ASSUM MP_TAC THEN CONV_TAC ARITH_CONV);

2.
e (REPEAT GEN_TAC THEN Q.ASM_CASES_TAC`all_tdepth z = 0`);
2.1
e (DISJ2_TAC THEN ASM_RW_TAC[all_tdepth_eqns]);
e (CONJ_TAC THEN TRY(CONV_TAC ARITH_CONV));
e (RW_TAC[cond_size_def] THEN CONV_TAC ARITH_CONV);
2.2
e (DISJ1_TAC THEN ASM_RW_TAC[all_tdepth_eqns]);
e (POP_ASSUM MP_TAC THEN CONV_TAC ARITH_CONV);

3.
e (RW_TAC[all_tdepth_eqns]);
e (REPEAT GEN_TAC THEN DISJ1_TAC);
e (STRIP_ASSUME_TAC (Q.SPEC`w` (#nchotomy (#2 cond_ty_def))) THEN 
   POP_ASSUM SUBST_ALL_TAC);
3.1
e (RW_TAC[all_tdepth_eqns] THEN CONV_TAC ARITH_CONV);
3.2
e (RW_TAC[all_tdepth_eqns]);
4.
*)
*)
html_theory"-";
