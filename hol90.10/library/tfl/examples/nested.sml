(*----------------------------------------------------------------------------
 * Nesting poses extra problems. Here we look at two ways to solve the
 * termination condition for a simple nested function. The first way is to 
 * blindly prove the given termination condition (by recursion induction).
 * The second is to see that a lemma, in fact the "specification" of the 
 * function, provides an easy route to eliminating the termination condition. 
 *---------------------------------------------------------------------------*)

new_theory"nested" handle _ => ();

val LESS_SUC_REFL = theorem"prim_rec" "LESS_SUC_REFL";
val LESS_MONO = theorem "prim_rec" "LESS_MONO";
val LESS_TRANS = theorem "arithmetic" "LESS_TRANS";

(* Define the function *)

val Gdef = 
Rfunction `$<`  `(G 0 = 0) /\ 
                 (G(SUC x) = G(G x))`;


val Gterminates = save_thm("Gterminates",
Q.prove `!x. G x < SUC x`
(REC_INDUCT_TAC (#induction Gdef)
  THEN RW_TAC[#rules Gdef, LESS_SUC_REFL] (* Unroll def; eliminate base case *)
  THEN REPEAT STRIP_TAC 
  THEN RES_TAC                  (* Expose nested IH *)
  THEN MATCH_MP_TAC LESS_TRANS  (* Use transitivity *)
  THEN Q.EXISTS_TAC`SUC(G x)`   (* Instantiate nested IH to goal *)
  THEN ASM_CRW_TAC[LESS_MONO])) (* Instantiate inner IH to goal, then done *);


val Geqns = RW_RULE[Gterminates] (#rules Gdef);
val Ginduction = RW_RULE[Gterminates] (#induction Gdef);


val Gcorrect = Q.store_thm("Gcorrect",
`!x. G x = 0`,
REC_INDUCT_TAC Ginduction 
  THEN RW_TAC[Geqns]);


(*---------------------------------------------------------------------------
 * Using the following partial correctness route seems easier, but you 
 * have to know what the correctness is! (Unlike the previous approach, 
 * where the necessary goal is automatically computed.) Of course, this
 * example is so trivial that there's no difficulty either way.
 *---------------------------------------------------------------------------*)

val LESS_0 = theorem "prim_rec" "LESS_0";

val lemma = 
Q.prove `!x. G x = 0`
(INDUCT_TAC 
   THEN ASM_RW_TAC[#rules Gdef,LESS_0]);

val Geqns2 = RW_RULE [Q.prove`!x. G x < SUC x` (RW_TAC[lemma,LESS_0])]
                     (#rules Gdef);


(*---------------------------------------------------------------------------
 * Now try a destructor-based approach. This complicates the proof, but 
 * not essentially. We manipulate the goal to trade destructors for 
 * constructors, then invoke the derived induction rule and proceed as
 * before.
 *---------------------------------------------------------------------------*)

val Hdef = 
Rfunction `$<`  `H x = ((x=0) => 0 | H(H(x-1)))`;

val lem = EQT_ELIM(ARITH_CONV (Term`SUC n - 1 = n`));
val lem1 = EQT_ELIM(ARITH_CONV (Term`~(x=0) ==> (SUC(x - 1) = x)`));

use"../utils.sml";

val Hterminates = Q.store_thm("Hterminates",
`!x. ~(x = 0) ==> H (x - 1) < x`,
GEN_CASES_TAC(theorem"arithmetic" "num_CASES") THEN RW_TAC[lem]
  THEN Q.ID_SPEC_TAC`n`
  THEN REC_INDUCT_TAC (#induction Hdef)
  THEN RW_TAC[lem1]
  THEN REPEAT STRIP_TAC
  THEN ONCE_RW_TAC[#rules Hdef] (* Unroll defn *)
  THEN COND_CASES_TAC
  THENL
  [ CONV_TAC ARITH_CONV,
    ASM_RW_TAC[]
      THEN MATCH_MP_TAC LESS_TRANS  (* Use transitivity *) 
      THEN Q.EXISTS_TAC`SUC (H(x-1))`   (* Instantiate nested IH to goal *) 
     THEN ASM_CRW_TAC[LESS_MONO] (* Instantiate inner IH to goal, then done *) 
  ]);

val Hrule = RW_RULE[Hterminates] (#rules Hdef);
val Hinduction  = RW_RULE[Hterminates] (#induction Hdef);

val Hcorrect = Q.store_thm("Hcorrect",
`!x. H x = 0`,
PROGRAM_TAC{induction = Hinduction, rules = Hrule}
  THENL [REFL_TAC, RES_TAC]);

val _ = html_theory"-";
