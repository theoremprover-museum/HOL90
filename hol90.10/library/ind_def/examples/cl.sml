(* =====================================================================*)
(* FILE		: cl.ml							*)
(* DESCRIPTION   : Creates the syntactic theory of combinatory logic and*)
(*		  defines reduction of terms in the logic. Proves the	*)
(*		  Church-Rosser theorem for this reduction relation.	*)
(*									*)
(* AUTHORS	: Tom Melham and Juanito Camilleri			*)
(* DATE		: 91.10.09						*)
(* =====================================================================*)

(* ---------------------------------------------------------------------*)
(* Open a new theory and load the inductive definitions library.	*)
(* ---------------------------------------------------------------------*)


(* load_library{lib = Sys_lib.ind_def_lib,theory = "cl"}; *)
open ind_defLib;

infix ##;
infix THEN THENL ORELSE THENC ORELSEC;

(* An attempt to make the rule sets a little less cluttered-looking. *)

val TERM = Parse.term_parser
val TYPE = Parse.type_parser;
val TY_ANTIQ = Term.ty_antiq o TYPE;

val relation = TY_ANTIQ`:'a -> 'a -> bool`;

infix 5 -------------------------------------------------------------------;
fun (x ------------------------------------------------------------------- y)
    = (x,y);

val new_inductive_definition = fn{name, fixity, patt,rules} =>
  new_inductive_definition
    {name = name, fixity = fixity, 
     patt = (TERM ## map TERM) patt,
     rules = map (fn((H,S),C) => {hypotheses=H,side_conditions=S,conclusion=C})
                 (map ((map TERM ## map TERM) ## TERM) rules)};


new_theory"cl";
(* =====================================================================*)
(* Syntax of the combinatory logic.					*)
(* =====================================================================*)

(* ---------------------------------------------------------------------*)
(* The recursive types package is used to define the syntax of terms in *)
(* combinatory logic. The syntax is:					*)
(*									*)
(*    U ::=   s  |  k  |  U1 # U2					*)
(*                                                                      *)
(* where U, U1, and U2 range over terms. In higher order logic, terms of*)
(* combinatory logic are represented by the following constructors of a	*)
(* recursive type cl:							*)
(*						                        *)
(*    s:cl,  k:cl, and #:cl -> cl -> cl                                 *)
(*									*)
(* We are unfortunately prevented from the using upper-case letter S, as*)
(* this is already a constant in the built-in HOL theory hierarchy.     *)
(* ---------------------------------------------------------------------*)

val cl = define_type{name="cl",
                     type_spec = `cl = s | k | # of cl => cl`,
                     fixities = [Prefix, Prefix, Infix 800]};


(* =====================================================================*)
(* Standard syntactic theory, derived by the recursive types package.	*)
(* =====================================================================*)

(* ---------------------------------------------------------------------*)
(* Structural induction theorem for terms of combinatory logic .	*)
(* ---------------------------------------------------------------------*)

val induct = save_thm ("induct",prove_induction_thm cl);

(* ---------------------------------------------------------------------*)
(* Exhaustive case analysis theorem for terms of combinatory logic.	*)
(* ---------------------------------------------------------------------*)

val cases = save_thm ("cases", prove_cases_thm induct);

(* ---------------------------------------------------------------------*)
(* Prove that the application constructor is one-to-one.		*)
(* ---------------------------------------------------------------------*)

val ap11 = save_thm("ap11", prove_constructors_one_one cl);

(* ---------------------------------------------------------------------*)
(* Prove that the constructors yield syntactically distinct values. One	*)
(* typically needs all symmetric forms of the inequalities.		*)
(* ---------------------------------------------------------------------*)

val distinct =
    let val ths = CONJUNCTS (prove_constructors_distinct cl)
        val rths = map (GEN_ALL o NOT_EQ_SYM o SPEC_ALL) ths 
    in save_thm("distinct", LIST_CONJ (ths @ rths))
    end;


(* =====================================================================*)
(* Inductive definition of reduction of CL terms.			*)
(* =====================================================================*)

(* ---------------------------------------------------------------------*)
(* Definition of weak contraction.					*)
(*                                                                      *)
(* The one-step contraction relation -> is inductively defined by the 	*)
(* rules shown below.  This is the "weak contraction' relation of 	*)
(* Hindley and Seldin.  A weak redex is a term of the form Kxy or Sxyz. *)
(* A term U weakly contracts to V (i.e. U ---> V) if V can be obtained  *)
(* by replacing one occurrence of a redex in U, where a redex Kxy is	*)
(* replaced by x and a redex Sxyz is replaced by (xz)yz.  The first two *)
(* rules in the inductive definition given below define the contraction *) 
(* of redexes, the second two rules define the contraction of subterms.	*)
(* ---------------------------------------------------------------------*)


val {desc=Crules,induction_thm = Cind} =
let val CTR = TERM`---> :cl->cl->bool`
in
new_inductive_definition {name="contract", fixity = Infix 700,
   patt = (`^CTR U V`, []),
   rules=[



      ([],                                                            [])
      -------------------------------------------------------------------
                          `^CTR ((k # x) # y) x`                        ,


      ([],                                                            [])
      -------------------------------------------------------------------
                `^CTR (((s # x) # y) # z)  ((x # z) # (y # z))`         ,



      ([                       `^CTR x y`                           ],[])
      -------------------------------------------------------------------
                         `^CTR (x # z) (y # z)`                         ,



      ([                       `^CTR x y`                           ],[])
      -------------------------------------------------------------------
                          `^CTR (z # x) (z # y)`                       ]}
end;



(* ---------------------------------------------------------------------*)
(* Stronger form of rule induction.					*)
(* ---------------------------------------------------------------------*)

val Csind = derive_strong_induction (Crules,Cind);

(* ---------------------------------------------------------------------*)
(* Standard rule induction tactic for --->.  This uses the weaker form  *)
(* of the rule induction theorem, and both premisses and side conditions*)
(* are just assumed (in stripped form).  				*)
(* ---------------------------------------------------------------------*)

val C_INDUCT_TAC =
    RULE_INDUCT_THEN Cind STRIP_ASSUME_TAC STRIP_ASSUME_TAC;

(* ---------------------------------------------------------------------*)
(* Prove the case analysis theorem for the contraction rules.		*)
(* ---------------------------------------------------------------------*)

val Ccases = derive_cases_thm (Crules,Cind);

(* ---------------------------------------------------------------------*)
(* Tactics for each of the contraction rules.				*)
(* ---------------------------------------------------------------------*)
val [Ck_TAC,Cs_TAC,LCap_TAC,RCap_TAC] = map RULE_TAC Crules;


(* ---------------------------------------------------------------------*)
(* The weak reduction relation on terms in combinatory logic is just the*)
(* reflexive-transitive closure of --->.  We define reflexive-transitive*)
(* closure inductively as follows, and then define the weak reduction 	*)
(* relation --->* to be RTC --->.					*)
(* ---------------------------------------------------------------------*)

val {desc=RTCrules,induction_thm = RTCind} =
let val RTC = TERM`RTC:('a->'a->bool)->'a->'a->bool` 
in
new_inductive_definition{name="RTC", fixity=Prefix,
   patt=(`^RTC R x y`, [`R:^relation`]),
   rules=[


      ([],[                 `(R:^relation) x y`                        ])
      -------------------------------------------------------------------
                               `^RTC R x y`                             ,


      ([],                                                            [])
      -------------------------------------------------------------------
                               `^RTC R x x`                             ,



      ([         `^RTC R x z`,             `^RTC R z y`],             [])
      -------------------------------------------------------------------
                              `^RTC R x y`                             ]}
end;



(* ---------------------------------------------------------------------*)
(* Standard rule induction tactic for RTC.				*)
(* ---------------------------------------------------------------------*)

val RTC_INDUCT_TAC =
    RULE_INDUCT_THEN RTCind STRIP_ASSUME_TAC STRIP_ASSUME_TAC;

(* ---------------------------------------------------------------------*)
(* Tactics for the RTC rules.						*)
(* ---------------------------------------------------------------------*)

val [RTC_IN_TAC,RTC_REFL_TAC,RTC_TRANS_TAC] = map RULE_TAC RTCrules;


(* ---------------------------------------------------------------------*)
(* Case analysis theorem for RTC.					*)
(* ---------------------------------------------------------------------*)

val RTCcases = derive_cases_thm (RTCrules,RTCind);


(* ---------------------------------------------------------------------*)
(* Definition of weak reduction.					*)
(* ---------------------------------------------------------------------*)

val reduce = new_infix_definition("reduce", (--`--->* = RTC $--->`--),700);


(* =====================================================================*)
(* Theorem : ---> does not have the Church-Rosser property. 		*)
(*									*)
(* We wish to prove that weak reduction is Church-Rosser.  If we could 	*)
(* prove that the one-step contraction ---> has this property, then we	*)
(* could also show that reduction does, since taking the reflexive-	*)
(* transitive closure of a relation preserves the Church-Rosser theorem.*)
(* Unfortunately, however, ---> is not Church- Rosser, as the following	*)
(* counterexample shows.	  					*)
(*									*)
(* The counter example is ki(ii) where i = skk. We have that:		*)
(*									*)
(*             ki(ii)							*)
(*              /  \							*)
(*             /    \							*)
(*            /      \							*)
(*           i    ki(ki)(ki)						*)
(*                   /							*)
(*                  /							*)
(*                 /							*)
(*                i							*)
(*									*)
(* But i doesn't contract to i (or indeed to any other term).		*)
(* =====================================================================*)

(* ---------------------------------------------------------------------*)
(* We first define i to be skk.						*)
(* ---------------------------------------------------------------------*)

val iDEF = new_definition ("iDEF", (--`i = (s # k) # k`--));

(* ---------------------------------------------------------------------*)
(* Given the tactics defined above for each rule, it is straightforward *)
(* to construct a tactic for automatically checking an assertion that	*)
(* one term contracts to another.  The tactic just does a search for a  *)
(* proof using the rules for --->.					*)
(* ---------------------------------------------------------------------*)

fun CONT_TAC g =
   FIRST [Cs_TAC,
          Ck_TAC,
          LCap_TAC THEN CONT_TAC,
          RCap_TAC THEN CONT_TAC] g 
   handle _ => raise HOL_ERR{origin_function = "CONT_TAC",
                             message = "", origin_structure = ""};


(* ---------------------------------------------------------------------*)
(* We can now use this tactic to show the following lemmas:		*)
(*									*)
(*    1) ki(ii) ---> i 							*)
(*    2) ki(ii) ---> ki((ki)(ki))					*)
(*    3) ki((ki)(ki)) ---> i						*)
(* ---------------------------------------------------------------------*)

val lemma1 = prove
    ((--`((k # i) # (i # i)) ---> i`--),
     CONT_TAC);

val lemma2 =
    prove
    ((--`((k # i) # (i # i)) ---> (k # i) # ((k # i) # (k # i))`--),
     SUBST1_TAC iDEF THEN CONT_TAC);

val lemma3 =
    prove
    ((--`((k # i) # ((k # i) # (k # i))) ---> i`--),
     SUBST1_TAC iDEF THEN CONT_TAC);

(* ---------------------------------------------------------------------*)
(* For the proof that ~?U. i ---> U, we construct some infrastructure 	*)
(* for a general way of dealing with contractability assertions.  The   *)
(* core of this consists of a tactic that rewrites assertions of the    *)
(* form (--`U ---> V`--) with the cases theorem for ---> :		*)
(* 									*)
(*   |- !U V.								*)
(*       U ---> V =							*)
(*       (?y. U = (k # V) # y) \/					*)
(*       (?x y z. (U = ((s # x) # y) # z) /\ (V = (x # z) # (y # z))) \/ *)
(*       (?x y z. (U = x # z) /\ (V = y # z) /\ x ---> y) \/		*)
(*       (?x y z. (U = z # x) /\ (V = z # y) /\ x ---> y)		*)
(*									*)
(* The full method is as follows:					*)
(*									*)
(*   1) rewrite just once using the cases theorem			*)
(*									*)
(*        PURE_ONCE_REWRITE_TAC [Ccases]				*)
(*									*)
(*   2) simplify any equations between cl-terms that arise from step	*)
(*      1 by using distinctness and injectivity of application.  Also 	*)
(*      normalize conjunctions and disjunctions.			*)
(*									*)
(*        REWRITE_TAC [distinct,ap11,GSYM CONJ_ASSOC, LEFT_AND_OVER_OR] *)
(*									*)
(*   3) move any buried existential quantifiers outwards through 	*)
(*      conjunctions and inwards through disjunctions.			*)
(*									*)
(*        let outc = LEFT_AND_EXISTS_CONV ORELSEC RIGHT_AND_EXISTS_CONV *)
(*        CONV_TAC (REDEPTH_CONV outc) THEN				*)
(*        CONV_TAC (REDEPTH_CONV EXISTS_OR_CONV) 			*)
(*									*)
(*   4) eliminate redundant equations using REDUCE from ind_defs	*)
(*									*)
(*        CONV_TAC (ONCE_DEPTH_CONV REDUCE)				*)
(*									*)
(* The overall effect is one step of expansion with the cases theorem,	*)
(* followed by a renormalization step.  Repeat as often as needed, but  *)
(* note that REPEAT may loop.  Could guard step 1 with a stopping	*)
(* condition if necessary.  Note that the normal form is a disjunction  *)
(* of existentially-quantified conjunctions.				*)
(* ---------------------------------------------------------------------*)

val EXPAND_CASES_TAC =
   let val outc = LEFT_AND_EXISTS_CONV ORELSEC RIGHT_AND_EXISTS_CONV 
   in PURE_ONCE_REWRITE_TAC [Ccases] THEN
      REWRITE_TAC [distinct,ap11,GSYM CONJ_ASSOC, LEFT_AND_OVER_OR] THEN
      CONV_TAC (REDEPTH_CONV outc) THEN
      CONV_TAC (REDEPTH_CONV EXISTS_OR_CONV) THEN
      CONV_TAC (ONCE_DEPTH_CONV REDUCE)
   end;

(* ---------------------------------------------------------------------*)
(* We can now use this tactic to prove that i doesn't contract to any 	*)
(* term of combinatory logic.  Note that since the transition in fact	*)
(* does NOT hold, step 2 of EXPAND_CASES_TAC eventually solves the goal.*)
(* Hence we may use REPEAT here.					*)
(* ---------------------------------------------------------------------*)

val lemma4 =
    prove
    ((--`~?U. i ---> U`--),
     SUBST_TAC [iDEF] THEN REPEAT EXPAND_CASES_TAC);


(* ---------------------------------------------------------------------*)
(* We now have our counterexample to show that ---> does not have the	*)
(* Church-Rosser property.  We first define an abbreviation for the 	*)
(* assertion that a relation R has this property.			*)
(* ---------------------------------------------------------------------*)

val CR =
    new_definition
    ("CR",
      (--`CR (R: 'a -> 'a -> bool) =
       !a b. R a b ==> !c. R a c ==> ?d. R b d /\ R c d`--));

(* ---------------------------------------------------------------------*)
(* Use the counterexample to show that ---> is not Church-Rosser.	*)
(* The conversion NOT_CONV moves negations inwards through quantifiers,	*)
(* applies Demorgan's laws where ever possible, and simplifies ~~P to P.*)
(* ---------------------------------------------------------------------*)

val NOT_CONV =
   let val ths = CONJUNCTS(SPEC_ALL DE_MORGAN_THM)
       val rcnv = map REWR_CONV (CONJUNCT1 NOT_CLAUSES :: ths) 
   in REDEPTH_CONV (FIRST_CONV ([NOT_FORALL_CONV, NOT_EXISTS_CONV] @ rcnv))
   end;

val NOT_C_CR =
    store_thm
    ("NOT_C_CR",
     (--`~CR($--->)`--),
     PURE_REWRITE_TAC [CR,IMP_DISJ_THM] THEN
     CONV_TAC NOT_CONV THEN
     EXISTS_TAC (--`(k # i) # (i # i)`--) THEN
     EXISTS_TAC (--`(k # i) # ((k # i) # (k # i))`--) THEN
     REWRITE_TAC [lemma2] THEN
     EXISTS_TAC (--`i`--) THEN
     REWRITE_TAC [lemma1,CONV_RULE NOT_EXISTS_CONV lemma4]);

(* =====================================================================*)
(* Inductive definition of parallel reduction of CL terms		*)
(* =====================================================================*)

(* --------------------------------------------------------------------- *)
(* Definition of one-step parallel contraction.				 *)
(* 									 *)
(* This one-step contraction relation has the Church-Rosser property,    *)
(* and its transitive closure (parallel reduction) therefore also does.  *)
(* Moreover, parallel reduction and --->* are the same relation, so we can*)
(* prove the Church-Rosser theorem for --->* by proving it for parallel	 *)
(* reduction.  The inductive definition of one-step parallel contraction *)
(* is given below.  The allow any number of redexes among the subterms   *)
(* of a term to be contracted in a single step.				 *)
(* --------------------------------------------------------------------- *)


val {desc=PCrules,induction_thm = PCind} =
let val PCTR = TERM`===> :cl->cl->bool` 
in
new_inductive_definition{name="pcontract", fixity = Infix 700,
   patt=(`^PCTR U V`, []),
   rules=[


      ([],                                                            [])
      -------------------------------------------------------------------
                                 `^PCTR x x`                            ,



      ([],                                                            [])
      -------------------------------------------------------------------
                          `^PCTR ((k # x) # y) x`                       ,


      ([],                                                            [])
      -------------------------------------------------------------------
               `^PCTR (((s # x) # y) # z)  ((x # z) # (y # z))`         ,


      ([          `^PCTR w x`,             `^PCTR y z`              ],[])
      -------------------------------------------------------------------
                         `^PCTR (w # y) (x # z)`                        ]}
end;



(* --------------------------------------------------------------------- *)
(* Stronger form of rule induction.					 *)
(* --------------------------------------------------------------------- *)

val PCsind = derive_strong_induction (PCrules,PCind);


(* --------------------------------------------------------------------- *)
(* Standard rule induction tactic for ===>.				 *)
(* --------------------------------------------------------------------- *)

val PC_INDUCT_TAC =
    RULE_INDUCT_THEN PCind STRIP_ASSUME_TAC STRIP_ASSUME_TAC;

(* ---------------------------------------------------------------------*)
(* Case analysis theorem for ===>.					*)
(* ---------------------------------------------------------------------*)

val PCcases = derive_cases_thm (PCrules,PCind);


(* ---------------------------------------------------------------------*)
(* Tactics for each of the parallel contraction rules.			*)
(* ---------------------------------------------------------------------*)
val [PC_REFL_TAC,PCk_TAC,PCs_TAC,PCap_TAC] = map RULE_TAC PCrules;

(* ---------------------------------------------------------------------*)
(* Given the tactics defined above for each rule, it is straightforward *)
(* to construct a tactic for automatically checking an assertion that	*)
(* one term contracts to another.  The tactic just does a search for a  *)
(* proof using the rules for ===>.					*)
(* ---------------------------------------------------------------------*)

fun PC_TAC g =
   FIRST [PC_REFL_TAC,
          PCk_TAC,
          PCs_TAC,
          PCap_TAC THEN PC_TAC] g handle _ => ALL_TAC g;


(* --------------------------------------------------------------------- *)
(* The weak reduction relation on terms in combinatory logic is just the *)
(* transitive closure of ===>.  Transitive is defined inductively as	*)
(* follows.  Note that the transitivity rule formulated as:		*)
(*									*)
(*            TC R x z 							*)
(*   R1:   -------------- R z y						*)
(*            TC R x y							*)
(*									*)
(* and not as								*)
(*									*)
(*          TC R x z   TC R z y						*)
(*   R2:  ------------------------					*)
(*              TC R x z						*)
(*									*)
(* This is because rule R1 gives a linear structure to rule inductions  *)
(* for transitive closure, which make the details of these proofs easier*)
(* to handle than the tree-shaped structure induced by rule R2.		*)
(*									*)
(* Once transitive closure has been defined, the parallel reduction 	*)
(* relation ===>* can just be defined to be TC ===>.			*)
(* ---------------------------------------------------------------------*)

val {desc = TCrules, induction_thm = TCind} =
let val TC = TERM`TC:('a->'a->bool)->'a->'a->bool` 
in
new_inductive_definition{name="TC" ,fixity=Prefix,
   patt=(`^TC R x y`, [`R:^relation`]),
   rules=[


      ([],[                    `(R:^relation) x y`                     ])
      -------------------------------------------------------------------
                                  `^TC R x y`                           ,


      ([             `^TC R x z`],           [`(R:^relation) z y`      ])
      -------------------------------------------------------------------
                                  `^TC R x y`                           ]}
end;


(* ---------------------------------------------------------------------*)
(* Standard rule induction tactic for TC.				*)
(* ---------------------------------------------------------------------*)

val TC_INDUCT_TAC =
    RULE_INDUCT_THEN TCind STRIP_ASSUME_TAC STRIP_ASSUME_TAC;


(* ---------------------------------------------------------------------*)
(* Tactics for the TC rules.						*)
(* ---------------------------------------------------------------------*)

val [TC_IN_TAC,TC_TRANS_TAC] = map RULE_TAC TCrules;


(* ---------------------------------------------------------------------*)
(* Strong form of rule induction for TC.				*)
(* ---------------------------------------------------------------------*)

val TCsind = derive_strong_induction (TCrules,TCind);


(* ---------------------------------------------------------------------*)
(* Now, define parallel reduction for terms of CL.			*)
(* ---------------------------------------------------------------------*)

val preduce = new_infix_definition("preduce", (--`===>* = TC $===>`--),700);

(* =====================================================================*)
(* Theorem: ===>* and --->* are the same relation.			*)
(* =====================================================================*)

(* ---------------------------------------------------------------------*)
(* The following sequence of lemmas show that the rules for the single	*)
(* step contraction ---> also hold its reflexive-transitive closure, 	*)
(* namely the relation --->*.  The proofs are trivial for the k and s	*)
(* axioms. For the two application rules, we need a simple induction	*)
(* on the rules defining RTC.  						*)
(* ---------------------------------------------------------------------*)

val Rk_THM =
    prove
    ((--`!a b. ((k # a) # b) --->* a`--),
     SUBST1_TAC reduce THEN
     RTC_IN_TAC THEN Ck_TAC);

val Rs_THM =
    prove
    ((--`!a b c. (((s # a) # b) # c) --->* ((a # c) # (b # c))`--),
     SUBST1_TAC reduce THEN
     RTC_IN_TAC THEN Cs_TAC);

val LRap_THM =
    prove
    ((--`!a b. a --->* b ==> !c. (a # c) --->* (b # c)`--),
     SUBST1_TAC reduce THEN
     RTC_INDUCT_TAC THEN REPEAT GEN_TAC THENL
     [RTC_IN_TAC THEN LCap_TAC THEN FIRST_ASSUM ACCEPT_TAC,
      RTC_REFL_TAC,
      RTC_TRANS_TAC THEN EXISTS_TAC (--`z # c`--) THEN ASM_REWRITE_TAC[]]);

val RRap_THM =
    prove
    ((--`!a b. a --->* b ==> !c. (c # a) --->* (c # b)`--),
     SUBST1_TAC reduce THEN
     RTC_INDUCT_TAC THEN REPEAT GEN_TAC THENL
     [RTC_IN_TAC THEN RCap_TAC THEN FIRST_ASSUM ACCEPT_TAC,
      RTC_REFL_TAC,
      RTC_TRANS_TAC THEN EXISTS_TAC (--`c # z`--) THEN ASM_REWRITE_TAC[]]);

(* --------------------------------------------------------------------- *)
(* To avoid having to expand --->* into RTC --->, we also prove that the *)
(* rules for reflexive-transitive closure hold of --->*.  The proofs are *)
(* completely trivial.							 *)
(* --------------------------------------------------------------------- *)

val CONT_IN_RED =
    prove
    ((--`!U V. U ---> V ==> U --->* V`--),
     REWRITE_TAC (reduce :: RTCrules));


val RED_REFL =
    prove
    ((--`!U. U --->* U`--),
     REWRITE_TAC (reduce :: RTCrules));


val RED_TRANS =
    prove
    ((--`!U V. (?W. U --->* W /\ W --->* V) ==> (U --->* V)`--),
     REWRITE_TAC (reduce :: RTCrules));


(* ---------------------------------------------------------------------  *)
(* We can now use these lemmas to prove that the relation ===>* is a 	  *)
(* subset of --->*. The proof has two parts. The first is to show that if *)
(* there is a one-step parallel reduction U ===> V, then U --->* V. Given *)
(* the lemmas proved above, it is easy to show that --->* is closed under *)
(* the rules that define ===>, and hence by rule induction that ===> is	  *)
(* a subset of --->*.							  *)
(* ---------------------------------------------------------------------  *)


val PCONT_SUB_RED =
    prove
    ((--`!U V. U ===> V ==> U --->* V`--),
     PC_INDUCT_TAC THEN REPEAT GEN_TAC THENL
     [MATCH_ACCEPT_TAC RED_REFL,
      MATCH_ACCEPT_TAC Rk_THM,
      MATCH_ACCEPT_TAC Rs_THM,
      MATCH_MP_TAC RED_TRANS THEN
      EXISTS_TAC (--`(x # y)`--) THEN CONJ_TAC THENL
      [IMP_RES_THEN (TRY o MATCH_ACCEPT_TAC) LRap_THM,
       IMP_RES_THEN (TRY o MATCH_ACCEPT_TAC) RRap_THM]]);

(* --------------------------------------------------------------------- *)
(* Given this result, one can then prove that ===>* is a subset of --->* *)
(* by rule induction.  The previous lemma just states that the relation  *)
(* --->* is closed under the inclusion rule for TC ===>. And one can also*)
(* prove that --->* is closed under the transitivity rule, since we have *)
(* already above proved that --->* is transitive.  Hence, by rule 	 *)
(* induction of transitive closure, TC ===> is a subset of --->*.	 *)
(* --------------------------------------------------------------------- *)

val PRED_SUB_RED =
    prove
    ((--`!U V. (U ===>* V) ==> U --->* V`--),
     SUBST1_TAC preduce THEN
     TC_INDUCT_TAC THEN REPEAT GEN_TAC THEN
     IMP_RES_TAC PCONT_SUB_RED THEN
     IMP_RES_TAC RED_TRANS);


(* --------------------------------------------------------------------- *)
(* The proof of the converse inclusion, that --->* is a subset of ===>*, *)
(* is similar.  Again, we begin with a series of lemmas which establish	 *)
(* that the rules defining ===> hold for its transitive closure ===>*.	 *)
(* --------------------------------------------------------------------- *)

val PRk_THM =
    prove
    ((--`!a b. ((k # a) # b) ===>* a`--),
     SUBST1_TAC preduce THEN
     TC_IN_TAC THEN PC_TAC);

val PRs_THM =
    prove
    ((--`!a b c. (((s # a) # b) # c) ===>* ((a # c) # (b # c))`--),
     SUBST1_TAC preduce THEN
     TC_IN_TAC THEN PC_TAC);

(* --------------------------------------------------------------------- *)
(* The application case is slightly trickier than the two analogous 	 *)
(* application theorems in the previous series of lemmas. Because of the *)
(* way the transitivity rule is formulated, a double rule induction is   *)
(* needed.								 *)
(* --------------------------------------------------------------------- *)

val PRap_THM =
    prove
    ((--`!a b. (a ===>* b) ==> 
               !c d. (c ===>* d) ==> 
                     ((a # c) ===>* (b # d))`--),
     SUBST1_TAC preduce THEN
     REPEAT TC_INDUCT_TAC THENL
     [TC_IN_TAC,
      TC_TRANS_TAC THEN EXISTS_TAC (--`y # z`--) THEN CONJ_TAC,
      TC_TRANS_TAC THEN EXISTS_TAC (--`z # x'`--) THEN CONJ_TAC THENL
      [FIRST_ASSUM MATCH_MP_TAC THEN TC_IN_TAC,ALL_TAC],
      TC_TRANS_TAC THEN EXISTS_TAC (--`y # z'`--) THEN CONJ_TAC] THEN
     PC_TAC THEN FIRST_ASSUM MATCH_ACCEPT_TAC);

(* --------------------------------------------------------------------- *)
(* We also need to show that ===>* is reflexive and transitive. Note that*)
(* in the transitivity case we need a careful formulation of the 	 *)
(* induction hypothesis, because of the way the transitivity rule for TC *)
(* is stated.  In particular, we induct on b ===>* c, rather than on	 *)
(* a ===>* b.								 *)
(* --------------------------------------------------------------------- *)

val PR_REFL =
    prove
    ((--`!U. U ===>* U`--),
     SUBST1_TAC preduce THEN
     TC_IN_TAC THEN PC_TAC);

val PR_TRANS = 
    prove
    ((--`!b c. (b ===>* c) ==> !a. (a ===>* b) ==> (a ===>* c)`--),
     SUBST1_TAC preduce THEN
     TC_INDUCT_TAC THEN REPEAT STRIP_TAC THENL
     [TC_TRANS_TAC THEN EXISTS_TAC (--`x:cl`--),
      TC_TRANS_TAC THEN EXISTS_TAC (--`z:cl`--) THEN RES_TAC] THEN
     ASM_REWRITE_TAC[]);


(* ---------------------------------------------------------------------  *)
(* We now show by rule induction that ---> is a subset of ===>*. We have  *)
(* already proved that the s and k rules for ---> also hold for ===>*.    *)
(* Futhermore, the two application rules for ---> follow easily for the   *)
(* relation ===>*, since the more general application rule holds for this *)
(* relation and since it is reflexive.					  *)
(* ---------------------------------------------------------------------  *)

val CONT_SUB_PRED =
    prove
    ((--`!U V. U ---> V ==> U ===>* V`--),
     C_INDUCT_TAC THEN REPEAT GEN_TAC THENL
     [MATCH_ACCEPT_TAC PRk_THM,
      MATCH_ACCEPT_TAC PRs_THM,
      ASSUME_TAC (SPEC (--`z:cl`--) PR_REFL) THEN IMP_RES_TAC PRap_THM,
      ASSUME_TAC (SPEC (--`z:cl`--) PR_REFL) THEN IMP_RES_TAC PRap_THM]);

(* ---------------------------------------------------------------------   *)
(* That --->* is a subset of ===>* now follows by rule induction.  We have *)
(* shown that ===>* contains ---> and that it is reflexive and transitive. *)
(* So ===>* is closed under the rules for RTC --->, and hence --->* is a   *)
(* subset of ===>*.							   *)
(* ---------------------------------------------------------------------   *)

val RED_SUB_PRED =
    prove
    ((--`!U V. U --->* V ==> U ===>* V`--),
     SUBST1_TAC reduce THEN
     RTC_INDUCT_TAC THEN REPEAT GEN_TAC THENL
     [IMP_RES_TAC CONT_SUB_PRED,
      MATCH_ACCEPT_TAC PR_REFL,
      IMP_RES_TAC PR_TRANS]);

(* --------------------------------------------------------------------- *)
(* The equality of --->* and ===>* follows immediately.			 *)
(* --------------------------------------------------------------------- *)

val RED_EQ_PRED =
    store_thm
    ("RED_EQ_PRED",
     (--`!U V. U --->* V = U ===>* V`--),
     REPEAT (STRIP_TAC ORELSE EQ_TAC) THENL
     [IMP_RES_TAC RED_SUB_PRED, IMP_RES_TAC PRED_SUB_RED]);

(* ===================================================================== *)
(* Theorem: taking the transitive closure preserves Church-Rosser.	 *)
(* ===================================================================== *)

(* ---------------------------------------------------------------------*)
(* Lemma: we can fill in any "strip' one transition wide.  That is, if	*)
(* R has the Church-Rosser rpoperty, then we have that 			*)
(*									*)
(*             a                                        a		*)
(*            / \				       / \		*)
(*  if       b   \       then there exists d st:      b   \		*)
(*                \                                    \   \		*)
(*                 c                                    \   c		*)
(*							 \ /		*)
(*							  d	        *)
(*									*)
(* The choice of formulation for the transitivity rule makes the proof a *)
(* straightforward rule indction down the a-to-c leg of the rectangle.   *)
(* --------------------------------------------------------------------- *)

val CR_LEMMA =
    store_thm
    ("CR_LEMMA",
     (--`!R:'a->'a->bool.
       CR R ==> !a c. TC R a c ==> !b. R a b ==> ?d. TC R b d /\ R c d`--),
     GEN_TAC THEN PURE_ONCE_REWRITE_TAC [CR] THEN STRIP_TAC THEN
     TC_INDUCT_TAC THEN REPEAT STRIP_TAC THEN RES_TAC THENL
     [EXISTS_TAC (--`d':'a`--) THEN CONJ_TAC THENL
      [TC_IN_TAC THEN FIRST_ASSUM ACCEPT_TAC, FIRST_ASSUM ACCEPT_TAC],
      EXISTS_TAC (--`d'':'a`--) THEN CONJ_TAC THENL
      [TC_TRANS_TAC THEN EXISTS_TAC (--`d:'a`--) THEN
       CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC,
       FIRST_ASSUM ACCEPT_TAC]]);


(* --------------------------------------------------------------------- *)
(* With a second rule induction, down the other "leg' of the diamond, we *)
(* can now prove that taking the transitive closure preserves the Church *)
(* Rosser property. The theorem is that if R is Church-Rosser, then:	*)
(*									*)
(*             a                                        a		*)
(*            / \				       / \		*)
(*  if       /   \       then there exists d st:      /   \		*)
(*          /     \                                  /     \		*)
(*         b       c                                b       c		*)
(*						     \     /		*)
(*						      \   /		*)
(*						       \ /		*)
(*						        d		*)
(*									*)
(* The proof is by rule induction on TC R a b.				*)
(* --------------------------------------------------------------------- *)

val TC_PRESERVES_CR_THM = 
    prove
    ((--`!R:'a->'a->bool.
        CR R ==> 
           !a c. TC R a c ==> !b. TC R a b ==> ?d. TC R b d /\ TC R c d`--),
     GEN_TAC THEN STRIP_TAC THEN TC_INDUCT_TAC THEN
     REPEAT STRIP_TAC THENL
     [IMP_RES_TAC CR_LEMMA THEN
      IMP_RES_TAC (el 1 TCrules) THEN
      EXISTS_TAC (--`d:'a`--) THEN 
      CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC,
      RES_THEN (fn th => STRIP_ASSUME_TAC th THEN ASSUME_TAC th) THEN
      IMP_RES_TAC CR_LEMMA THEN
      EXISTS_TAC (--`d':'a`--) THEN CONJ_TAC THENL
      [TC_TRANS_TAC THEN EXISTS_TAC (--`d:'a`--) THEN
       CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC,
       FIRST_ASSUM ACCEPT_TAC]]);

val TC_PRESERVES_CR =
    store_thm
    ("TC_PRESERVES_CR",
     (--`!R:'a->'a->bool. CR R ==> CR (TC R)`--),
     REPEAT STRIP_TAC THEN
     PURE_ONCE_REWRITE_TAC [CR] THEN
     PURE_ONCE_REWRITE_TAC [CONJ_SYM] THEN
     MATCH_MP_TAC TC_PRESERVES_CR_THM THEN
     FIRST_ASSUM ACCEPT_TAC);

(* ===================================================================== *)
(* Theorem: the parallel contraction relation ===> is Church-Rosser.	 *)
(* ===================================================================== *)

(* --------------------------------------------------------------------- *)
(* We define a conversion EXPAND_PC_CASES_CONV for expanding with the 	 *)
(* cases theorem for ===>.  This is analogous to EXPAND_CASES_TAC above, *)
(* except that it's a conversion, and it is designed to fail for terms   *)
(* that do not contain at least one subterm (--`U ===> V`--) where U and *)
(* V are not both variables.  This condition means you can repeat        *)
(* (REPEATC) this conversion, and the resulting conversion will always   *)
(* halt.                                                                 *)
(* --------------------------------------------------------------------- *)

val EXPAND_PC_CASES_CONV =
   let val outc = LEFT_AND_EXISTS_CONV ORELSEC RIGHT_AND_EXISTS_CONV
       fun guard tm = 
          let val (_,[x,y]) = strip_comb tm 
          in if (is_var x andalso is_var y) 
             then raise HOL_ERR{origin_function="EXPAND_PC_CASES_CONV",
                                message="",origin_structure=""}
             else REWR_CONV PCcases tm
          end
   in CHANGED_CONV (ONCE_DEPTH_CONV guard) THENC
      REWRITE_CONV [distinct,ap11,GSYM CONJ_ASSOC, 
                    LEFT_AND_OVER_OR,RIGHT_AND_OVER_OR] THENC
      REDEPTH_CONV outc THENC
      REDEPTH_CONV EXISTS_OR_CONV THENC
      ONCE_DEPTH_CONV REDUCE
   end;

(* --------------------------------------------------------------------- *)
(* Now for the main theorem. The proof proceeds by strong rule induction *)
(* on the relation ===>.  The four cases in the induction are:		*)
(*									*)
(*  1) (--`(w # y) ===> c ==> (?d. (x # z) ===> d /\ c ===> d)`--)	*)
(*     [ (--`w ===> x`--) ]						*)
(*     [ (--`!c. w ===> c ==> (?d. x ===> d /\ c ===> d)`--) ]		*)
(*     [ (--`y ===> z`--) ]						*)
(*     [ (--`!c. y ===> c ==> (?d. z ===> d /\ c ===> d)`--) ]		*)
(*									*)
(*  2) (--`(((s # x) # y) # z) ===> c ==>				*)
(*      (?d. ((x # z) # (y # z)) ===> d /\ c ===> d)`--)		*)
(*									*)
(*  3) (--`((k # x) # y) ===> c ==> (?d. x ===> d /\ c ===> d)`--)	*)
(*									*)
(*  4) (--`x ===> c ==> (?d. x ===> d /\ c ===> d)`--)			*)
(*                                                                      *)
(* Cases 2,3 and 4 are solved by case analysis (using PCcases) on the 	*)
(* antecedent, followed by straightforward search for the proof of the	*)
(* consequent using the tactics for ===>.  Case 1 is solved also by	*)
(* first analysing the antecedent by PCcases followed by search for the *)
(* proof.  In two sub-cases, however, one needs to do a case analysis	*)
(* on the strong induction assumption.  See the proof below for details.*)
(* ---------------------------------------------------------------------*)


val CR_THEOREM = prove (--`CR $===>`--,
   let val ecnv = REPEATC EXPAND_PC_CASES_CONV 
       fun ttac th g = SUBST_ALL_TAC th g  handle _ => ASSUME_TAC th g 
       val mkcases = REPEAT_TCL STRIP_THM_THEN ttac 
       val STRIP_PC_TAC = REPEAT STRIP_TAC THEN PC_TAC THEN
                          TRY(FIRST_ASSUM MATCH_ACCEPT_TAC) 
   in PURE_ONCE_REWRITE_TAC [CR] THEN
      RULE_INDUCT_THEN PCsind STRIP_ASSUME_TAC STRIP_ASSUME_TAC THEN
      REPEAT GEN_TAC THENL
      [DISCH_TAC THEN EXISTS_TAC (--`c:cl`--) THEN STRIP_PC_TAC,
       DISCH_THEN (mkcases o CONV_RULE ecnv) THENL
       map EXISTS_TAC [(--`x:cl`--),(--`c:cl`--),
                       (--`x:cl`--),(--`z':cl`--)] THEN STRIP_PC_TAC,
       DISCH_THEN (mkcases o CONV_RULE ecnv) THENL     
       map EXISTS_TAC [(--`((x#z)#(y#z))`--),
                       (--`((x#z)#(y#z))`--),
                       (--`((x#z')#(y#z'))`--),
                       (--`((x#z')#(z''#z'))`--),
                       (--`((z'''#z')#(z''#z'))`--)] THEN STRIP_PC_TAC,
       DISCH_THEN (mkcases o CONV_RULE ecnv) THENL
       [EXISTS_TAC (--`x#z`--) THEN STRIP_PC_TAC,
        let val cth = UNDISCH (fst(EQ_IMP_RULE (ecnv (--`(k#c) ===> x`--)))) 
        in DISJ_CASES_THEN (REPEAT_TCL STRIP_THM_THEN ttac) cth 
        end THENL map EXISTS_TAC [(--`c:cl`--),(--`z':cl`--)] THEN 
        STRIP_PC_TAC,
        let val cth = UNDISCH(fst(EQ_IMP_RULE(ecnv(--`(s#x')#y' ===> x`--)))) 
        in DISJ_CASES_THEN (REPEAT_TCL STRIP_THM_THEN ttac) cth 
        end THENL map EXISTS_TAC [(--`((x'#z)#(y'#z))`--),
                                  (--`((x'#z)#(z'#z))`--),
                                  (--`((z''#z)#(z'#z))`--)] THEN 
        STRIP_PC_TAC,
        RES_TAC THEN EXISTS_TAC (--`d''#d`--) THEN STRIP_PC_TAC]]
   end);

(* --------------------------------------------------------------------- *)
(* We now do the following trivial proof.				 *)
(* --------------------------------------------------------------------- *)

val preduce_HAS_CR =
    store_thm
    ("preduce_HAS_CR",
     (--`CR $===>*`--),
     REWRITE_TAC [preduce] THEN
     MATCH_MP_TAC TC_PRESERVES_CR THEN
     ACCEPT_TAC CR_THEOREM);

(* --------------------------------------------------------------------- *)
(* Q.E.D. 								 *)
(* --------------------------------------------------------------------- *)

val CHURCH_ROSSER = store_thm ("CHURCH_ROSSER",
   --`CR $--->*`--,
  let val th = EXT (GEN (--`U:cl`--) (EXT (SPEC (--`U:cl`--) RED_EQ_PRED))) 
  in REWRITE_TAC [th,preduce_HAS_CR]
  end);


(* --------------------------------------------------------------------- *)
(* End of example.							 *)
(* --------------------------------------------------------------------- *)

html_theory"-";
(* export_theory(); *)

