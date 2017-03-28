(* =====================================================================*)
(* FILE		: opsem.sml						*)
(* DESCRIPTION   : Creates a theory of the syntax and operational 	*)
(* 		  semantics of a very simple imperative programming 	*)
(* 		  language.  Illustrates the inductive definitions 	*)
(* 		  package with proofs that the evaluation relation for	*)
(*		  the given semantics is deterministic and that the 	*)
(*		  Hoare-logic rule for while loops follows from a 	*)
(*		  suitable definition of partial correctness.		*)
(*									*)
(* AUTHORS	: Tom Melham and Juanito Camilleri			*)
(* DATE		: 91.10.09						*)
(* TRANSLATED   : Dec. 27, 1992 Konrad Slind                            *)
(* =====================================================================*)

(* ---------------------------------------------------------------------*)
(* Open a new theory and load the required libraries.			*)
(* ---------------------------------------------------------------------*)

load_library{lib=Sys_lib.string_lib, theory = "opsem"};

load_library{lib = Sys_lib.ind_def_lib, theory = "-"};
open Inductive_def;

(* An attempt to make the rule sets a little less cluttered. *)

val TERM = Parse.term_parser
val TYPE = Parse.type_parser;
val TY_ANTIQ = Term.ty_antiq o TYPE;

infix 5 -------------------------------------------------------------------;
fun (x ------------------------------------------------------------------- y)
    = (x,y);

val new_inductive_definition = fn{name, fixity, patt, rules} =>
  new_inductive_definition
    {name = name, fixity = fixity, 
     patt = (TERM ## map TERM) patt,
     rules = map (fn((H,S),C) => {hypotheses=H,side_conditions=S,conclusion=C})
                 (map ((map TERM ## map TERM) ## TERM) rules)};


(* ===================================================================== *)
(* Syntax of the programming language.					 *)
(* ===================================================================== *)

(* --------------------------------------------------------------------- *)
(* Program variables will be represented by strings, and states will be  *)
(* modelled by functions from program variables to natural numbers.	 *)
(* --------------------------------------------------------------------- *)

val state = TY_ANTIQ`:string->num`;

(* --------------------------------------------------------------------- *)
(* Natural number expressions and boolean expressions will just be 	 *)
(* modelled by total functions from states to numbers and booleans       *)
(* respectively.  This simplification allows us to concentrate in this   *)
(* example on defining the semantics of commands.			 *)
(* --------------------------------------------------------------------- *)

val nexp = TY_ANTIQ`:^state -> num`;
val bexp = TY_ANTIQ`:^state -> bool`;

(* ---------------------------------------------------------------------*)
(* We can now use the recursive types package to define the syntax of   *)
(* commands (or "programs').  We have the following types of commands:  *)
(*									*)
(*    C ::=   skip                     (does nothing)			*)
(*          | V := E                   (assignment)          		*)
(*          | C1 ; C2                  (sequencing)           		*)
(*          | if B then C1 else C2     (conditional)			*)
(*          | while B do C             (repetition)			*)
(*                                                                      *)
(* where V ranges over program varibles, E ranges over natural number	*)
(* expressions, B ranges over boolean expressions, and C, C1 and C2     *)
(* range over commands.  						*)
(*									*)
(* In the logic, we represent this abstract syntax with a set of prefix *)
(* type constructors. So we have:					*)
(*						                        *)
(*    V := E                  represented by `assign V E`		*)
(*    C1 ; C2                 represented by `seq C1 C2`		*)
(*    if B then C1 else C2    represented by `if B C1 C2`		*)
(*    while B do C            represented by `while B C`		*)
(*									*)
(* For notational clarity, we later introduce two constants := and ; as *)
(* infix abbreviations for assign and seq.  This can't be done here just*)
(* because define_type doesn't suppport infix constructors.  		*)
(*                                                                      *)
(* Now it does. kls.Dec.1992                                            *)
(* ---------------------------------------------------------------------*)

val comm = 
  define_type{name="comm",
              type_spec = `comm = skip 
                                | := of string => ^nexp 
                                | ;; of comm => comm
                                | if of ^bexp => comm => comm
                                | while of ^bexp => comm`,
              fixities = [Prefix,Infix 400, Infix 350, Prefix, Prefix]};


(* =====================================================================*)
(* Standard syntactic theory, derived by the recursive types package.	*)
(* =====================================================================*)

(* ---------------------------------------------------------------------*)
(* Structural induction theorem for commands.				*)
(* ---------------------------------------------------------------------*)

val induct = save_thm ("induct",prove_induction_thm comm);

(* ---------------------------------------------------------------------*)
(* Exhaustive case analysis theorem for commands.			*)
(* ---------------------------------------------------------------------*)

val cases = save_thm ("cases", prove_cases_thm induct);

(* ---------------------------------------------------------------------*)
(* Prove that the abstract syntax constructors are one-to-one.		*)
(* ---------------------------------------------------------------------*)

val const11 = 
    let val [assign11,seq11,if11,while11] =
        (CONJUNCTS (prove_constructors_one_one comm)) 
    in map save_thm [("assign11",assign11),
                     ("seq11",seq11),
                     ("if11",if11),
                     ("while11",while11)]
    end;


(* ---------------------------------------------------------------------  *)
(* Prove that the constructors yield syntactically distinct values. Note  *)
(* that one typically needs symmetric forms of the inequalities, so 	  *)
(* these	are constructed here and grouped togther into one theorem.*)
(* ---------------------------------------------------------------------- *)

val distinct =
    let val ths = CONJUNCTS (prove_constructors_distinct comm)
        val rths = map (GEN_ALL o NOT_EQ_SYM o SPEC_ALL) ths 
    in save_thm("distinct", LIST_CONJ (ths @ rths))
    end;

(* ===================================================================== *)
(* Definition of the operational semantics.				 *)
(* ===================================================================== *)

(* ---------------------------------------------------------------------*)
(* The semantics of commands will be given by an evaluation relation	*)
(*									*)
(*       EVAL : comm -> state -> state -> bool     			*)
(*									*)
(* defined inductively such that 					*)
(*									*)
(*       EVAL C s1 s2							*)
(*									*)
(* holds exactly when executing the command C in the initial state s1 	*)
(* terminates in the final state s2. The evaluation relation is defined *)
(* inductively by the set of rules shown below.  			*)
(* ---------------------------------------------------------------------*)

val {desc=rules,induction_thm=ind} = 
let val EVAL = TERM`EVAL : comm -> ^state -> ^state -> bool`
in
new_inductive_definition{name="trans", fixity=Prefix,
   patt = (`^EVAL C s1 s2`, []),
   rules=[

      ([],                                                            [])
      -------------------------------------------------------------------
                           `^EVAL skip s s`                             ,


      ([],                                                            [])
      -------------------------------------------------------------------
                 `^EVAL (V := E) s (\v. (v=V) => E s | s v)`            ,



      ([        `^EVAL C1 s1 s2`,         `^EVAL C2 s2 s3`          ],[])
      -------------------------------------------------------------------
                         `^EVAL (C1;;C2) s1 s3`                         ,



      ([`                     ^EVAL C1 s1 s2`         ],[`(B:^bexp) s1`])
      -------------------------------------------------------------------
                         `^EVAL (if B C1 C2) s1 s2`                     ,



      ([                     `^EVAL C2 s1 s2`      ],  [`~(B:^bexp) s1`])
      -------------------------------------------------------------------
                        `^EVAL (if B C1 C2) s1 s2`                      ,


      ([],[                  `~(B:^bexp) s`                            ])
      -------------------------------------------------------------------
                          `^EVAL (while B C) s s`                        ,



      ([`^EVAL C s1 s2`,     `^EVAL (while B C) s2 s3`], [`(B:^bexp) s1`])
      -------------------------------------------------------------------
                        `^EVAL (while B C) s1 s3`                        ]}
end;

(* --------------------------------------------------------------------- *)
(* Stronger form of rule induction.					 *)
(* --------------------------------------------------------------------- *)

val sind = derive_strong_induction(rules,ind);

(* ---------------------------------------------------------------------*)
(* Construct the standard rule induction tactic for EVAL.  This uses	*)
(* the "weaker' form of the rule induction theorem, and both premisses	*)
(* and side conditions are simply assumed (in stripped form).  This 	*)
(* served for many proofs, but when a more elaborate treatment of	*)
(* premisses or side conditions is needed, or when the stronger form of	*)
(* induction is required, a specialized  rule induction tactic is	*)
(* constructed on the fly.						*)
(* ---------------------------------------------------------------------*)

val RULE_INDUCT_TAC =
    RULE_INDUCT_THEN ind STRIP_ASSUME_TAC STRIP_ASSUME_TAC;

(* ---------------------------------------------------------------------*)
(* Prove the case analysis theorem for the evaluation rules.		*)
(* ---------------------------------------------------------------------*)

val ecases = derive_cases_thm (rules,ind);

(* =====================================================================*)
(* Derivation of backwards case analysis theorems for each rule.        *)
(*									*)
(* These theorems are consequences of the general case analysis theorem *)
(* proved above.  They are used to justify formal reasoning in which the*)
(* rules are driven "backwards', inferring premisses from conclusions.  *)
(* One infers from the assertion that:					*)
(*									*)
(*    1: EVAL C s1 s2 							*)
(*									*)
(* for a specific command C (e.g. for C = (--`skip`--)) that the        *)
(* corresponding instance of the premisses of the rule(s) for C must    *)
(* also hold, since  (1) can hold only by virtue of being derivable by  *)
(* the rule for C. This kind of reasoning occurs frequently in proofs   *)
(* about operational semantics.  Formally, one must use the fact that   *)
(* the logical representations of syntactically different commands are  *)
(* distinct, a fact automatically proved by the recursive types package.*)
(* =====================================================================*)

(* ---------------------------------------------------------------------*)
(* The following rule is used to simplify special cases of the general  *)
(* exhaustive case analysis theorem, which looks something like:	*)
(*									*)
(*      |- !C s1 s2.							*)
(*          EVAL C s1 s2 =						*)
(*             (C = skip) ... \/					*)
(*             (?V E. (C = V := E) ...) \/				*)
(*             (?C1 C2 s2'. (C = C1 ; C2) ...) \/			*)
(*             (?C1 B C2. (C = if B C1 C2) /\ B s1 ...) \/		*)
(*             (?C2 B C1. (C = if B C1 C2) /\ ~B s1 ...) \/		*)
(*             (?B C'. (C = while B C') /\ ~B s1 ... ) \/		*)
(*             (?C' B s2'. (C = while B C') /\ B s1 ...)		*)
(*  									*)
(* If C is specialized to some particular syntactic form, for example   *)
(* to (--`C1;;C2`--), then most of the disjuncts in the conclusion become*)
(* just false because of the syntactic inequality of different commands.*)
(* These false can be simplified away by rewriting with the theorem	*)
(* distinct.  The disjuncts that match the command to which C is 	*)
(* specialized can also be simplified by rewriting with const11.  This  *)
(* changes equalities between similar commands, for example:		*)
(*									*)
(*    (C1 ;; C2) = (C1' ;; C2')						*)
(*									*)
(* to equalities between their coresponding constitutents:		*)
(*									*)
(*    C1 = C1'  /\  C2 = C2'						*)
(*									*)
(* These can then generally be used for substitution.			*)
(* ---------------------------------------------------------------------*)

val SIMPLIFY = REWRITE_RULE (distinct :: const11);

(* --------------------------------------------------------------------- *)
(* CASE_TAC : this is applicable to goals of the form:			 *)
(*									 *)
(*      TRANS C s1 s2 ==> P						 *)
(*									 *)
(* When applied to such a goal, the antecedant is matched to the general *)
(* case analysis theorem and a corresponding instance of its conclusion  *)
(* is obtained.  This is simplified using the SIMPLIFY rule described    *)
(* above and the result is assumed in stripped form.  Given this tactic, *)
(* the sequence of theorems given below are simple to prove.  The proofs *)
(* are fairly uniform; with a careful analysis of the regularities, one  *)
(* should be able to devise an automatic proof procedure for deriving    *)
(* sets of theorems of this type.					 *)
(* --------------------------------------------------------------------- *)

val CASE_TAC = DISCH_THEN 
               (STRIP_ASSUME_TAC o SIMPLIFY o ONCE_REWRITE_RULE[ecases]);

(* --------------------------------------------------------------------- *)
(* SKIP_THM : EVAL skip s1 s2 is provable only by the skip rule, which   *)
(* requires that s1 and s2 be the same state.				 *)
(* --------------------------------------------------------------------- *)

val SKIP_THM = store_thm("SKIP_THM",
     (--`!s1 s2. EVAL skip s1 s2 = (s1 = s2)`--),
     REPEAT GEN_TAC THEN EQ_TAC THENL
     [CASE_TAC THEN ASM_REWRITE_TAC [],
      DISCH_THEN SUBST1_TAC THEN MAP_FIRST RULE_TAC rules]);


(* --------------------------------------------------------------------- *)
(* ASSIGN_THM : EVAL (V := E) s1 s2 is provable only by the assignment	 *)
(* rule, which requires that s2 be the state s1 with V updated to E.	 *)
(* --------------------------------------------------------------------- *)

val ASSIGN_THM = store_thm ("ASSIGN_THM",
 (--`!s1 s2 V E. EVAL (V := E) s1 s2 = ((\v. ((v=V) => E s1 | s1 v)) = s2)`--),
     REPEAT GEN_TAC THEN EQ_TAC THENL
     [CASE_TAC THEN ASM_REWRITE_TAC [],
      DISCH_THEN (SUBST1_TAC o SYM) THEN MAP_FIRST RULE_TAC rules]);


(* --------------------------------------------------------------------- *)
(* SEQ_THM : EVAL (C1;C2) s1 s2 is provable only by the sequencing rule, *)
(* which requires that some intermediate state s3 exists such that C1    *)
(* in state s1 terminates in s3 and C3 in s3 terminates in s2.		 *)
(* --------------------------------------------------------------------- *)

val SEQ_THM = store_thm("SEQ_THM",
--`!s1 s2 C1 C2.EVAL (C1;;C2) s1 s2 = (?s3. EVAL C1 s1 s3 /\ EVAL C2 s3 s2)`--,
  REPEAT GEN_TAC THEN EQ_TAC THENL
  [CASE_TAC THEN EXISTS_TAC (--`s2':^state`--) THEN ASM_REWRITE_TAC [],
   DISCH_THEN (fn th => MAP_FIRST RULE_TAC rules THEN MATCH_ACCEPT_TAC th)]);


(* --------------------------------------------------------------------- *)
(* IF_T_THM : if B(s1) is true, then EVAL (if B C2 C2) s1 s2 is provable *)
(* only by the first conditional rule, which requires that C1 when	 *)
(* evaluated in s1 terminates in s2.					 *)
(* --------------------------------------------------------------------- *)

val IF_T_THM = store_thm ("IF_T_THM",
(--`!s1 s2 B C1 C2. B s1 ==> (EVAL (if B C1 C2) s1 s2 = EVAL C1 s1 s2)`--),
     REPEAT STRIP_TAC THEN EQ_TAC THENL
     [CASE_TAC THEN EVERY_ASSUM (TRY o SUBST_ALL_TAC) THENL
      [FIRST_ASSUM ACCEPT_TAC, RES_TAC],
      DISCH_TAC THEN MAP_FIRST RULE_TAC rules THEN FIRST_ASSUM ACCEPT_TAC]);


(* --------------------------------------------------------------------- *)
(* IF_F_THM : if B(s1) is false, then EVAL (if B C1 C2) s1 s2 is 	 *)
(* provable only by the second conditional rule, which requires that C2	 *)
(* when evaluated in s1 terminates in s2.				 *)
(* --------------------------------------------------------------------- *)

val IF_F_THM = store_thm ("IF_F_THM",
(--`!s1 s2 B C1 C2. ~B s1 ==> (EVAL (if B C1 C2) s1 s2 = EVAL C2 s1 s2)`--),
   REPEAT STRIP_TAC THEN EQ_TAC THENL
   [CASE_TAC THEN EVERY_ASSUM (TRY o SUBST_ALL_TAC) THENL
    [RES_TAC, FIRST_ASSUM ACCEPT_TAC],
     DISCH_TAC THEN MAP_FIRST RULE_TAC (rev rules) THEN
     FIRST_ASSUM ACCEPT_TAC]);


(* ---------------------------------------------------------------------*)
(* WHILE_T_THM : if B(s1) is true, then EVAL (while B C) s1 s2 is 	*)
(* provable only by the corresponding while rule, which requires that 	*)
(* there is an intermediate state s3 such that C in state s1 terminates *)
(* in s3, and while B do C in state s3 terminates in s2.		*)
(* ---------------------------------------------------------------------*)

val WHILE_T_THM = store_thm ("WHILE_T_THM",
     (--`!s1 s2 B C.
      B s1 ==> (EVAL (while B C) s1 s2 =
                (?s3. EVAL C s1 s3 /\ EVAL (while B C) s3 s2))`--),
   REPEAT STRIP_TAC THEN EQ_TAC THENL
   [CASE_TAC THEN EVERY_ASSUM (TRY o SUBST_ALL_TAC) THENL
    [RES_TAC,
     EXISTS_TAC (--`s2':^state`--) THEN CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC],
    STRIP_TAC THEN MAP_FIRST RULE_TAC (rev rules) THEN
    EXISTS_TAC (--`s3:^state`--) THEN
    REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC]);


(* ---------------------------------------------------------------------*)
(* WHILE_F_THM : if B(s1) is false, then EVAL (while B C) s1 s2 is	*)
(* provable only by the corresponding while rule, which requires that 	*)
(* s2 equals the original state s1					*)
(* ---------------------------------------------------------------------*)

val WHILE_F_THM = store_thm ("WHILE_F_THM",
     (--`!s1 s2 B C. ~B s1 ==> (EVAL (while B C) s1 s2 = (s1 = s2))`--),
     REPEAT STRIP_TAC THEN EQ_TAC THENL
     [CASE_TAC THENL
      [CONV_TAC SYM_CONV THEN FIRST_ASSUM ACCEPT_TAC,
       EVERY_ASSUM (TRY o SUBST_ALL_TAC) THEN RES_TAC],
      DISCH_THEN (SUBST1_TAC o SYM) THEN MAP_FIRST RULE_TAC rules THEN
      FIRST_ASSUM ACCEPT_TAC]);


(* ===================================================================== *)
(* THEOREM: the operational semantics is deterministic.			 *)
(*									 *)
(* Given the suite of theorems proved above, this proof is relatively    *)
(* strightforward.  The standard proof is by structural induction on C,  *)
(* but the proof by rule induction given below gives rise to a slightly  *)
(* easier analysis in each case of the induction.  There are, however,   *)
(* more cases---one per rule, rather than one per constructor.		 *)
(* ===================================================================== *)

val DETERMINISTIC = store_thm ("DETERMINISTIC",
(--`!C st1 st2. EVAL C st1 st2 ==> !st3. EVAL C st1 st3 ==> (st2 = st3)`--),
     RULE_INDUCT_TAC THEN REPEAT GEN_TAC THENL
     [REWRITE_TAC [SKIP_THM],
      REWRITE_TAC [ASSIGN_THM],
      PURE_ONCE_REWRITE_TAC [SEQ_THM] THEN STRIP_TAC THEN
      FIRST_ASSUM MATCH_MP_TAC THEN RES_TAC THEN ASM_REWRITE_TAC [],
      IMP_RES_TAC IF_T_THM THEN ASM_REWRITE_TAC [],
      IMP_RES_TAC IF_F_THM THEN ASM_REWRITE_TAC [],
      IMP_RES_TAC WHILE_F_THM THEN ASM_REWRITE_TAC [],
      IMP_RES_THEN (fn th =>  PURE_ONCE_REWRITE_TAC [th]) WHILE_T_THM THEN
      STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
      RES_TAC THEN ASM_REWRITE_TAC []]);


(* ===================================================================== *)
(* Definition of partial correctness and derivation of proof rules.	 *)
(* ===================================================================== *)

val SPEC_DEF = new_definition ("SPEC_DEF",
     (--`SPEC P C Q = !s1 s2. (P s1 /\ EVAL C s1 s2) ==> Q s2`--));

(* --------------------------------------------------------------------- *)
(* Proof of the while rule in Hoare logic.				 *)
(* --------------------------------------------------------------------- *)

(* --------------------------------------------------------------------- *)
(* In the following proofs, theorems of the form:			 *)
(*									 *)
(*     |- !y1...yn. (C x1 ... xn = C y1 ... yn) ==> tm[y1,...,yn]	 *)
(*									 *)
(* frequently arise, where C is one of the constructors of the data type *)
(* of commands.  The following theorem-tactic simplifies such theorems   *)
(* by specializing yi to xi and then removing the resulting trivially    *)
(* true antecedent.  The result is:					 *)
(*									 *)
(*     |- tm[x1,...,xn/y1,...,yn]					 *)
(*									 *)
(* which is passed to the theorem continuation function. The tactic just *)
(* discards theorems not of the form shown above.   For the while proof  *)
(* given below, this has the effect of thinning out useless induction	 *)
(* hypotheses of the form:						 *)
(*									 *)
(*     |- !B' C'. (C = while B' C') ==> tm[B',C']			 *)
(* 									 *)
(* These are just discarded.						 *)
(* --------------------------------------------------------------------- *)

fun REFL_MP_THEN ttac th =
   let val tm = lhs(#ant(dest_imp(snd(strip_forall(concl th)))))
   in ttac (MATCH_MP th (REFL tm))
   end handle _ => ALL_TAC;

(* --------------------------------------------------------------------- *)
(* The following lemma states that the condition B in while B C must be  *)
(* false upon termination of a while loop.  The proof is by a rule 	 *)
(* induction specialized to the while rule cases.  We show that the set	 *)
(* 									 *)
(*    {(while B C,s1,s2) | ~(B s2)} U {(C,s1,s2) | ~(C = while B' C')}   *)
(*									 *)
(* is closed under the rules for the evaluation relation. Note that this *)
(* formulation illustrates a general way of proving a property of some   *)
(* specific class of commands by rule induction.  One takes the union of *)
(* the set containing triples with the desired property and the set of   *)
(* all other triples whose command component is NOT an element of the    *)
(* class of commands of interest.					 *)
(*									 *)
(* The proof is trivial for all but the two while rules, since this set	 *)
(* contains all triples (C,s1,s2) for which C is not a while command.  	 *)
(* The subgoals corresponding to these cases are vacuously true, since 	 *)
(* they are implications with antecedents of the form (C = while B' C'), *)
(* where C is a command syntactically distinct from any while command.	 *)
(*									 *)
(* Showing that the above set is closed under the two while rules is     *)
(* likewise trivial.  For the while axiom, we get ~(B s2) immediately 	 *)
(* from the side condition. For the other while rule, the statement to	 *)
(* prove is just one of the induction hypotheses; since RULE_INDUCT_TAC  *)
(* uses STRIP_ASSUME_TAC on this hypothesis, this subgoal is solved	 *)
(* immediately.								 *)
(* --------------------------------------------------------------------- *)


val WHILE_LEMMA1 = TAC_PROOF(([],
 (--`!C s1 s2. EVAL C s1 s2 ==> !B' C'. (C = while B' C') ==> ~(B' s2)`--)),
     RULE_INDUCT_TAC THEN REWRITE_TAC (distinct :: const11) THEN
     REPEAT GEN_TAC THEN DISCH_THEN (STRIP_THM_THEN SUBST_ALL_TAC) THEN
     FIRST_ASSUM ACCEPT_TAC);

(* ---------------------------------------------------------------------*)
(* The second lemma deals with the invariant part of the Hoare proof 	*)
(* rule for while commands.  We show that if P is an invariant of C, 	*)
(* then it is also an invariant of while B C.  The proof is essentially *)
(* an induction on the number of applications of the evaluation rule for*)
(* while commands.  This is expressed as a rule induction, which 	*)
(* establishes that the set:						*)
(*									*)
(*    {(while B C,s1,s2) | P invariant of C ==> (P s1 ==> P s2)}	*)
(*									*)
(* is closed under the transition rules.  As in lemma 1, the rules for  *)
(* other kinds of commands are dealt with by taking the union of this 	*)
(* set with 								*)
(* 									*)
(*    {(C,s1,s2) | ~(C = while B' C')}					*)
(*									*)
(* Closure under evaluation rules other than the two rules for while is *)
(* therefore trivial, as outlined in the comments to lemma 1 above. 	*)
(*									*)
(* The proof in fact proceeds by strong rule induction.  With ordinary  *)
(* rule induction, one obtains hypotheses that are too weak to imply the*)
(* desired conclusion in the step case of the while rule.  To see why, 	*)
(* try replacing strong by weak induction in the tactic proof below.	*)
(*									*)
(* Note that REFL_MP_THEN is used to simplify the induction hypotheses  *)
(* before adding them to the assumption list.  This avoids having the 	*)
(* assumptions in an awkward form (try using ASSUME_TAC instead). Note	*)
(* also that in the case of the while axiom, the states s1 and s2 are	*)
(* identical, so the corresponding subgoal is trivial and is solved by	*)
(* the rewriting step.							*)
(* ---------------------------------------------------------------------*)

val WHILE_LEMMA2 =
    TAC_PROOF(([],
  --`!C s1 s2. 
     EVAL C s1 s2 ==>
     !B' C'. (C = while B' C') ==>
             (!s1 s2. P s1 /\ B' s1 /\ EVAL C' s1 s2 ==> P s2) ==>
             (P s1 ==> P s2)`--),
     RULE_INDUCT_THEN sind (REFL_MP_THEN ASSUME_TAC) ASSUME_TAC THEN 
     REWRITE_TAC (distinct :: const11) THEN REPEAT GEN_TAC THEN
     DISCH_THEN (STRIP_THM_THEN SUBST_ALL_TAC) THEN
     REPEAT STRIP_TAC THEN RES_TAC);

(* ---------------------------------------------------------------------*)
(* The proof rule for while commands in Hoare logic is:			*)
(*									*)
(*         |- {P /\ B} C {P}						*)
(*      ----------------------						*)
(*        |- {P} C {P /\ ~B}						*)
(* 									*)
(* Given the two lemmas proved above, it is trivial to prove this rule. *)
(* The antecedent of the rule is just the assumption of invariance of P *)
(* for C which occurs in lemma 2.  Note that REFL_MP_THEN is used to    *)
(* simplify the conclusions of the lemmas after one resolution step.	*)
(* ---------------------------------------------------------------------*)

val WHILE = store_thm ("WHILE",
     (--`!P C. SPEC (\s. P s /\ B s) C P ==>
            SPEC P (while B C) (\s. P s /\ ~B s)`--),
     PURE_ONCE_REWRITE_TAC [SPEC_DEF] THEN
     CONV_TAC (ONCE_DEPTH_CONV BETA_CONV) THEN
     PURE_ONCE_REWRITE_TAC [SYM(SPEC_ALL CONJ_ASSOC)] THEN
     REPEAT STRIP_TAC THENL
     [IMP_RES_THEN (REFL_MP_THEN IMP_RES_TAC) WHILE_LEMMA2,
      IMP_RES_THEN (REFL_MP_THEN IMP_RES_TAC) WHILE_LEMMA1]);

(* ---------------------------------------------------------------------*)
(* End of example.							*)
(* ---------------------------------------------------------------------*)

html_theory"-";
export_theory();

