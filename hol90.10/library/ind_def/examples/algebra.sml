(* ===================================================================== *)
(* File		: algebra.ml						 *)
(* DESCRIPTION  : Maximal trace semantics and transition semantics of a  *)
(*		  small process algebra.              			 *)
(*									 *)
(* AUTHORS	: Juanito Camilleri and Tom Melham		       	 *)
(* DATE		: 91.05.13						 *)
(* ===================================================================== *)


(* --------------------------------------------------------------------- *)
(* Open a new theory and load the inductive definitions library.	 *)
(* --------------------------------------------------------------------- *)



load_library{lib = Sys_lib.ind_def_lib, theory = "algebra"};
open Inductive_def;

(* --------------------------------------------------------------------- *)
(* Load the string library.               				 *)
(* --------------------------------------------------------------------- *)

load_library{lib = Sys_lib.string_lib, theory = "-"};


(* Declare ML bindings for the values of the builtin "list" theory       *)
val _ = add_theory_to_sml "list";

val TERM = Parse.term_parser
val TYPE = Parse.type_parser;
val TY_ANTIQ = Term.ty_antiq o TYPE;

infix 5 -------------------------------------------------------------------;
fun (x ------------------------------------------------------------------- y)
    = (x,y);

val new_inductive_definition = fn{name, fixity, patt,rules} =>
  new_inductive_definition
    {name = name, fixity = fixity, 
     patt = (TERM ## map TERM) patt,
     rules = map (fn((H,S),C) => {hypotheses=H,side_conditions=S,conclusion=C})
                 (map ((map TERM ## map TERM) ## TERM) rules)};


(* ===================================================================== *)
(* Syntax of a small process algebra		        		 *)
(* ===================================================================== *)

(* --------------------------------------------------------------------- *)
(* We use the recursive types package to define the syntax of a small	 *)
(* process algebra, with processes					 *)
(*									 *)
(*    agent  ::=   Nil                    [does nothing]		 *)
(*               | Pre  label agent       [prefix agent with label]	 *)
(*               | Sum  agent agent       [nondeterministic choice]	 *)
(*	         | Prod agent agent       [composition]			 *)
(*									 *)
(* The different syntactic classes of processes are thus represented by  *)
(* the constructors (constant functions):				 *)
(*									 *)
(*  Nil:agent, Pre:label->agent->agent, Sum and Prod:agent->agent->agent *)
(*									 *)
(* for the concrete data type :agent.  The type :label here is just an	 *)
(* abbreviation for :string.						 *)
(* --------------------------------------------------------------------- *)

(* new_type_abbrev ("label", (==`:string==)); *)
(* use ty_antiq and "antiquote it in hol90; it doesn't have type abbrevs *)
val  label = TY_ANTIQ`:string`;

val agent = define_type 
    {name = "agent",
     type_spec =  `agent =  Nil 
                         |  Pre of  ^label => agent
                         |  Sum of   agent => agent
                         |  Prod of  agent => agent`,
     fixities = [Prefix,Prefix,Prefix,Prefix]};

(* ===================================================================== *)
(* Standard syntactic theory, derived by the recursive types package.	 *)
(* ===================================================================== *)

(* --------------------------------------------------------------------- *)
(* prove structural induction theorem for agent.                         *)
(* --------------------------------------------------------------------- *)
val induct = save_thm ("induct",prove_induction_thm agent);

(* --------------------------------------------------------------------- *)
(* prove cases theorem for agent.                                        *)
(* --------------------------------------------------------------------- *)
val cases = save_thm ("cases", prove_cases_thm induct);

(* --------------------------------------------------------------------- *)
(* Prove that the constructors of the type :agent yield syntactically 	 *)
(* distinct values. One typically needs all symmetric forms of the	 *)
(* inequalities, so we package them all together here.			 *)
(* --------------------------------------------------------------------- *)
val distinct =
   let val ths = CONJUNCTS (prove_constructors_distinct agent)
       val rths = map (GEN_ALL o NOT_EQ_SYM o SPEC_ALL) ths
   in save_thm("distinct", LIST_CONJ (ths @ rths))
   end;

(* --------------------------------------------------------------------- *)
(* Prove that the constructors Pre, Sum and Prod are one-to-one.         *)
(* --------------------------------------------------------------------- *)
val agent11 =
   let val [Pre11,Sum11,Prod11] = (CONJUNCTS(prove_constructors_one_one agent))
   in map save_thm [("Pre11",Pre11),
                    ("Sum11",Sum11),
                    ("Prod11",Prod11)]
   end;

(* ===================================================================== *)
(* Definition of a maximal trace semantics for the process algebra.	 *)
(* ===================================================================== *)

(* --------------------------------------------------------------------- *)
(* Type abbreviation for traces.   These are just finite sequences of 	 *)
(* labels, represented here by lists.					 *)
(* --------------------------------------------------------------------- *)
(* new_type_abbrev ("trace", (==`:(label)list`==)); *)
val trace = TY_ANTIQ`:^label list`;

(* --------------------------------------------------------------------- *)
(* Inductive definition of a trace relation MTRACE.  This is defined so	 *)
(* that MTRACE P A means A is the maximal trace of the process P. The 	 *)
(* definition is done inductively by the rules given below.	     	 *)
(* --------------------------------------------------------------------- *)

val {desc=trules,induction_thm=tind} =
let val MTRACE = TERM`MTRACE:agent->^trace->bool`
in
new_inductive_definition{name="MTRACE_DEF", fixity = Prefix,
   patt=(`^MTRACE P A`, []),
   rules=[


      ([],                                                            [])
      -------------------------------------------------------------------
                            `^MTRACE Nil []`                            ,



      ([                      `^MTRACE P A`                         ],[])
      -------------------------------------------------------------------
                      `^MTRACE (Pre a P) (CONS a A)`                    ,



      ([                     `^MTRACE P A`                           ],[])
      -------------------------------------------------------------------
                          `^MTRACE (Sum P Q) A`                         ,



      ([                     `^MTRACE Q A`                          ],[])
      -------------------------------------------------------------------
                         `^MTRACE (Sum P Q) A`                          ,



      ([         `^MTRACE P A`,           `^MTRACE Q A`             ],[])
      -------------------------------------------------------------------
                         `^MTRACE (Prod P Q) A`                         ]}
end;

                  


(* --------------------------------------------------------------------- *)
(* Definition of a terminal process: one with [] as a maximal trace.	 *)
(* --------------------------------------------------------------------- *)

val TERMINAL_DEF =
    new_definition ("TERMINAL_DEF", (--`TERMINAL P = MTRACE P []`--));


(* --------------------------------------------------------------------- *)
(* Stronger form of rule induction.					 *)
(* --------------------------------------------------------------------- *)

val tsind = derive_strong_induction (trules,tind);

(* --------------------------------------------------------------------- *)
(* Standard rule induction tactic for MTRACE. This uses the weaker form  *)
(* of the rule induction theorem, and both premisses and side conditions *)
(* are just assumed (in stripped form).  				 *)
(* --------------------------------------------------------------------- *)

val MTRACE_INDUCT_TAC =
    RULE_INDUCT_THEN tind STRIP_ASSUME_TAC STRIP_ASSUME_TAC;

(* --------------------------------------------------------------------- *)
(* Prove the case analysis theorem for the rules defining MTRACE.	 *)
(* --------------------------------------------------------------------- *)

val tcases = derive_cases_thm (trules,tind);

(* --------------------------------------------------------------------- *)
(* Tactics for each of the rules defining MTRACE.			 *)
(* --------------------------------------------------------------------- *)
val [Nil_TAC,Pre_TAC,SumL_TAC,SumR_TAC,Prod_TAC] = map RULE_TAC trules;

(* --------------------------------------------------------------------- *)
(* Given the tactics defined above for each rule, we now define a tactic *)
(* that searches for a proof that a process has some particular maximal  *)
(* trace, given some assumptions about maximal traces.  Note that there	 *)
(* are two Sum rules, so our tactic may have to do some backtracking in  *)
(* the proof.  In addition to seaching using the MTRACE rules, the 	 *)
(* looks for solutions among the assumptions as well as back-chaining 	 *)
(* with any implications among the assumptions. The tactics fails unless *)
(* it completely solves the goal.					 *)
(* --------------------------------------------------------------------- *)

fun MTRACE_TAC g =
   (REPEAT STRIP_TAC THEN
    FIRST [Nil_TAC,
           FIRST_ASSUM MATCH_ACCEPT_TAC,
           Pre_TAC THEN MTRACE_TAC,
           SumL_TAC THEN MTRACE_TAC,
           SumR_TAC THEN MTRACE_TAC,
           Prod_TAC  THEN MTRACE_TAC,
   	   FIRST_ASSUM MATCH_MP_TAC THEN MTRACE_TAC]) g 
   handle _ => raise HOL_ERR{origin_function="MTRACE_TAC",
                             message="", origin_structure=""};

(* --------------------------------------------------------------------- *)
(* The following is a little rule for getting simplified instances of	 *)
(* the tcases theorem.  All it does is to specialize tcases to the 	 *)
(* supplied process, rewrite using the distinctness and injectivity of	 *)
(* constructors, and eliminate redundant equations using REDUCE. Examples*)
(* of using MTCASE are:							 *)
(*									 *)
(*   #MTCASE (--`Prod P Q`--);						 *)
(*   |- !P Q A. MTRACE(Prod P Q)A = MTRACE P A /\ MTRACE Q A		 *)
(*									 *)
(*   #MTCASE (--`Sum P Q`--);						 *)
(*   |- !P Q A. MTRACE(Sum P Q)A = MTRACE P A \/ MTRACE Q A		 *)
(*									 *)
(* --------------------------------------------------------------------- *)

val MTCASE =
   let val SIMPLIFY = REWRITE_RULE (distinct :: agent11)
   in fn tm => let val th1 = SIMPLIFY (SPEC tm tcases) 
               in GEN_ALL (CONV_RULE (ONCE_DEPTH_CONV REDUCE) th1)
               end
   end;

(* ===================================================================== *)
(* Inductive definition of a labelled transition system.                 *)
(* ===================================================================== *)

(* --------------------------------------------------------------------- *)
(* We now define a labelled transition relation TRANS P l Q to mean	 *)
(* there that process P can participate in action l and thereby evolve	 *)
(* into process Q.  The definition is done inductively, as usual.        *)
(* --------------------------------------------------------------------- *)

val {desc=lrules, induction_thm=lind} =
let val TRANS = TERM`TRANS: agent->^label->agent->bool`
in
new_inductive_definition{name="TRANS_DEF",fixity=Prefix,
   patt=(`^TRANS G b E`,[]),
   rules=[


      ([],                                                            [])
      -------------------------------------------------------------------
                          `^TRANS (Pre a Q) a Q`                        ,



      ([                     `^TRANS P a P'`                        ],[])
      -------------------------------------------------------------------
                          `^TRANS (Sum P Q) a P'`                       ,



      ([                     `^TRANS Q a Q'`                        ],[])
      -------------------------------------------------------------------
                          `^TRANS (Sum P Q) a Q'`                       ,



      ([        `^TRANS P a P'`,               `^TRANS Q a Q'`      ],[])
      -------------------------------------------------------------------
                      `^TRANS (Prod P Q) a (Prod P' Q')`               ]}
end;

(* --------------------------------------------------------------------- *)
(* Strong form of rule induction for TRANS.	      			 *)
(* --------------------------------------------------------------------- *)

val lsind = derive_strong_induction (lrules,lind);

(* --------------------------------------------------------------------- *)
(* Standard rule induction tactic for TRANS. This again just uses the	 *)
(* weaker form of rule induction theorem.  Both premisses and side 	 *)
(* conditions are assumed (in stripped form).  				 *)
(* --------------------------------------------------------------------- *)

val TRANS_INDUCT_TAC =
    RULE_INDUCT_THEN lind STRIP_ASSUME_TAC STRIP_ASSUME_TAC;

(* --------------------------------------------------------------------- *)
(* Cases theorem for TRANS. 						 *)
(* --------------------------------------------------------------------- *)

val lcases =  derive_cases_thm (lrules,lind);

(* --------------------------------------------------------------------- *)
(* Tactics for the TRANS rules.						 *)
(* --------------------------------------------------------------------- *)
val [TPre_TAC,TSumL_TAC,TSumR_TAC,TProd_TAC] = map RULE_TAC lrules;

(* --------------------------------------------------------------------- *)
(* Given the tactics defined above for each rule, we construct a tactic  *)
(* that searches for a proof of TRANS P a Q, with becktracking in the 	 *)
(* Sum case.  The tactic also looks for the solution on the assumption	 *)
(* list of the goal, with backchaining through implications. 		 *)
(* --------------------------------------------------------------------- *)
fun TRANS_TAC g =
   (REPEAT STRIP_TAC THEN
    FIRST [FIRST_ASSUM MATCH_ACCEPT_TAC,
           TPre_TAC,
           TSumL_TAC THEN TRANS_TAC,
           TSumR_TAC THEN TRANS_TAC,
           TProd_TAC  THEN TRANS_TAC,
   	   FIRST_ASSUM MATCH_MP_TAC THEN TRANS_TAC]) g
   handle _ => raise HOL_ERR{origin_function="TRANS_TAC",message="",
                             origin_structure=""};

(* ===================================================================== *)
(* Inductive definition of a trace transition system                	 *)
(* ===================================================================== *)

(* --------------------------------------------------------------------- *)
(* We now define a transition system that accumulates the trace of a	 *)
(* process.  This is essentially the reflexive-transitive closure of	 *)
(* TRANS, but with the label being a list of the labels from TRANS.	 *)
(* --------------------------------------------------------------------- *)

val {desc=Lrules,induction_thm=Lind} =
let val TRANSIT = TERM`TRANSIT: agent-> ^label list->agent->bool`
in
new_inductive_definition{name="TRANSIT_DEF",fixity=Prefix,
   patt=(`^TRANSIT X L Y`,[]),
   rules=[


      ([],                                                            [])
      -------------------------------------------------------------------
                            `^TRANSIT P [] P`                           ,


      ([`TRANS (P:agent) (a:^label) (Q:agent)`,    `^TRANSIT Q B P'`],[])
      -------------------------------------------------------------------
                      `^TRANSIT P (CONS a B) P'`                       ]}
end;

(* --------------------------------------------------------------------- *)
(* Strong form of rule induction for labelled (trace) transitions.       *)
(* --------------------------------------------------------------------- *)

val Lsind = derive_strong_induction (Lrules,Lind);

(* --------------------------------------------------------------------- *)
(* Rule induction tactic for TRANSIT.					 *)
(* --------------------------------------------------------------------- *)

val TRANSIT_INDUCT_TAC = RULE_INDUCT_THEN Lind ASSUME_TAC ASSUME_TAC;

(* --------------------------------------------------------------------- *)
(* Cases theorem for the trace transition system.		      	 *)
(* --------------------------------------------------------------------- *)

val Lcases = derive_cases_thm (Lrules,Lind);

(* --------------------------------------------------------------------- *)
(* A tactic for each TRANSIT rule. If matching conclusions to goals,     *)
(* the two rules are mutually exclusive---so only the following single	 *)
(* tactic is needed.							 *)
(* --------------------------------------------------------------------- *)

val TRANSIT_TAC = MAP_FIRST RULE_TAC Lrules;

(* ===================================================================== *)
(* Theorem 1: Maximal trace semantics "agrees' with transition semantics *)
(* ===================================================================== *)

(* --------------------------------------------------------------------- *)
(* Lemma 1 is to prove the following theorem:				 *)
(*									 *)
(*    |- !P a Q. TRANS P a Q ==> !A. MTRACE Q A ==> MTRACE P (CONS a A)  *)
(*									 *)
(* The proof is a straightforward rule induction on TRANS, followed by	 *)
(* a case analysis on MTRACE Q A when Q is a product (Prod), and then	 *)
(* completed by a simple search for the proof of the conclusion using 	 *)
(* the tactic MTRACE_TAC.						 *)
(* --------------------------------------------------------------------- *)

val Lemma1 = prove
(--`!P a Q. TRANS P a Q ==> !A. MTRACE Q A ==> MTRACE P (CONS a A)`--,  
     TRANS_INDUCT_TAC THEN REPEAT GEN_TAC THEN
     let val PCASES = PURE_ONCE_REWRITE_RULE [MTCASE (--`Prod P Q`--)] 
     in DISCH_THEN (STRIP_ASSUME_TAC o PCASES) THEN MTRACE_TAC
     end);

(* --------------------------------------------------------------------- *)
(* Theorem 1:  |- !P A Q. TRANSIT P A Q ==> TERMINAL Q ==> MTRACE P A    *)
(*									 *)
(* This theorem shows that the trace semantics agrees with the 		 *)
(* trace-transition semantics, in the sense that if we follow the	 *)
(* transitions of a process P until we reach a terminal process Q, that	 *)
(* is a process with an empty maximal trace, then we will have gone	 *)
(* through a maximal trace of P.					 *)
(* --------------------------------------------------------------------- *)

val Theorem1 =
    store_thm
    ("Theorem1",
     (--`!P A Q. TRANSIT P A Q ==> TERMINAL Q ==> MTRACE P A`--),
     PURE_ONCE_REWRITE_TAC [TERMINAL_DEF] THEN 
     TRANSIT_INDUCT_TAC THEN REPEAT STRIP_TAC THEN
     RES_TAC THEN IMP_RES_TAC Lemma1);

(* --------------------------------------------------------------------- *)
(* Corollary 1: !P A Q. TRANSIT P A Nil ==> MTRACE P A                   *)
(*									 *)
(* Note that the converse does not hold.				 *)
(* --------------------------------------------------------------------- *)

val Corollary1 = 
    store_thm
    ("Corollary1",
     (--`!P A. TRANSIT P A Nil ==> MTRACE P A`--),
     REPEAT STRIP_TAC THEN
     IMP_RES_THEN MATCH_MP_TAC Theorem1 THEN
     PURE_ONCE_REWRITE_TAC [TERMINAL_DEF] THEN
     MTRACE_TAC);

(* ===================================================================== *)
(* Theorem 2: Transition semantics "agrees' with maximal trace semantics *)
(* ===================================================================== *)

(* --------------------------------------------------------------------- *)
(* The following tactic is for solving existentially-quantified goals,	 *)
(* the bodies of which are conjunctions of assertions of membership in	 *)
(* one or more of the inductively-defined relations we're working with.  *)
(* All it does is to reduce the goal with the supplied witness, and then *)
(* apply the tactic for the relevant relation.				 *)
(* --------------------------------------------------------------------- *)

fun EXISTS_SEARCH_TAC tm =
     EXISTS_TAC tm THEN REPEAT STRIP_TAC THEN
       TRY(FIRST [TRANS_TAC, MTRACE_TAC, TRANSIT_TAC]);

(* --------------------------------------------------------------------- *)
(* A little tactic for case analysis on the trace-transition system. 	 *)
(* When supplied with a term (--`TRANSIT P A Q`--), which should be one  *)
(* of the assumptions of the current goal, the tactic gets the           *)
(* corresponding instance of the TRANSIT case analysis theorem,          *)
(* simplifies out any false case, and enriches the goal with the         *)
(* remaining facts, either by assuming them or, in the case of equations,*)
(* by substitution.		                                         *)
(* --------------------------------------------------------------------- *)

val TRANSIT_CASES_TAC = 
    let fun SUBST_ASSUME th g = SUBST_ALL_TAC th g 
                                handle _ => STRIP_ASSUME_TAC th g
        val TTAC = (REPEAT_TCL STRIP_THM_THEN SUBST_ASSUME) 
    in fn tm =>
      let val th1 = UNDISCH(fst(EQ_IMP_RULE(REWR_CONV Lcases tm)))
          val th2 = REWRITE_RULE [NOT_CONS_NIL,NOT_NIL_CONS,CONS_11] th1 
      in REPEAT_TCL STRIP_THM_THEN SUBST_ASSUME th2
      end
    end;

(* --------------------------------------------------------------------- *)
(* Lemma 2 shows that the trace of a product is just the trace of its	 *)
(* two components in the relation TRANSIT. The proof is a sraightfoward	 *)
(* structural induction on the list A, with simplification using the     *)
(* case analysis theorem for TRANSIT.					 *)
(* --------------------------------------------------------------------- *)

val Lemma2 = prove
(--`!A P Q P' Q'.
    TRANSIT P A Q /\ TRANSIT P' A Q' ==> TRANSIT (Prod P P') A (Prod Q Q')`--,
  INDUCT_THEN list_INDUCT ASSUME_TAC THEN
  PURE_ONCE_REWRITE_TAC [Lcases] THEN
  REWRITE_TAC ([NOT_NIL_CONS,NOT_CONS_NIL,CONS_11] @ agent11) THEN
  CONV_TAC (ONCE_DEPTH_CONV REDUCE) THEN
  REPEAT STRIP_TAC THEN EXISTS_SEARCH_TAC (--`Prod Q'' Q'''`--));

(* --------------------------------------------------------------------- *)
(* Theorem 2:  |- !P A. MTRACE P A ==> ?Q. TRANSIT P A Q /\ TERMINAL Q	 *)
(*									 *)
(* This theorem shows that the transition semantics "agrees' with the	 *)
(* trace semantics, in the sense that every maximal trace A leads in the *)
(* transition semantics to a terminal process.  The proof proceeds by	 *)
(* rule induction on MTRACE P A, followed by semi-automatic search for 	 *)
(* proofs of TRANSIT P A Q and TERMINAL Q.  The user supplies a witness  *)
(* for any existential goals that arise.  There is also a case analysis  *)
(* on the TRANSIT assumption in the Sum cases, there being different 	 *)
(* witnesses required for the two TRANSIT rules.			 *)
(* --------------------------------------------------------------------- *)

val Theorem2 = store_thm ("Theorem2",
(--`!P A. MTRACE P A ==> ?Q. TRANSIT P A Q /\ TERMINAL Q`--),
     PURE_ONCE_REWRITE_TAC [TERMINAL_DEF] THEN
     MTRACE_INDUCT_TAC THEN REPEAT GEN_TAC THENL
     [EXISTS_SEARCH_TAC (--`Nil`--),
      MAP_EVERY EXISTS_SEARCH_TAC [(--`Q:agent`--),(--`P:agent`--)],
      TRANSIT_CASES_TAC (--`TRANSIT P A Q`--) THENL
      [EXISTS_SEARCH_TAC (--`Sum P Q'`--),
       MAP_EVERY EXISTS_SEARCH_TAC [(--`Q:agent`--), (--`Q'':agent`--)]],
      TRANSIT_CASES_TAC (--`TRANSIT Q A Q'`--) THENL
      [EXISTS_SEARCH_TAC (--`Sum P Q`--),
       MAP_EVERY EXISTS_SEARCH_TAC [(--`Q':agent`--), (--`Q'':agent`--)]], 
      IMP_RES_TAC Lemma2 THEN EXISTS_SEARCH_TAC (--`Prod Q' Q''`--)]);

(* ===================================================================== *)
(* Theorem3: The transition and maximal trace semantics "agree'.	 *)
(* ===================================================================== *)

val Theorem3 =
    store_thm
    ("Theorem3",
     (--`!P A. MTRACE P A = (?Q. TRANSIT P A Q /\ TERMINAL Q)`--),
     REPEAT (EQ_TAC ORELSE STRIP_TAC) THENL
     [MATCH_MP_TAC Theorem2 THEN FIRST_ASSUM ACCEPT_TAC,
      IMP_RES_TAC Theorem1]);


(* ===================================================================== *)
(* Definitions of notions of equivalence                                 *)
(* ===================================================================== *)

(* --------------------------------------------------------------------- *)
(* Maximal trace equivalence. Two processes are maximal trace equivalent *)
(* if they have the same maximal traces.				 *)
(* --------------------------------------------------------------------- *)

val MEQUIV_DEF =
    new_infix_definition 
    ("MEQUIV_DEF",    
     (--`MEQUIV P Q = (!A. MTRACE P A = MTRACE Q A)`--),700);

(* --------------------------------------------------------------------- *)
(* Bisimulation equivalence.  A binary relation s:agent->agent->bool is  *)
(* a simulation if s P Q implies that any transitions that P can do can  *)
(* also be done by Q such that the corresponding successive pairs of	 *)
(* agents remain in the relation s.  Equivalence is then defined to be 	 *)
(* the bisimulation (simulation whose inverse is also a simulation).	 *)
(* --------------------------------------------------------------------- *)

val SIM_DEF =
    new_definition 
    ("SIM_DEF",
     (--`SIM s = 
      !P Q. s P Q ==>
            !a P'. TRANS P a P' ==> ?Q'. TRANS Q a Q' /\ s P' Q'`--));

val BEQUIV_DEF =
    new_infix_definition 
    ("BEQUIV_DEF",
     (--`BEQUIV P Q = ?s. SIM s /\ s P Q /\ SIM(\x y. s y x)`--),700);


(* --------------------------------------------------------------------- *)
(* End of example.							 *)
(* --------------------------------------------------------------------- *)

html_theory"-";
export_theory();
