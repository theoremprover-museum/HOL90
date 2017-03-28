(* ===================================================================== *)
(* FILE          : tactic.sml                                            *)
(* DESCRIPTION   : Tactics are from LCF. They are a fundamental proof    *)
(*                 method due to Robin Milner. Translated from hol88.    *)
(*                                                                       *)
(* AUTHORS       : (c) University of Edinburgh and                       *)
(*                     University of Cambridge, for hol88                *)
(* TRANSLATOR    : Konrad Slind, University of Calgary                   *)
(* DATE          : September 11, 1991                                    *)
(* ===================================================================== *)


structure Tactic : Tactic_sig =
struct
open Base_logic;
open Term_io.Parse;
open Tactical;
  infix THEN;
  infix THENL;
  infix ORELSE;

fun TACTIC_ERR{function,message} = HOL_ERR{origin_structure = "Tactic",
					   origin_function = function,
					   message = message}


(* Accepts a theorem that satisfies the goal

	A
    =========	ACCEPT_TAC "|-A"
	-
*)
val ACCEPT_TAC :thm_tactic = fn th => fn (asl,w) =>
   if (Term.aconv (Thm.concl th) w)
   then ([], fn [] => th)
   else raise TACTIC_ERR{function = "ACCEPT_TAC",message = ""};


(* --------------------------------------------------------------------- *)
(* DISCARD_TAC: checks that a theorem is useless, then ignores it.	*)
(* Revised: 90.06.15 TFM.						*)
(* --------------------------------------------------------------------- *)
local
val truth = --`T`--
in
fun DISCARD_TAC th (asl,w) =
   if (exists (Term.aconv (Thm.concl th)) (truth::asl))
   then Tactical.ALL_TAC (asl,w)
   else raise TACTIC_ERR{function = "DISCARD_TAC",message = ""}
end;


(* Contradiction rule
 *
 *	 A
 *    ===========  CONTR_TAC "|- FALSITY"
 *       -
 ******)
val CONTR_TAC :thm_tactic = fn cth => fn (asl,w) => 
   let val th = Drule.CONTR w cth
   in
   ([], fn [] => th)
   end
   handle _ => raise TACTIC_ERR{function = "CONTR_TAC",message = ""};


(* Classical contradiction rule
 *
 *	 A
 *    ===========  CCONTR_TAC 
 *       -
 ******)
local 
val F = --`F`--
in
fun CCONTR_TAC (asl, w) =
  ([(Dsyntax.mk_neg w::asl, F)], fn [th] => Drule.CCONTR w th)
end;

(* Put a theorem onto the assumption list.
 *    Note:  since an assumption B denotes a theorem B|-B, 
 *           you cannot instantiate types or variables in assumptions.
 * 
 *         A
 *    ===========  |- B
 *      [B] A
 *******)
val ASSUME_TAC :thm_tactic = fn bth => fn (asl,w) =>
   ([(((Thm.concl bth)::asl),w)],
    (fn [th] => Drule.PROVE_HYP bth th));


(*"Freeze" a theorem to prevent instantiation 
 * 
 *         A
 *    ===========	ttac "B|-B"
 *        ...
 *******)
val FREEZE_THEN :thm_tactical = fn (ttac:thm_tactic) => fn bth => fn g => 
   let val (gl,prf) = ttac (Thm.ASSUME (Thm.concl bth)) g 
   in
   (gl, (Drule.PROVE_HYP bth o prf))
   end;


(* Conjunction introduction
 * 
 *         A /\ B
 *     ===============
 *       A        B
 ********)
val CONJ_TAC:tactic = fn (asl,w) =>
   let val {conj1,conj2} = Dsyntax.dest_conj w 
   in
   ([(asl,conj1), (asl,conj2)], fn [th1,th2] => Drule.CONJ th1 th2)
   end
   handle _ => raise TACTIC_ERR{function = "CONJ_TAC",message = ""};




(* Disjunction introduction

	A \/ B
    ==============
	  A
*)
val DISJ1_TAC:tactic = fn (asl,w) =>
   (let val {disj1,disj2} = Dsyntax.dest_disj w 
    in
    ([(asl,disj1)], fn [tha] => Drule.DISJ1 tha disj2)
    end
   )
   handle _ => raise TACTIC_ERR{function = "DISJ1_TAC",message = ""};



(*	A \/ B
    ==============
	  B
*)
val DISJ2_TAC:tactic = fn (asl,w) =>
   let val {disj1,disj2} = Dsyntax.dest_disj w
   in
   ([(asl,disj2)], fn [thb] => Drule.DISJ2 disj1 thb)
   end
   handle _ => raise TACTIC_ERR{function = "DISJ2_TAC",message = ""};



(*Implication elimination

	         A
    |- B  ================ 
               B ==> A   
*)
val MP_TAC :thm_tactic = fn thb => fn (asl,wa) =>
   ([(asl, Dsyntax.mk_imp{ant = Thm.concl thb, conseq = wa})],
    fn [thimp] => Thm.MP thimp thb);


val EQ_TAC:tactic = fn (asl,t) =>
   let val {lhs,rhs} = Dsyntax.dest_eq t
   in
   ([(asl, Dsyntax.mk_imp{ant = lhs, conseq = rhs}),
     (asl, Dsyntax.mk_imp{ant = rhs, conseq = lhs})],
    fn [th1,th2] => Drule.IMP_ANTISYM_RULE th1 th2)
   end
   handle _ => raise TACTIC_ERR{function = "EQ_TAC",message = ""};

(* Universal quantifier							*)

(*	!x.A(x)
    ==============
	 A(x')

 explicit version for tactic programming;  proof fails if x' is free in hyps

*)

(* fun X_GEN_TAC x' :tactic (asl,w) =			*)
(*   (let val x,body = dest_forall w in			*)
(*    [ (asl, subst[x',x]body) ], (\[th]. GEN x' th) 	*)
(*   ) ? failwith X_GEN_TAC;;				*)

(* T. Melham. X_GEN_TAC rewritten 88.09.17				*)
(*									*)
(* 1)  X_GEN_TAC x'    now fails if x' is not a variable.		*)
(*									*)
(* 2) rewritten so that the proof yields the same quantified var as the *)
(*    goal.								*)
(*									*)
(*  fun X_GEN_TAC x' :tactic =						*)
(*   if not(is_var x') then failwith X_GEN_TAC else			*)
(*   \(asl,w).((let val x,body = dest_forall w in			*)
(*               [(asl,subst[x',x]body)],				*)
(*                (\[th]. GEN x (INST [(x,x')] th)))			*)
(*              ? failwith X_GEN_TAC);;				        *)
(* Bugfix for HOL88.1.05, MJCG, 4 April 1989				*)
(* Instantiation before GEN replaced by alpha-conversion after it to 	*)
(* prevent spurious failures due to bound variable problems when 	*)
(* quantified variable is free in assumptions.				*)
(* Optimization for the x=x' case added.                                *)
fun X_GEN_TAC x1 : tactic = fn (asl,w) =>
   if (not(Term.is_var x1))
   then raise TACTIC_ERR{function = "X_GEN_TAC",message = "need a var."}
   else let val {Bvar,Body} = Dsyntax.dest_forall w 
        in
        if (Bvar=x1)
        then ([(asl,Body)], fn [th] => Drule.GEN x1 th)
        else ([(asl,Term.subst [{redex = Bvar, residue = x1}] Body)],
             fn [th] => let val th' = Drule.GEN x1 th
                        in
                        Drule.EQ_MP(Drule.GEN_ALPHA_CONV Bvar (Thm.concl th')) 
                                                         th'
                        end)
        end
    handle _ => raise TACTIC_ERR{function = "X_GEN_TAC",message = ""};


(* chooses a variant for the user;  for interactive proof		*)
val GEN_TAC:tactic = fn (asl,w) =>
    let val {Bvar,...} = Dsyntax.dest_forall w
                         handle _ => raise TACTIC_ERR{function = "GEN_TAC",
                                                      message = "not a forall"}
    in X_GEN_TAC (Term.variant (Term.free_varsl (w::asl)) Bvar) (asl,w)
    end;


(* Specialization
	A(t)
    ============  t,x
       !x.A(x)

example of use:  generalizing a goal before attempting an inductive proof
as with Boyer and Moore.
*)
fun SPEC_TAC (t,x) :tactic = fn (asl,w) =>
    ([(asl, Dsyntax.mk_forall{Bvar = x, 
                              Body = Term.subst[{redex = t,residue = x}] w})],
     fn [th] => Drule.SPEC t th)
    handle _ => raise TACTIC_ERR{function = "SPEC_TAC",message = ""};


(* Existential introduction

	?x.A(x)
    ==============   t
	 A(t)
*)
fun EXISTS_TAC t :tactic = fn (asl,w) =>
   (let val {Bvar,Body} = Dsyntax.dest_exists w 
    in
    ([(asl, Term.subst [{redex = Bvar, residue = t}] Body)],
     fn [th] => Drule.EXISTS (w,t) th)
    end)
    handle _ => raise TACTIC_ERR{function = "EXISTS_TAC",message = ""};


(* Substitution
   These substitute in the goal;  thus they DO NOT invert the rules SUBS and
   SUBS_OCCS, despite superficial similarities.  In fact, SUBS and SUBS_OCCS
   are not invertible;  only SUBST is.
*)
fun GSUBST_TAC substfn ths :tactic = 
   fn (asl,w) =>
      let val (theta1,theta2,theta3) =
             itlist (fn th => fn (theta1,theta2,theta3) =>
                       let val {lhs,rhs} = Dsyntax.dest_eq(Thm.concl th)
                           val v = Term.genvar (Term.type_of lhs)
                       in
                       ({redex = lhs, residue = v}::theta1,
                        {redex = v, residue = rhs}::theta2,
                        {var = v, thm = Drule.SYM th}::theta3)
                       end)
                    ths ([],[],[])
          val base = substfn theta1 w
      in
      ([(asl, Term.subst theta2 base)], fn [th] => Thm.SUBST theta3 base th)
      end
      handle _ => raise TACTIC_ERR{function = "GSUBST_TAC",message = ""};

(*	A(ti)
    ==============   |- ti == ui
	A(ui)
*)

fun SUBST_TAC ths = GSUBST_TAC Term.subst ths 
                    handle _ => raise TACTIC_ERR{function = "SUBST_TAC",
						 message = ""};

fun SUBST_OCCS_TAC nlths = 
   let val (nll, ths) = unzip nlths 
   in  
   GSUBST_TAC (Dsyntax.subst_occs nll) ths
   end
   handle _ => raise TACTIC_ERR{function = "SUBST_OCCS_TAC",message = ""};


(*	 A(t)
    ===============   |- t==u
	 A(u)

works nicely with tacticals 

*)

fun SUBST1_TAC rthm = SUBST_TAC [rthm];


(* Map an inference rule over the assumptions, replacing them. *)
fun cons a L = a::L

fun RULE_ASSUM_TAC rule :tactic =
   Tactical.POP_ASSUM_LIST
   (fn asl => Tactical.MAP_EVERY ASSUME_TAC (rev_itlist (cons o rule) asl []));

(*Substitute throughout the goal and its assumptions*)

fun SUBST_ALL_TAC rth = SUBST1_TAC rth THEN
                        RULE_ASSUM_TAC (Drule.SUBS [rth]);

val CHECK_ASSUME_TAC :thm_tactic = fn gth =>
    FIRST [CONTR_TAC gth,  ACCEPT_TAC gth, DISCARD_TAC gth, ASSUME_TAC gth];


val STRIP_ASSUME_TAC = (Thm_cont.REPEAT_TCL Thm_cont.STRIP_THM_THEN) 
                       CHECK_ASSUME_TAC;

(*
 * given a theorem:
 * 
 * |- (?y1. (x=t1(y1)) /\ B1(x,y1))  \/ ... \/  (?yn. (x=tn(yn)) /\ Bn(x,yn))
 * 
 * where each y is a vector of zero or more variables
 * and each Bi is a conjunction (Ci1 /\ ... /\ Cin)
 * 
 * 		        A(x)
 *     ===============================================
 *     [Ci1(tm,y1')] A(t1)  . . .  [Cin(tm,yn')] A(tn)
 * 
 * such definitions specify a structure as having n different possible
 * constructions (the ti) from subcomponents (the yi) that satisfy various 
 * constraints (the Cij).
 *************************)

val STRUCT_CASES_TAC = 
 Thm_cont.REPEAT_TCL Thm_cont.STRIP_THM_THEN
                     (fn th => Tactical. ORELSE(SUBST1_TAC th, ASSUME_TAC th));

(* -------------------------------------------------------------------- *)
(* COND_CASES_TAC: tactic for doing a case split on the condition p	*)
(*                 in a conditional (p => u | v).			*)
(*									*)
(* Find a conditional "p => u | v" that is free in the goal and whose 	*)
(* condition p is not a constant. Perform a case split on the condition.*)
(*                                                                      *)
(*									*)
(*	t[p=>u|v]							*)
(*    =================	 COND_CASES_TAC					*)
(*       {p}  t[u]							*)
(*       {~p}  t[v]							*)
(*									*)
(* 						[Revised: TFM 90.05.11] *)
(* -------------------------------------------------------------------- *)

local
fun is_good_cond tm = not(Term.is_const(#cond(Dsyntax.dest_cond tm))) 
                      handle _ => false
val alpha =  ==`:'a`==
fun alpha_subst ty = [{redex = alpha, residue = ty}]
in
val COND_CASES_TAC :tactic = fn (asl,w) =>
   let val cond = Dsyntax.find_term (fn tm => is_good_cond tm
                                              andalso 
                                              Term.free_in tm w) 
                                    w
                  handle _ => raise TACTIC_ERR{function = "COND_CASES_TAC",
					       message = ""}
       val {cond,larm,rarm} = Dsyntax.dest_cond cond
       val inst = Thm.INST_TYPE (alpha_subst (Term.type_of larm)) 
                                Drule.COND_CLAUSES
       val (ct,cf) = Drule.CONJ_PAIR (Drule.SPEC rarm (Drule.SPEC larm inst))
   in
   Thm_cont.DISJ_CASES_THEN2
     (fn th =>  SUBST1_TAC (Drule.EQT_INTRO th) THEN 
                SUBST1_TAC ct THEN ASSUME_TAC th)
     (fn th => SUBST1_TAC (Drule.EQF_INTRO th) THEN 
               SUBST1_TAC cf THEN ASSUME_TAC th)
     (Drule.SPEC cond Drule.EXCLUDED_MIDDLE)
     (asl,w)
   end
end;

(*Cases on  |- p=T  \/  p=F *)
fun BOOL_CASES_TAC p = STRUCT_CASES_TAC (Drule.SPEC p Bool.BOOL_CASES_AX);

(*Strip one outer !, /\, ==> from the goal*)
fun STRIP_GOAL_THEN ttac =  Tactical.FIRST [GEN_TAC,
                                            CONJ_TAC,
                                            Thm_cont.DISCH_THEN ttac];

(* Like GEN_TAC but fails if the term equals the quantified variable *)
fun FILTER_GEN_TAC tm : tactic = fn (asl,w) =>
    if (Dsyntax.is_forall w andalso not (tm = (#Bvar(Dsyntax.dest_forall w))))
    then GEN_TAC (asl,w)
    else  raise TACTIC_ERR{function = "FILTER_GEN_TAC",message = ""};


(*Like DISCH_THEN but fails if the antecedent mentions the term*)
fun FILTER_DISCH_THEN (ttac:thm_tactic) tm : tactic  = fn (asl,w) =>
    if (Dsyntax.is_imp w
        andalso 
        not(mem tm (Term.free_vars (#ant(Dsyntax.dest_imp w)))))
    then Thm_cont.DISCH_THEN ttac (asl,w)
    else raise TACTIC_ERR{function = "FILTER_DISCH_THEN",message = ""};

(*Like STRIP_THEN but preserves any part of the goal that mentions the term*)

fun FILTER_STRIP_THEN ttac tm =
    FIRST [ FILTER_GEN_TAC tm,	FILTER_DISCH_THEN ttac tm, CONJ_TAC];

fun DISCH_TAC g = Thm_cont.DISCH_THEN ASSUME_TAC g 
                  handle _ => raise TACTIC_ERR{function = "DISCH_TAC",
					       message = ""};
val DISJ_CASES_TAC = Thm_cont.DISJ_CASES_THEN ASSUME_TAC;
val CHOOSE_TAC = Thm_cont.CHOOSE_THEN ASSUME_TAC;
fun X_CHOOSE_TAC x = Thm_cont.X_CHOOSE_THEN  x  ASSUME_TAC;
fun STRIP_TAC g = STRIP_GOAL_THEN STRIP_ASSUME_TAC g 
                  handle _ => raise TACTIC_ERR{function = "DISCH_TAC",
					       message = ""};
val FILTER_DISCH_TAC = FILTER_DISCH_THEN STRIP_ASSUME_TAC;
val FILTER_STRIP_TAC = FILTER_STRIP_THEN STRIP_ASSUME_TAC;

(* Cases on  |- t \/ ~t *)

fun ASM_CASES_TAC t = DISJ_CASES_TAC(Drule.SPEC t Drule.EXCLUDED_MIDDLE);


(* --------------------------------------------------------------------- *)
(* A tactic inverting REFL (from tfm).	 				*)
(*									*)
(*     A = A								*)
(* ==============							*)
(*									*)
(* Revised to work if lhs is alpha-equivalent to rhs      [TFM 91.02.02]*)
(* Also revised to retain assumptions.					*)
(* --------------------------------------------------------------------- *)

val REFL_TAC:tactic = fn (asl,g) =>
   let val {lhs,rhs} = Dsyntax.dest_eq g 
                       handle _ => raise TACTIC_ERR{function = "REFL_TAC",
                                                   message = "not an equation"}
       val asms = itlist Drule.ADD_ASSUM asl 
   in 
   if (lhs = rhs) 
   then ([], K (asms (Thm.REFL lhs)))
   else if (Term.aconv lhs rhs) 
        then ([], K (asms (Drule.ALPHA lhs rhs)))
        else raise TACTIC_ERR{function = "REFL_TAC",
			      message = "lhs and rhs not alpha-equivalent"}
   end;

(* UNDISCH_TAC -
   moves one of the assumptions as LHS of an implication
   to the goal (fails if named assumption not in assumptions)

UNDISCH_TAC: term -> tactic
              tm

         [ t1;t2;...;tm;tn;...tz ]  t
   ======================================
        [ t1;t2;...;tn;...tz ]  tm ==> t
*)

fun UNDISCH_TAC wf :tactic = fn (asl,w) =>
 if (mem wf asl) 
 then ([(set_diff asl [wf], Dsyntax.mk_imp {ant = wf,conseq = w})], 
       Drule.UNDISCH o hd)
 else raise TACTIC_ERR{function = "UNDISCH_TAC",message = ""};

(* ---------------------------------------------------------------------*)
(* AP_TERM_TAC: Strips a function application off the lhs and rhs of an	*)
(* equation.  If the function is not one-to-one, does not preserve 	*)
(* equivalence of the goal and subgoal.					*)
(*									*)
(*   f x = f y								*)
(* =============							*)
(*     x = y								*)
(*									*)
(* Added: TFM 88.03.31							*)
(* Revised: TFM 91.02.02						*)
(* --------------------------------------------------------------------- *)

val AP_TERM_TAC:tactic = fn (asl,gl) =>
   let val {lhs,rhs} = Dsyntax.dest_eq gl 
                       handle _ => raise TACTIC_ERR{function = "AP_TERM_TAC",
                                                   message = "not an equation"}
       val {Rator = g, Rand = x} = Term.dest_comb lhs 
                        handle _ => raise TACTIC_ERR {function = "AP_TERM_TAC",
                                            message = "lhs not an application"}
       val {Rator = f, Rand = y} = Term.dest_comb rhs
                         handle _ => raise TACTIC_ERR{function = "AP_TERM_TAC",
                                            message = "rhs not an application"}
   in if (not(f = g))
      then raise TACTIC_ERR{function = "AP_TERM_TAC",
                            message = "functions on lhs and rhs differ"} 
      else ([(asl, Dsyntax.mk_eq{lhs = x, rhs = y})], (Drule.AP_TERM f o hd))
   end;


(* --------------------------------------------------------------------- *)
(* AP_THM_TAC: inverts the AP_THM inference rule.			*)
(*									*)
(*   f x = g x								*)
(* =============							*)
(*     f = g								*)
(*									*)
(* Added: TFM 91.02.02							*)
(* --------------------------------------------------------------------- *)

val AP_THM_TAC:tactic = fn (asl,gl) =>
   let val {lhs,rhs} = Dsyntax.dest_eq gl 
                       handle _ => raise TACTIC_ERR{function = "AP_THM_TAC",
                                                   message = "not an equation"}
       val {Rator = g, Rand = x} = Term.dest_comb lhs
                         handle _ => raise TACTIC_ERR {function = "AP_THM_TAC",
                                            message = "lhs not an application"}
       val {Rator = f, Rand = y} = Term.dest_comb rhs
                         handle _ => raise TACTIC_ERR {function = "AP_THM_TAC",
                                            message = "rhs not an application"}
   in if not(x = y)
      then raise TACTIC_ERR{function = "AP_THM_TAC",
                            message = "arguments on lhs and rhs differ"} 
      else ([(asl, Dsyntax.mk_eq{lhs = g, rhs = f})], (C Drule.AP_THM x o hd))
   end;


end; (* Tactic *)
