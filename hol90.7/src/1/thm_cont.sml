(* ===================================================================== *)
(* FILE          : thm_cont.sml                                          *)
(* DESCRIPTION   : Larry Paulson's theorem continuations for HOL.        *)
(*                 Translated from hol88.                                *)
(*                                                                       *)
(* "Theorem continuations"                                               *)
(*                                                                       *)
(* Many inference rules, particularly those involving disjunction and    *)
(* existential quantifiers, produce intermediate results that are needed *)
(* only briefly.  One approach is to treat the assumption list like a    *)
(* stack, pushing and popping theorems from it.  However, it is          *)
(* traditional to regard the assumptions as unordered;  also, stack      *)
(* operations are crude.                                                 *)
(*                                                                       *)
(* Instead, we adopt a continuation approach:  a continuation is a       *)
(* function that maps theorems to tactics.  It can put the theorem on    *)
(* the assumption list, produce a case split, throw it away, etc.  The	 *)
(* text of a large theorem continuation should be a readable description *)
(* of the flow of inference.						 *)
(*                                                                       *)
(* AUTHORS       : (c) Larry Paulson and others,                         *)
(*                     University of Cambridge, for hol88                *)
(* TRANSLATOR    : Konrad Slind, University of Calgary                   *)
(* DATE          : September 11, 1991                                    *)
(* ===================================================================== *)


structure Thm_cont : Thm_cont_sig =
struct
open Base_logic;

fun THM_CONT_ERR{function,message} = HOL_ERR{origin_structure = "Thm_cont",
					     origin_function = function,
					     message = message}

infix THEN_TCL ORELSE_TCL;

fun (ttcl1:thm_tactical) THEN_TCL (ttcl2:thm_tactical) =  fn ttac =>  
     ttcl1 (ttcl2 ttac);

fun (ttcl1:thm_tactical) ORELSE_TCL (ttcl2:thm_tactical) = fn ttac => fn th =>
    (ttcl1 ttac th)  handle _ => (ttcl2 ttac th);

fun REPEAT_TCL ttcl ttac th =
    ((ttcl  THEN_TCL  (REPEAT_TCL ttcl))  ORELSE_TCL  I) ttac th;

(* --------------------------------------------------------------------- *)
(* New version of REPEAT for ttcl's.  Designed for use with IMP_RES_THEN.*)
(* TFM 91.01.20.                                                         *)
(* --------------------------------------------------------------------- *)
fun REPEAT_GTCL (ttcl: thm_tactical) ttac th (A,g) =  
    ttcl (REPEAT_GTCL ttcl ttac) th (A,g) 
    handle _ => ttac th (A,g);

val ALL_THEN :thm_tactical = I;
val NO_THEN :thm_tactical = 
   fn ttac => fn th => raise THM_CONT_ERR{function = "NO_THEN",message = ""};

(* Uses every theorem tactical.

   EVERY_TCL [ttcl1;...;ttcln] =  ttcl1  THEN_TCL  ...  THEN_TCL  ttcln
*)
fun EVERY_TCL ttcll = itlist (curry (op THEN_TCL)) ttcll ALL_THEN;

(* Uses first successful theorem tactical.
   FIRST_TCL [ttcl1;...;ttcln] =  ttcl1  ORELSE_TCL  ...  ORELSE_TCL  ttcln
*)
fun FIRST_TCL ttcll = itlist (curry (op ORELSE_TCL)) ttcll NO_THEN;

(*
Conjunction elimination

	C
   ==============       |- A1 /\ A2
	C
      ===== ttac1 |-A1
       ...
      ===== ttac2 |-A2
       ...
*)
fun CONJUNCTS_THEN2 (ttac1:thm_tactic) (ttac2:thm_tactic) :thm_tactic = 
   fn cth => let val (th1,th2) = Drule.CONJ_PAIR cth
             in
             Tactical.THEN (ttac1 th1, ttac2 th2)
             end
             handle _ => raise THM_CONT_ERR{function = "CONJUNCTS_THEN2",
					    message = ""};



val CONJUNCTS_THEN :thm_tactical = fn ttac => CONJUNCTS_THEN2 ttac ttac;;

(*
Disjunction elimination

	         C
   =============================       |- A1 \/ A2
      C                     C
    ===== ttac1 A1|-A1    ===== ttac2 A2|-A2
     ...		   ...
*)
(* -------------------------------------------------------------------------*)
(* REVISED 22 Oct 1992 by TFM. Bugfix.					    *)
(*									    *)
(* The problem was, for example:					    *)
(*									    *)
(*  th = |- ?n. ((?n. n = SUC 0) \/ F) /\ (n = 0)			    *)
(*  set_goal ([], "F");;						    *)
(*  expandf (STRIP_ASSUME_TAC th);;				 	    *)
(*  OK..								    *)
(*  "F"									    *)
(*     [ "n = SUC 0" ] (n.b. should be n')				    *)
(*     [ "n = 0" ]						            *)
(* 								            *)
(* let DISJ_CASES_THEN2 ttac1 ttac2 disth :tactic  =			    *)
(*     let a1,a2 = dest_disj (concl disth) ? failwith `DISJ_CASES_THEN2` in *)
(*     \(asl,w).							    *)
(*      let gl1,prf1 = ttac1 (ASSUME a1) (asl,w)			    *)
(*      and gl2,prf2 = ttac2 (ASSUME a2) (asl,w)			    *)
(*      in							            *)
(*      gl1 @ gl2,							    *)
(*      \thl. let thl1,thl2 = chop_list (length gl1) thl in		    *)
(*            DISJ_CASES disth (prf1 thl1) (prf2 thl2);;		    *)
(* -------------------------------------------------------------------------*)
fun DISJ_CASES_THEN2 (ttac1:thm_tactic) (ttac2:thm_tactic):thm_tactic = 
 fn disth:(Thm.thm) =>
   let val {disj1,disj2} = Dsyntax.dest_disj (Thm.concl disth)
   in
   fn (asl,w) =>
      let val (gl1,prf1) = ttac1 (itlist Drule.ADD_ASSUM (Thm.hyp disth) 
                                         (Thm.ASSUME disj1))
                                 (asl,w)
          and (gl2,prf2) = ttac2 (itlist Drule.ADD_ASSUM (Thm.hyp disth)
                                         (Thm.ASSUME disj2))
                                 (asl,w)
      in
      ((gl1@gl2), 
       (fn thl => let val (thl1,thl2) = split_after (length gl1) thl 
                  in
                  Drule.DISJ_CASES disth (prf1 thl1) (prf2 thl2)
                  end))
      end 
   end
   handle _ => raise THM_CONT_ERR{function = "DISJ_CASES_THEN2",message = ""};


(*Single-, multi-tactic versions*)
val DISJ_CASES_THEN :thm_tactical = fn ttac => DISJ_CASES_THEN2 ttac ttac;
val DISJ_CASES_THENL  = end_itlist DISJ_CASES_THEN2;;

(* Implication introduction

	A ==> B
    ==============
	  B
    ==============  ttac |-A
	. . .
*)

(* DISCH changed to NEG_DISCH for HOL *)

(* Deleted: TFM 88.03.31						*)
(*									*)
(* let DISCH_THEN ttac :tactic (asl,w) =				*)
(*     let ante,conc = dest_imp w ? failwith `DISCH_THEN` in		*)
(*     let gl,prf = ttac (ASSUME ante) (asl,conc) in			*)
(*     gl, (NEG_DISCH ante) o prf;;					*)
(* Added: TFM 88.03.31  (bug fix)					*)

fun DISCH_THEN (ttac:thm_tactic) :tactic = fn (asl,w) =>
   let val {ant,conseq} = Dsyntax.dest_imp w 
       val (gl,prf) = ttac (Thm.ASSUME ant) (asl,conseq) 
   in
   (gl, (if (Dsyntax.is_neg w) 
         then Drule.NEG_DISCH ant 
         else Thm.DISCH ant) o prf)
   end
   handle _ => raise THM_CONT_ERR{function = "DISCH_THEN",message = ""};


(* Existential elimination

	    B
    ==================   |- ?x. A(x)
            B
    ==================    ttac A(y)
	   ...
explicit version for tactic programming
*)
fun X_CHOOSE_THEN y (ttac:thm_tactic) : thm_tactic = fn xth =>
   let val {Bvar,Body} = Dsyntax.dest_exists (Thm.concl xth)
   in
   fn (asl,w) =>
      let val th = itlist Drule.ADD_ASSUM (Thm.hyp xth)
                          (Thm.ASSUME (Term.subst[{redex=Bvar,residue=y}]Body))
          val (gl,prf) = ttac th (asl,w) 
      in
      (gl, (Drule.CHOOSE (y,xth)) o prf)
      end
   end
   handle _ => raise THM_CONT_ERR{function = "X_CHOOSE_THEN",message = ""};


(*chooses a variant for the user*)
val CHOOSE_THEN :thm_tactical = fn ttac => fn xth =>
   let val (hyp,conc) = Thm.dest_thm xth
       val {Bvar,...} = Dsyntax.dest_exists conc
   in
   fn (asl,w) =>
     let val y = Term.variant (Term.free_varsl ((conc::hyp)@(w::asl))) Bvar
     in
     X_CHOOSE_THEN y ttac xth (asl,w)
     end
   end
   handle _ => raise THM_CONT_ERR{function = "CHOOSE_THEN",message = ""};


(*Cases tactics*)

(*for a generalized disjunction  |-(?xl1.B1(xl1))  \/...\/  (?xln.Bn(xln))
where the xl1...xln are vectors of zero or more variables,
and the variables in each of yl1...yln have the same types as the 
corresponding xli do

                           A
    =============================================
       A                                     A
    ======= ttac1 |-B1(yl1)     ...       ======= ttacn |-Bn(yln)
      ...                                   ...
*)
fun X_CASES_THENL varsl (ttacl:thm_tactic list) =
    DISJ_CASES_THENL 
       (map (fn (vars,ttac) => EVERY_TCL (map X_CHOOSE_THEN vars) ttac)
            (varsl zip ttacl));


fun X_CASES_THEN varsl ttac =
    DISJ_CASES_THENL 
       (map (fn vars => EVERY_TCL (map X_CHOOSE_THEN vars) ttac) varsl);


(*Version that chooses the y's as variants of the x's*)

fun CASES_THENL ttacl = DISJ_CASES_THENL (map (REPEAT_TCL CHOOSE_THEN) ttacl);


(*Tactical to strip off ONE disjunction, conjunction, or existential*)

val STRIP_THM_THEN = FIRST_TCL [CONJUNCTS_THEN, DISJ_CASES_THEN, CHOOSE_THEN];

end; (* THM_CONT *)
