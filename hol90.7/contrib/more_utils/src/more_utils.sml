(************************ more_utils.sml ********************************)
(*                                                                      *)
(* Author: Ralf Reetz                                                   *)
(* Date:   5.10.1994                                                    *)
(*                                                                      *)
(* Description:                                         	        *)
(*                                                                      *)
(*   see more_utils.sig                                                 *)
(*                                                                      *)
(* Used files:     more_utils.sig                                       *)
(* Used modules:                                                        *)
(* Used theories:                                                       *)
(* Used libraries: Integer                                              *)
(*                                                                      *)
(************************************************************************)

structure more_utils : MORE_UTILS =
struct
open Rsyntax; (* use records *)
(*-------------------------------------------------------------------------*)

(*
  Global Input:
   Integer.makestring
  Input:
   a number na and a list of assumptions
  Output:
   error message for tactics handling the n-th assumption
*)
fun No_message n asm =
 if (length asm) = 0 then 
  "The assumption list is empty.\n"
 else
  "There is no "^(Integer.makestring n)^"th assumption\n";

(*--- UNDISCH ---*)

(*
  Global Input:
   No_message
  Input:
   a number n and a goal (asm,g)
  Output:
   see more_utils.sig
  Algorithm:
   first check, whether the number really chooses an assumption. Then
   take the n-th assumption and use UNDISCH_TAC
*)
fun No_UNDISCH_TAC n ((asm,g):goal) = 
 if (0 < n) andalso (n <= (length asm)) then
  UNDISCH_TAC (el n asm) ((asm,g):goal)
 else
  raise HOL_ERR
  {message          = (No_message n asm),
   origin_function  = "No_UNDISCH_TAC",
   origin_structure = "more_utils"};

fun ALL_UNDISCH_TAC ((asm,g):goal) =
 let
  val ALL_UNDISCH_TAC1 =
   EVERY [
    REPEAT (POP_ASSUM (fn th1 => 
      POP_ASSUM (fn th2 => ASSUME_TAC (CONJ th1 th2)))),
    POP_ASSUM (fn th => ASSUME_TAC th THEN UNDISCH_TAC (concl th))
   ]
 in
  if asm=[] then
    ALL_TAC (asm,g)
  else 
   ALL_UNDISCH_TAC1 (asm,g)
 end;

(*--- DISCARD ---*)

fun No_DISCARD_ASSUM_TAC n ((asm,g):goal) =
 let
  fun No_DISCARD_ASSUM_TAC1 k [] = 
   ALL_TAC
  | No_DISCARD_ASSUM_TAC1 k (th::th_list) =
   if k=1 then 
    No_DISCARD_ASSUM_TAC1 0 th_list
   else 
    (No_DISCARD_ASSUM_TAC1 (k-1) th_list) THEN ASSUME_TAC th
 in
  if (0 < n) andalso (n <= (length asm)) then
   POP_ASSUM_LIST (No_DISCARD_ASSUM_TAC1 n) (asm,g)
  else
   raise HOL_ERR
   {message          = (No_message n asm),
    origin_function  = "No_DISCARD_ASSUM_TAC",
    origin_structure = "more_utils"}
 end;

val ALL_DISCARD_ASSUM_TAC =
  REPEAT (POP_ASSUM (fn th => ALL_TAC));

(*--- POP_ASSUM ---*)

fun No_POP_ASSUM n f ((asm,g):goal) =
 let
  fun No_POP_ASSUM1 k [] = 
   ALL_TAC
  | No_POP_ASSUM1 k (th::th_list) =
   if k=1 then 
    (No_POP_ASSUM1 0 th_list) THEN ASSUME_TAC th THEN POP_ASSUM f 
   else 
    (No_POP_ASSUM1 (k-1) th_list) THEN ASSUME_TAC th
 in
  if (0 < n) andalso (n <= (length asm)) then
   POP_ASSUM_LIST (No_POP_ASSUM1 n) (asm,g)
  else
   raise HOL_ERR
   {message          = (No_message n asm),
    origin_function  = "No_POP_ASSUM",
    origin_structure = "more_utils"}
 end;

(*--- RULE_ASSUM ---*)

fun No_RULE_ASSUM_TAC n rule ((asm,g):goal) =
 let
  fun No_RULE_ASSUM_TAC1 k [] = 
   ALL_TAC
  | No_RULE_ASSUM_TAC1 k (th::th_list) =
   if k=1 then 
    (No_RULE_ASSUM_TAC1 0 th_list) THEN ASSUME_TAC (rule th)
   else 
    (No_RULE_ASSUM_TAC1 (k-1) th_list) THEN ASSUME_TAC th
 in
  if (0 < n) andalso (n <= (length asm)) then
   POP_ASSUM_LIST (No_RULE_ASSUM_TAC1 n) (asm,g)
  else
   raise HOL_ERR
   {message          = (No_message n asm),
    origin_function  = "No_RULE_ASSUM_TAC",
    origin_structure = "more_utils"}
 end;

(*-------------------------------------------------------------------------*)

val RES_CONTR_TAC = 
 let
  fun RES_CONTR [] = 
    ALL_TAC
  | RES_CONTR (th::thl) =
    let
      val neg_te = if is_neg(concl th) then 
                     (dest_neg(concl th))
                   else
                     (mk_neg(concl th))
    in
      if mem neg_te (map (fn x => concl x) thl) then
        EVERY [
          RULE_ASSUM_TAC (REWRITE_RULE [th]),
          ALL_UNDISCH_TAC,
          REWRITE_TAC []
        ]
      else
        RES_CONTR thl
    end
 in
  ASSUM_LIST RES_CONTR
 end;

(*-------------------------------------------------------------------------*)

fun mk_thm_TAC ((asm,g):goal) =
  REWRITE_TAC [mk_thm([],g)] (asm,g);

(*-------------------------------------------------------------------------*)

(* *********************** MP2_TAC ****************************	*)
(*       A ?- t							*)
(*   ==============  MP2_TAC (A' |- s ==> t)			*)
(*    A ?- s 							*)
(*								*)
(* ************************************************************	*)

fun MP2_TAC th ((asm,g):goal) =
    let val {ant=s,conseq=t} = dest_imp(concl th)
     in ([(asm,s)],fn [t]=> MP th t)
    end

(* ******************* SELECT_EXISTS_TAC **********************	*)
(*								*)
(* 			G |- Q(@x.P x)				*)
(*		==================================		*)
(* 		G |- ?x.P x	G |- !y.P y==> Q y		*)
(*								*)
(* The term @x.P x has to be given as argument. The tactic will	*)
(* then eliminate this term in Q and the subgoals above are 	*)
(* obtained. This tactic only makes sense if G|-?x.P x holds.	*)
(* Otherwise the tactic below should be used.			*)
(* ************************************************************	*)

fun SELECT_EXISTS_TAC t (asm,g) =
    let val SELECT_ELIM_THM = TAC_PROOF( 
	    ([],--`!P Q. (?x:'a. P x) /\ (!y. P y ==> Q y) ==> Q(@x.P x)`--),
	    REPEAT GEN_TAC 
	    THEN SUBST1_TAC(SYM(SELECT_CONV(--`P(@x:'a.P x)`--)))
	    THEN STRIP_TAC THEN RES_TAC)
	val {Bvar=x,Body=Px} = dest_select t
	val P = mk_abs{Bvar=x,Body=Px}
	val y = genvar(type_of x)
	val Q = mk_abs {Bvar=y,Body=subst[{redex=t,residue=y}]g}
	val lemma1 = INST_TYPE[{redex=(==`:'a`==),residue=(type_of x)}] SELECT_ELIM_THM
	val lemma2 = BETA_RULE(SPECL[P,Q]lemma1)
     in
	(MP2_TAC lemma2 THEN CONJ_TAC)(asm,g)
    end

(* *********************** SELECT_TAC *************************	*)
(*								*)
(*			G |- Q(@x.P x)				*)
(* 	   ==========================================		*)
(*	    G |-(?x.P x) => !y. P y ==> Q y | !y.Q y		*)
(*								*)
(* ************************************************************	*)

fun SELECT_TAC t (asm,g) =
    let val SELECT_THM = TAC_PROOF( 
	    ([],--`!P Q. ((?x:'a.P x) => !y. P y ==> Q y | !y.Q y) ==> Q(@x.P x) `--),
	    REPEAT GEN_TAC
	    THEN DISJ_CASES_TAC(SPEC(--`?x:'a.P x`--)BOOL_CASES_AX) 
	    THEN ASM_REWRITE_TAC[] THEN STRIP_TAC
	    THENL[RULE_ASSUM_TAC (REWRITE_RULE [SYM(SELECT_CONV (--`P(@x:'a.P x)`--))])
		  THEN RES_TAC THEN ASM_REWRITE_TAC[],
		  ASM_REWRITE_TAC[]])
	val {Bvar=x,Body=Px} = dest_select t
	val P = mk_abs{Bvar=x,Body=Px}
	val y = genvar(type_of x)
	val Q = mk_abs {Bvar=y,Body=subst[{redex=t,residue=y}]g}
	val lemma1 = INST_TYPE[{redex=(==`:'a`==),residue=(type_of x)}] 
							SELECT_THM
	val lemma2 = BETA_RULE(SPECL[P,Q]lemma1)
     in
	(MP2_TAC lemma2 THEN COND_CASES_TAC)(asm,g)
    end

(* ****************  SELECT_UNIQUE_RULE ***********************	*)
(*								*)
(*       "y"   A1 |- Q[y]  A2 |- !x y.(Q[x]/\Q[y]) ==> (x=y)	*)
(*        ===================================================	*)
(*                A1 U A2 |- (@x.Q[x]) = y			*)
(*								*)
(* Permits substitution for values specified by the Hilbert 	*)
(* Choice operator with a specific value, if and only if unique *)
(* existance of the specific value is proven.			*)
(*                                                              *)
(* Dependency on module Compat removed. 24.6.1994, Ralf Reetz   *)
(* ************************************************************	*)

val SELECT_UNIQUE_THM = TAC_PROOF(
	([],--`!Q y. Q y /\ (!x y:'a.(Q x /\ Q y) ==> (x=y)) ==> ((@x.Q x) = y)`--),
	REPEAT STRIP_TAC THEN SELECT_EXISTS_TAC (--`@x.(Q:'a->bool) x`--)
	THENL[EXISTS_TAC(--`y:'a`--) THEN ASM_REWRITE_TAC[],
	      GEN_TAC THEN DISCH_TAC THEN RES_TAC])

fun SELECT_UNIQUE_RULE y th1 th2 =
    let val Q=(hd o strip_conj o #ant o dest_imp o snd o strip_forall o 
           concl) th2
        val x=(hd o (filter(C mem(free_vars Q))) o fst o strip_forall o 
           concl)th2
        val Q'= mk_abs{Bvar=x,Body=Q}
        val th1'=SUBST 
                     [{thm=SYM (BETA_CONV (--`^Q' ^y`--)),var=(--`b:bool`--)}] 
                     (--`b:bool`--) th1
        in
          (MP (SPECL [(--`$@ ^Q'`--), y] th2)
              (CONJ (BETA_RULE (SELECT_INTRO th1')) th1))
        end

fun SELECT_UNIQUE_TAC (asm,g) = 
    let val {lhs=Qx,rhs=y} = dest_eq g
	val {Bvar=x,Body=Q} = dest_select Qx
	val xty = type_of x
	val Qy = mk_abs{Bvar=x,Body=Q}
	val lemma1 = INST_TYPE[{redex=(==`:'a`==),residue=xty}] SELECT_UNIQUE_THM
	val lemma2 = BETA_RULE(SPECL[Qy,y] lemma1)
     in
	(MATCH_MP_TAC lemma2 THEN CONJ_TAC) (asm,g)
    end

end; (* struct *)
