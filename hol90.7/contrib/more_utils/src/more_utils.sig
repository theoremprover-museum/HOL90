(************************ more_utils.sig ********************************)
(*                                                                      *)
(* Author: Ralf Reetz                                                   *)
(* Date:   5.10.1994                                                    *)
(*                                                                      *)
(* Description:                                                         *)
(*                                                                      *)
(*   Some helpful stuff for proving in general.                         *)
(*                                                                      *)
(*   No_UNDISCH_TAC                                                     *)
(*     Takes a number ni and undischarges the ni-th assumption. E.g.    *)
(*     No_UNDISCH_TAC 1 undischarges the first assumption.              *)
(*                                                                      *)
(*   ALL_UNDISCH_TAC                                                    *)
(*     undischarges all assumptions.                                    *)
(*                                                                      *)
(*   No_DISCARD_ASSUM_TAC                                               *)
(*     Takes a number ni and throws the ni-th assumption away. E.g.     *)
(*     No_DISCARD_ASSUM_TAC 1 throws the first assumption away.         *)
(*                                                                      *)
(*   ALL_DISCARD_ASSUM_TAC                                              *)
(*     throws all assumptions away.                                     *)
(*                                                                      *)
(*   No_RULE_ASSUM_TAC                                                  *)
(*     Takes a number ni and maps an inference rule over the ni-th      *)
(*     assumption. E.g. RULE_ASSUM_No_TAC 1 rules an inference rule     *)
(*     over the first assumption.                                       *)
(*                                                                      *)
(*   No_POP_ASSUM                                                       *)
(*     Takes a number ni applies tactic generated from the ni-th        *)
(*     element of a goal's assumption list. E.g. No_POP_ASSUM 1 is the  *)
(*     same as POP_ASSUM.                                               *)
(*                                                                      *)
(*   RES_CONTR_TAC                                                      *)
(*     solves a goal, if there is a theorem |- A and it's contradiction *)
(*     |- ~A in the assumption list of the goal.                        *)
(*                                                                      *)
(*   mk_thm_TAC                                                         *)
(*     proves every goal (should be used for test purposes only!)       *)
(*                                                                      *)
(*   SELECT_EXISTS_TAC (from Klaus Schneider)                     	*)
(*								        *)
(* 			G |- Q(@x.P x)				        *)
(*		==================================		        *)
(* 		G |- ?x.P x	G |- !y.P y==> Q y		        *)
(*								        *)
(*     The term @x.P x has to be given as argument. The tactic will     *)
(*     then eliminate this term in Q and the subgoals above are  	*)
(*     obtained. This tactic only makes sense if G|-?x.P x holds. 	*)
(*     Otherwise the tactic SELECT_TAC should be used.          	*)
(*                                                                      *)
(*   SELECT_TAC (from Klaus Schneider)                                  *)
(*						        		*)
(*			G |- Q(@x.P x)				        *)
(* 	   ==========================================	          	*)
(*	    G |-(?x.P x) => !y. P y ==> Q y | !y.Q y		        *)
(*								        *)
(*   SELECT_UNIQUE_RULE, SELECT_UNIQUE_TAC (J. Harrison)         	*)
(*								        *)
(*       "y"   A1 |- Q[y]  A2 |- !x y.(Q[x]/\Q[y]) ==> (x=y)        	*)
(*        ===================================================	        *)
(*                A1 U A2 |- (@x.Q[x]) = y			        *)
(*								        *)
(*    Permits substitution for values specified by the Hilbert Choice  	*)
(*    operator with a specific value, if and only if unique existance   *)
(*    of the specific value is proven.	                		*)
(*                                                                      *)
(* Used files:                                                          *)
(* Used modules:                                                        *)
(* Used theories:                                                       *)
(* Used libraries:                                                      *)
(*                                                                      *)
(************************************************************************)

signature MORE_UTILS =
sig

val No_UNDISCH_TAC        : int -> tactic;
val ALL_UNDISCH_TAC       : tactic;
val No_DISCARD_ASSUM_TAC  : int -> tactic;
val ALL_DISCARD_ASSUM_TAC : tactic;
val No_RULE_ASSUM_TAC     : int -> ((thm -> thm) -> tactic);
val No_POP_ASSUM          : int -> (thm_tactic -> tactic);

val RES_CONTR_TAC        : tactic;

val mk_thm_TAC           : tactic;

val SELECT_EXISTS_TAC    : term -> tactic;
val SELECT_TAC           : term -> tactic;
val SELECT_UNIQUE_RULE   : term -> thm -> thm -> thm;
val SELECT_UNIQUE_TAC    : tactic;

end;
