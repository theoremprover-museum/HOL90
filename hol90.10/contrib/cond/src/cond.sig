(************************ cond.sig **************************************)
(*                                                                      *)
(* Author: Ralf Reetz                                                   *)
(* Date:   29.8.1994                                                    *)
(* Description:                                                         *)
(*                                                                      *)
(*   general help for proving with conditional terms.                   *)
(*                                                                      *)
(* ---                                                                  *)
(*                                                                      *)
(*   RATOR_COND_CONV                                                    *)
(*     moves a rator inward through a conditonal.                       *)
(*      |- f (A => x|y)                                                 *)
(*     ==================                                               *)
(*      |- A => f x|f y                                                 *)
(*                                                                      *)
(*   RATOR_COND_RULE                                                    *)
(*     the same as RATOR_COND_CONV as a rule.                           *)
(*                                                                      *)
(*   RATOR_COND_TAC                                                     *)
(*     the same as RATOR_COND_CONV as a tactic.                         *)
(*                                                                      *)
(*   FILTER_RATOR_COND_CONV                                             *)
(*     moves a selected rator inward through a conditonal.              *)
(*                                                                      *)
(*   FILTER_RATOR_COND_RULE                                             *)
(*     the same as FILTER_RATOR_COND_CONV as a rule.                    *)
(*                                                                      *)
(*   FILTER_RATOR_COND_TAC                                              *)
(*     the same as FILTER_RATOR_COND_CONV as a tactic.                  *)
(*                                                                      *)
(* ---                                                                  *)
(*                                                                      *)
(*   RAND_COND_CONV                                                     *)
(*     moves a rand inward through a conditonal.                        *)
(*      |- (A => f|g) x                                                 *)
(*     ==================                                               *)
(*      |- A => f x|f y                                                 *)
(*                                                                      *)
(*   RAND_COND_RULE                                                     *)
(*     the same as RAND_COND_CONV as a rule.                            *)
(*                                                                      *)
(*   RAND_COND_TAC                                                      *)
(*     the same as RAND_COND_CONV as a tactic.                          *)
(*                                                                      *)
(*   FILTER_RAND_COND_CONV                                              *)
(*     moves a selected rand inward through a conditonal.               *)
(*                                                                      *)
(*   FILTER_RAND_COND_RULE                                              *)
(*     the same as FILTER_RAND_COND_CONV as a rule.                     *)
(*                                                                      *)
(*   FILTER_RAND_COND_TAC                                               *)
(*     the same as FILTER_RAND_COND_CONV as a tactic.                   *)
(*                                                                      *)
(* ---                                                                  *)
(*                                                                      *)
(*   COND_RATOR_CONV                                                    *)
(*     moves a rator outward through a conditonal.                      *)
(*      |- (A => f x|f y)                                               *)
(*     ==================                                               *)
(*      |- f (A => x|y)                                                 *)
(*                                                                      *)
(*   COND_RATOR_RULE                                                    *)
(*     the same as COND_RATOR_CONV as a rule.                           *)
(*                                                                      *)
(*   COND_RATOR_TAC                                                     *)
(*     the same as COND_RATOR_CONV as a tactic.                         *)
(*                                                                      *)
(*   FILTER_COND_RATOR_CONV                                             *)
(*     moves a selected rand inward through a conditonal.               *)
(*                                                                      *)
(*   FILTER_COND_RATOR_RULE                                             *)
(*     the same as FILTER_COND_RATOR_CONV as a rule.                    *)
(*                                                                      *)
(*   FILTER_COND_RATOR_TAC                                              *)
(*     the same as FILTER_COND_RATOR_CONV as a tactic.                  *)
(*                                                                      *)
(* ---                                                                  *)
(*                                                                      *)
(*   COND_RAND_CONV                                                     *)
(*     moves a rand outward through a conditonal.                       *)
(*      |- (A => f x|g x)                                               *)
(*     ==================                                               *)
(*      |- (A => f|g) x                                                 *)
(*                                                                      *)
(*   COND_RAND_RULE                                                     *)
(*     the same as COND_RAND_CONV as a rule.                            *)
(*                                                                      *)
(*   COND_RAND_TAC                                                      *)
(*     the same as COND_RAND_CONV as a tactic.                          *)
(*                                                                      *)
(*   FILTER_COND_RAND_CONV                                              *)
(*     moves a selected rand inward through a conditonal.               *)
(*                                                                      *)
(*   FILTER_COND_RAND_RULE                                              *)
(*     the same as FILTER_COND_RAND_CONV as a rule.                     *)
(*                                                                      *)
(*   FILTER_COND_RAND_TAC                                               *)
(*     the same as FILTER_COND_RAND_CONV as a tactic.                   *)
(*                                                                      *)
(* ---                                                                  *)
(*                                                                      *)
(*   COND_EQ_CONV                                                       *)
(*     moves the right-hand term of an equation inward through a        *)
(*     conditional.                                                     *)
(*      |- (A => x|y) = z                                               *)
(*     ===================                                              *)
(*      |- A => x=z|y=z                                                 *)
(*                                                                      *)
(*   COND_EQ_RULE                                                       *)
(*     the same as COND_EQ_CONV as a rule.                              *)
(*                                                                      *)
(*   COND_EQ_TAC                                                        *)
(*     the same as COND_EQ_CONV as a tactic.                            *)
(*                                                                      *)
(*   FILTER_COND_EQ_CONV                                                *)
(*     moves a selected right-hand term of an equation inward through a *)
(*     conditional.                                                     *)
(*                                                                      *)
(*   FILTER_COND_EQ_RULE                                                *)
(*     the same as FILTER_COND_EQ_CONV as a rule.                       *)
(*                                                                      *)
(*   FILTER_COND_EQ_TAC                                                 *)
(*     the same as FILTER_COND_EQ_CONV as a tactic.                     *)
(*                                                                      *)
(* ---                                                                  *)
(*                                                                      *)
(*   EQ_COND_CONV                                                       *)
(*     moves the right-hand term of equations outward through a         *)
(*     conditional.                                                     *)
(*      |- (A => x=z|y=z)                                               *)
(*     ===================                                              *)
(*      |- (A => x|y) = z                                               *)
(*                                                                      *)
(*   EQ_COND_RULE                                                       *)
(*     the same as EQ_COND_CONV as a rule.                              *)
(*                                                                      *)
(*   EQ_COND_TAC                                                        *)
(*     the same as COND_EQ_CONV as a tactic.                            *)
(*                                                                      *)
(*   FILTER_EQ_COND_CONV                                                *)
(*     moves the selected right-hand term of equations outward through  *)
(*     a conditional.                                                   *)
(*                                                                      *)
(*   FILTER_EQ_COND_RULE                                                *)
(*     the same as FILTER_EQ_COND_CONV as a rule.                       *)
(*                                                                      *)
(*   FILTER_EQ_COND_TAC                                                 *)
(*     the same as FILTER_EQ_COND_CONV as a tactic.                     *)
(*                                                                      *)
(* ---                                                                  *)
(*                                                                      *)
(*   COND_bool_CONV                                                     *)
(*     eleminates conditionals with boolean arms.                       *)
(*      |- A => T|B     |- A => F|B     |- A => T|F     |- A => F|T     *)
(*     =============   =============   =============   =============    *)
(*      |- A\/B         |- ~A/\B        |- A            |- ~A           *)
(*                                                                      *)
(*      |- A => B|T     |- A => B|F     |- A => T|T     |- A => F|F     *)
(*     =============   =============   =============   =============    *)
(*      |- A ==> B      |- A/\B         |- T            |- F            *)
(*                                                                      *)
(*   COND_bool_RULE                                                     *)
(*     same as COND_bool_CONV as a rule.                                *)
(*                                                                      *)
(*   COND_bool_TAC                                                      *)
(*     same as COND_bool_TAC as a tactic.                               *)
(*                                                                      *)
(* ---                                                                  *)
(*                                                                      *)
(*   COND_COND_CONV                                                     *)
(*     reduces conditional of a conditional with the same condition.    *)
(*      |- A => (A => x|y)|z     |- A => (~A => x|y)|z                  *)
(*     ======================   =========================               *)
(*      |- A => x|z              |- A => y|z                            *)
(*                                                                      *)
(*   COND_COND_RULE                                                     *)
(*     same as COND_COND_CONV as a rule.                                *)
(*                                                                      *)
(*   COND_COND_TAC                                                      *)
(*     same as COND_COND_TAC as a tactic.                               *)
(*                                                                      *)
(* ---                                                                  *)
(*                                                                      *)
(*   SWAP_COND_CONV                                                     *)
(*     swaps a conditional subterm of conditional once by using the     *)
(*     following rule:                                                  *)
(*      |- A => (B => x|y)|z                                            *)
(*     =========================                                        *)
(*      |- A/\B => x|(A => y|z)                                         *)
(*                                                                      *)
(*   SWAP_COND_RULE                                                     *)
(*     same as SWAP_COND_CONV as a rule.                                *)
(*                                                                      *)
(*   SWAP_COND_TAC                                                      *)
(*     same as SWAP_COND_TAC as a tatic.                                *)
(*                                                                      *)
(* ---                                                                  *)
(*                                                                      *)
(*   COND_SUBS_CONV                                                     *)
(*     substitutes the free occurences of the condition of a            *)
(*     conditional in the arms of the conditional                       *)
(*      |- x => f|g                                                     *)
(*     =======================                                          *)
(*      |- x => f[x/T]|g[x/F]                                           *)
(*                                                                      *)
(*   COND_SUBS_RULE                                                     *)
(*     same as COND_SUBS_CONV as a rule.                                *)
(*                                                                      *)
(*   COND_SUBS_TAC                                                      *)
(*     same as COND_SUBS_CONV as a tactic.                              *)
(*                                                                      *)
(* ---                                                                  *)
(*                                                                      *)
(*   CHAIN_COND_CONV cond_EQ_CONV t                                     *)
(*     takes a term t of the form                                       *)
(*       p1 => x1 | p2 => y2 | p3 => y3 | ... | pn => yn| yn+1          *)
(*     and a conversion cond_EQ_CONV that states a theorem |-p=T or     *)
(*     |-pi=F for any pi and states a theorem |- t=yj for some yj.      *)
(*                                                                      *)
(*   CHAIN_COND_CASES_CONV x_EQ_CONV c t                                *)
(*     takes a conversion x_EQ_CONV, which takes terms of the form      *)
(*     --`xi=xj`--,where xi and xj are constants and delivers a theorem *)
(*     |- (xi=xj)=T or |-(xi=xj)=F, takes a term c of the form          *)
(*     --`x=xk`--, where x is a variable and xk is a constant, and a    *)
(*     term t of the form --`x=x1 => f1|x=x2 => f2|...|x=xm => fm|fn`-- *)
(*     and returns a theorem                                            *)
(*     |- ((x = xk) ==> t = ... ) /\ (~(x = xk) ==> t = ...).           *)
(*                                                                      *)
(* ---                                                                  *)
(*                                                                      *)
(*   COND_EQ_COND_TAC                                                   *)
(*     divides an equation of two conditionals into three subgoals:     *)
(*       A ?- (t1 => t2|t3) = (t4 => t5|t6)                             *)
(*     ======================================                           *)
(*                  A ?- (t4=t1)                                        *)  
(*      A u t1 u t4   ?- (t2=t5)                                        *)
(*      A u ~t1 u ~t4 ?- (t3=t6)                                        *) 
(*                                                                      *)
(* Used files:                                                          *)
(* Used modules:                                                        *)
(* Used theories:                                                       *)
(* Used libraries:                                                      *)
(*                                                                      *)
(************************************************************************)

signature COND =
sig

val RATOR_COND_CONV        : conv;
val RATOR_COND_RULE        : thm -> thm;
val RATOR_COND_TAC         : tactic;
val FILTER_RATOR_COND_CONV : (term -> bool) -> conv;
val FILTER_RATOR_COND_RULE : (term -> bool) -> thm -> thm;
val FILTER_RATOR_COND_TAC  : (term -> bool) -> tactic;

val RAND_COND_CONV        : conv;
val RAND_COND_RULE        : thm -> thm;
val RAND_COND_TAC         : tactic;
val FILTER_RAND_COND_CONV : (term -> bool) -> conv;
val FILTER_RAND_COND_RULE : (term -> bool) -> thm -> thm;
val FILTER_RAND_COND_TAC  : (term -> bool) -> tactic;

val COND_RATOR_CONV        : conv;
val COND_RATOR_RULE        : thm -> thm;
val COND_RATOR_TAC         : tactic;
val FILTER_COND_RATOR_CONV : (term -> bool) -> conv;
val FILTER_COND_RATOR_RULE : (term -> bool) -> thm -> thm;
val FILTER_COND_RATOR_TAC  : (term -> bool) -> tactic;

val COND_RAND_CONV        : conv;
val COND_RAND_RULE        : thm -> thm;
val COND_RAND_TAC         : tactic;
val FILTER_COND_RAND_CONV : (term -> bool) -> conv;
val FILTER_COND_RAND_RULE : (term -> bool) -> thm -> thm;
val FILTER_COND_RAND_TAC  : (term -> bool) -> tactic;

val COND_EQ_CONV        : conv;
val COND_EQ_RULE        : thm -> thm;
val COND_EQ_TAC         : tactic;
val FILTER_COND_EQ_CONV : (term -> bool) -> conv;
val FILTER_COND_EQ_RULE : (term -> bool) -> thm -> thm;
val FILTER_COND_EQ_TAC  : (term -> bool) -> tactic;

val EQ_COND_CONV        : conv;
val EQ_COND_RULE        : thm -> thm;
val EQ_COND_TAC         : tactic;
val FILTER_EQ_COND_CONV : (term -> bool) -> conv;
val FILTER_EQ_COND_RULE : (term -> bool) -> thm -> thm;
val FILTER_EQ_COND_TAC  : (term -> bool) -> tactic;

val COND_bool_CONV : conv;
val COND_bool_RULE : thm -> thm;
val COND_bool_TAC  : tactic;

val COND_COND_CONV : conv;
val COND_COND_RULE : thm -> thm;
val COND_COND_TAC  : tactic;

val SWAP_COND_CONV : conv;
val SWAP_COND_RULE : thm -> thm;
val SWAP_COND_TAC  : tactic;

val COND_SUBS_CONV : conv;
val COND_SUBS_RULE : thm -> thm;
val COND_SUBS_TAC  : tactic;

val CHAIN_COND_CONV       : conv -> conv;
val CHAIN_COND_CASES_CONV : conv -> term -> conv;

val COND_EQ_COND_TAC    : tactic;

end;
