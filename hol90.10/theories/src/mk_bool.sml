(* ===================================================================== *)
(* FILE          : mk_bool.sml                                           *)
(* DESCRIPTION   : Definition of the logical constants and assertion of  *)
(*                 the axioms. Translated from hol88.                    *)
(*                                                                       *)
(* AUTHOR        : (c) Mike Gordon, University of Cambridge              *)
(* TRANSLATOR    : Konrad Slind, University of Calgary                   *)
(* DATE          : September 11, 1991                                    *)
(* MODIFIED BY   : Donald Syme, University of Cambridge, October 1995    *)
(*                 This file now constructs - ld_bool loads if not       *)
(*                 remaking theory files.                                *)
(* ===================================================================== *)


structure boolThry : boolThrySig =
struct

structure Min = Min; (* Create dependency on "min" theory *)
structure Exists = Exists; (* Create dependency on defn of "?".  *)

open CoreHol.Theory;
open CoreHol.Const_def;
open Parse;

(*-------------------------------------------------------------------
 * The rest of the theory bool.                          DRS 
 *------------------------------------------------------------------*) 

  val _ = Lib.try extend_theory "bool";

  val T_DEF = Lib.try new_definition("TRUTH", 
     --`T = ((\x:bool. x) = \x:bool. x)`--);

  val FORALL_DEF = new_binder_definition ("FORALL_DEF", 
     --`! = (\P:'a->bool. P = \x. T)`--);

  val AND_DEF = new_infix_definition("AND_DEF",
     --`/\ = \t1. \t2. !t. (t1 ==> (t2 ==> t)) ==> t`--, 400);

  val OR_DEF = new_infix_definition("OR_DEF",
     --`\/ = \t1 t2. !t. (t1 ==> t) ==> ((t2 ==> t) ==> t)`--, 300);

  val F_DEF = new_definition("F_DEF",
     --`F = !t.t`--);

  val NOT_DEF = new_definition("NOT_DEF",
     --`~ = \t. t ==> F`--);

  val EXISTS_UNIQUE_DEF = new_binder_definition("EXISTS_UNIQUE_DEF",
            --`?! = \P:'a->bool. ($? P) /\ !x y. (P x /\ P y) ==> (x=y)`--);

  val LET_DEF = new_definition("LET_DEF", 
            --`LET = \(f:'a->'b) (x:'a). f x`--);

  val COND_DEF = new_definition("COND_DEF",
            --`COND = \t t1 t2. @x:'a. ((t=T)==>(x=t1)) /\ 
                                       ((t=F)==>(x=t2))`--);

  val ONE_ONE_DEF = new_definition("ONE_ONE_DEF",
            --`ONE_ONE (f:'a->'b) = !x1 x2. (f x1 = f x2) ==> (x1 = x2)`--);

  val ONTO_DEF = new_definition("ONTO_DEF",
            --`ONTO (f:'a->'b) = !y.?x. y = f x`--);

  val TYPE_DEFINITION = new_definition("TYPE_DEFINITION",
            --`!P rep. TYPE_DEFINITION (P:'a->bool) (rep:'b->'a) =
                       (!x' x''. (rep x' = rep x'') ==> (x' = x'')) /\	
                       (!x. P x = (?x'. x = rep x'))`--);

(* AXIOMS *)
  val BOOL_CASES_AX = new_open_axiom("BOOL_CASES_AX", 
            --`!t:bool. (t=T) \/ (t=F)`--);

  val IMP_ANTISYM_AX = new_open_axiom("IMP_ANTISYM_AX", 
            --`!t1 t2. (t1 ==> t2) ==> ((t2 ==> t1) ==> (t1 = t2))`--);

  val ETA_AX = new_open_axiom("ETA_AX", 
            --`!t:'a->'b. (\x. t x) = t`--);

  val SELECT_AX = new_open_axiom("SELECT_AX",
            --`!(P:'a->bool) x. P x ==> P ($@ P)`--);

  val INFINITY_AX = new_open_axiom("INFINITY_AX", 
            --`?f:ind->ind. ONE_ONE f /\ ~ONTO f`--)

val _ = export_theory();

end; (* MK_BOOL *)
