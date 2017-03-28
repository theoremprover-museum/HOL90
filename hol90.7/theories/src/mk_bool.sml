(* ===================================================================== *)
(* FILE          : mk_bool.sml                                           *)
(* DESCRIPTION   : Definition of the logical constants and assertion of  *)
(*                 the axioms. Translated from hol88.                    *)
(*                                                                       *)
(* AUTHOR        : (c) Mike Gordon, University of Cambridge              *)
(* TRANSLATOR    : Konrad Slind, University of Calgary                   *)
(* DATE          : September 11, 1991                                    *)
(* ===================================================================== *)


structure Bool : Mk_bool_sig =
struct
type thm = Theory.Thm.thm;

val -- = Term_io.Parse.--;

(* The rest of the theory bool *) 

val _ = Theory.extend_theory "bool"; 

val T_DEF = Const_def.new_definition("TRUTH", 
            --`T = ((\x:bool. x) = \x:bool. x)`--);

val FORALL_DEF = Const_def.new_binder_definition ("FORALL_DEF", 
            --`! = (\P:'a->bool. P = \x. T)`--);

val AND_DEF = Const_def.new_infix_definition("AND_DEF",
            --`/\ = \t1. \t2. !t. (t1 ==> (t2 ==> t)) ==> t`--, 400);

val OR_DEF = Const_def.new_infix_definition("OR_DEF",
            --`\/ = \t1 t2. !t. (t1 ==> t) ==> ((t2 ==> t) ==> t)`--, 300);

val F_DEF = Const_def.new_definition("F_DEF",
            --`F = !t.t`--);

val NOT_DEF = Const_def.new_definition("NOT_DEF",
            --`~ = \t. t ==> F`--);

val EXISTS_UNIQUE_DEF = Const_def.new_binder_definition("EXISTS_UNIQUE_DEF",
            --`?! = \P:'a->bool. ($? P) /\ !x y. (P x /\ P y) ==> (x=y)`--);

val LET_DEF = Const_def.new_definition("LET_DEF", 
            --`LET = \(f:'a->'b) (x:'a). f x`--);

val COND_DEF = Const_def.new_definition("COND_DEF",
            --`COND = \t t1 t2. @x:'a. ((t=T)==>(x=t1)) /\ 
                                       ((t=F)==>(x=t2))`--);

val ONE_ONE_DEF = Const_def.new_definition("ONE_ONE_DEF",
            --`ONE_ONE (f:'a->'b) = !x1 x2. (f x1 = f x2) ==> (x1 = x2)`--);

val ONTO_DEF = Const_def.new_definition("ONTO_DEF",
            --`ONTO (f:'a->'b) = !y.?x. y = f x`--);

val TYPE_DEFINITION = Const_def.new_definition("TYPE_DEFINITION",
            --`!P rep. TYPE_DEFINITION (P:'a->bool) (rep:'b->'a) =
                       (!x' x''. (rep x' = rep x'') ==> (x' = x'')) /\	
                       (!x. P x = (?x'. x = rep x'))`--);

(* AXIOMS *)
val BOOL_CASES_AX = Theory.new_open_axiom("BOOL_CASES_AX", 
            --`!t:bool. (t=T) \/ (t=F)`--);

val IMP_ANTISYM_AX = Theory.new_open_axiom("IMP_ANTISYM_AX", 
            --`!t1 t2. (t1 ==> t2) ==> ((t2 ==> t1) ==> (t1 = t2))`--);

val ETA_AX = Theory.new_open_axiom("ETA_AX", 
            --`!t:'a->'b. (\x. t x) = t`--);

val SELECT_AX = Theory.new_open_axiom("SELECT_AX",
            --`!(P:'a->bool) x. P x ==> P ($@ P)`--);

val INFINITY_AX = Theory.new_open_axiom("INFINITY_AX", 
            --`?f:ind->ind. ONE_ONE f /\ ~ONTO f`--);

val _ = Theory.close_theory();
val _ = Theory.export_theory();

end; (* MK_BOOL *)
