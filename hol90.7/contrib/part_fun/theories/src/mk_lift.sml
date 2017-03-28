(* ===================================================================== *)
(* FILE          : mk_part_fun.sml                                       *)
(* DESCRIPTION   : Theory of lifts and partial functions.                *)
(*                                                                       *)
(* AUTHOR        : Elsa L. Gunter, AT&T Bell Laboratories                *)
(* DATE          : 92.08.21                                              *)
(*                                                                       *)
(* ===================================================================== *)

(* Copyright 1992 by AT&T Bell Laboratories *)
(* Share and Enjoy *)

val _ = load_library {lib = utils_lib, theory = "-"};
open ExtraGeneralFunctions;

(* Set the path to write the theory to. *)

local
    val path = (!HOLdir)^"contrib/part_fun/theories/"^
	       Globals.theory_file_type^"/"
in
    val _ = theory_path := path :: (!theory_path)
end;

val _ = new_theory "lift";

val _ = add_theory_structure_to_sml{structure_name = "one",
				    theory_name = "one"};
open one;

val _ = add_theory_structure_to_sml{structure_name = "sum",
                                     theory_name = "sum"};
open sum;


val lift_TY_DEF =
    new_type_definition
    {name = "lift",
     pred = (--`\x:'a + one.T`--),
     inhab_thm = prove((--`?x:'a + one.(\x.T)x`--),
		       BETA_TAC THEN EXISTS_TAC(--`x:'a + one`--) THEN
		       ACCEPT_TAC TRUTH)};

(*
val lift_TY_DEF = |- ?rep. TYPE_DEFINITION (\x. T) rep : thm
*)


val lift_REP_ABS_DEF =
     define_new_type_bijections
     {name = "lift_REP_ABS_DEF",
      ABS = "lift_ABS", REP = "lift_REP",
      tyax = lift_TY_DEF};

(*
val lift_REP_ABS_DEF =
  |- (!a. lift_ABS (lift_REP a) = a) /\
     (!r. (\x. T) r = lift_REP (lift_ABS r) = r) : thm
*)

fun reduce thm = REWRITE_RULE[](BETA_RULE thm);

val lift_ABS_ONE_ONE = reduce(prove_abs_fn_one_one lift_REP_ABS_DEF);

(*
val lift_ABS_ONE_ONE = |- !r r'. (lift_ABS r = lift_ABS r') = r = r' : thm
*)


val lift_ABS_ONTO = reduce(prove_abs_fn_onto lift_REP_ABS_DEF);

(*
val lift_ABS_ONTO = |- !a. ?r. a = lift_ABS r : thm
*)


val lift_REP_ONE_ONE = prove_rep_fn_one_one lift_REP_ABS_DEF;

(*
val lift_REP_ONE_ONE = |- !a a'. (lift_REP a = lift_REP a') = a = a' : thm
*)


val lift_REP_ONTO = reduce(prove_rep_fn_onto lift_REP_ABS_DEF);

(*
val lift_REP_ONTO = |- !r. ?a. r = lift_REP a : thm
*)


val lift_DEF = new_definition("lift_DEF",
(--`!x:'a.lift x = lift_ABS(INL x)`--));

(*
val lift_DEF = |- !x. lift x = lift_ABS (INL x) : thm
*)


val undefined_DEF = new_definition("undefined_DEF",
(--`(undefined:'a lift) = lift_ABS(INR one)`--));

(*
val undefined_DEF = |- undefined = lift_ABS (INR one) : thm
*)


val lift_CASES = store_thm("lift_CASES",
(--`!l:'a lift. (?x. l = lift x) \/ (l = undefined)`--),
GEN_TAC THEN PURE_REWRITE_TAC[lift_DEF,undefined_DEF] THEN
PURE_ONCE_REWRITE_TAC[SYM(SPEC_ALL lift_REP_ONE_ONE)] THEN
PURE_ONCE_REWRITE_TAC[reduce(lift_REP_ABS_DEF)] THEN
STRIP_ASSUME_TAC (ISPEC (--`lift_REP (l:'a lift)`--) ISL_OR_ISR) THENL
[(DISJ1_TAC THEN IMP_RES_TAC INL THEN POP_ASSUM (SUBST1_TAC o SYM) THEN 
  EXISTS_TAC (--`OUTL (lift_REP (l:'a lift))`--) THEN REFL_TAC),
 (DISJ2_TAC THEN IMP_RES_TAC INR THEN POP_ASSUM (SUBST1_TAC o SYM) THEN
  ONCE_REWRITE_TAC[one] THEN REFL_TAC)]);

(*
val lift_CASES = |- !l. (?x. l = lift x) \/ (l = undefined) :thm
*)


val lift_INDUCTION = store_thm("lift_INDUCTION",
(--`!P. (!x. P (lift x)) /\ P undefined ==> (!l:'a lift. P l)`--),
GEN_TAC THEN STRIP_TAC THEN GEN_TAC THEN
STRIP_ASSUME_TAC (SPEC_ALL lift_CASES) THEN
ASM_REWRITE_TAC[]);

(*
val lift_INDUCTION =
  |- !P. (!x. P (lift x)) /\ P undefined ==> (!l. P l) :thm
*)


val lift_ONE_ONE = store_thm("lift_ONE_ONE",
(--`!x x':'a. (lift x = lift x') = x = x'`--),
GEN_TAC THEN GEN_TAC THEN
(EQ_TAC THENL [ALL_TAC,DISCH_THEN SUBST1_TAC THEN REFL_TAC]) THEN
REWRITE_TAC[lift_DEF,lift_ABS_ONE_ONE] THEN
DISCH_THEN (fn th => ASSUME_TAC(AP_TERM (--`OUTL :'a + one -> 'a`--)th)) THEN
FIRST_ASSUM (UNDISCH_TAC o concl) THEN
REWRITE_TAC [OUTL]);

(*
val lift_ONE_ONE = |- !x x'. (lift x = lift x') = x = x' :thm
*)


val lift_constructors_distinct = store_thm("lift_constructors_distinct",
(--`!x:'a. ~(lift x = undefined)`--),
GEN_TAC THEN REWRITE_TAC[lift_DEF, undefined_DEF, lift_ABS_ONE_ONE] THEN
STRIP_TAC THEN
FIRST_ASSUM (ASSUME_TAC o AP_TERM (--`ISL:'a + one -> bool`--)) THEN
FIRST_ASSUM (UNDISCH_TAC o concl) THEN REWRITE_TAC[ISL]);

(*
val lift_constructors_distinct = |- !x. ~(lift x = undefined) :thm
*)


val lift_Axiom = store_thm("lift_Axiom",
(--`!(f:'a -> 'b) e. ?!fn. (!x. fn (lift x) = f x) /\ (fn undefined = e)`--),
GEN_TAC THEN GEN_TAC THEN
CONV_TAC EXISTS_UNIQUE_CONV THEN CONJ_TAC THENL
[(PURE_REWRITE_TAC[lift_DEF,undefined_DEF] THEN
  STRIP_ASSUME_TAC (EXISTENCE (BETA_RULE
     (ISPECL[(--`\x:'a.((f x):'b)`--),(--`\x:one.(e:'b)`--)]sum_Axiom))) THEN
  EXISTS_TAC (--`\x:'a lift.((h(lift_REP x)):'b)`--) THEN BETA_TAC THEN
  ASM_REWRITE_TAC[reduce lift_REP_ABS_DEF]),
 (REPEAT STRIP_TAC THEN CONV_TAC FUN_EQ_CONV THEN GEN_TAC THEN
  STRIP_ASSUME_TAC (SPEC_ALL lift_CASES) THEN ASM_REWRITE_TAC[])]);

(*
val lift_Axiom =
  |- !f e. ?!fn. (!x. fn (lift x) = f x) /\ (fn undefined = e) :thm
*)
    

val undef_not_lift =
    save_thm("undef_not_lift",
	     CONV_RULE (ONCE_DEPTH_CONV SYM_CONV) lift_constructors_distinct);

(*
val undef_not_lift = |- !x. ~(undefined = lift x) : thm
*)


val undefined_not_exists_THM = store_thm("undefined_not_exists_THM",
(--`!y.(y = undefined) = ~(?x:'a.y = lift x)`--),
GEN_TAC THEN EQ_TAC THEN DISCH_TAC THENL
[CONV_TAC NOT_EXISTS_CONV THEN CONV_TAC (ONCE_DEPTH_CONV SYM_CONV) THEN
 ASM_REWRITE_TAC [lift_constructors_distinct],
 POP_ASSUM (STRIP_ASSUME_TAC o (CONV_RULE NOT_EXISTS_CONV)) THEN
 STRIP_ASSUME_TAC (SPEC (--`y:'a lift`--) lift_CASES) THEN
 RES_TAC]);

(*
val undefined_not_exists_THM =
  |- !y. (y = undefined) = ~(?x. y = lift x) :thm
*)


val exists_not_undefined_THM = save_thm ("exists_not_undefined_THM",
GEN_ALL(REWRITE_RULE [](AP_TERM (--`~`--)
			(SYM (SPEC_ALL undefined_not_exists_THM)))));

(*
val exists_not_undefined_THM = |- !y. (?x. y = lift x) = ~(y = undefined) : thm
*)


val is_defined_DEF = new_definition("is_defined_DEF",
(--`!x.(is_defined x = (?y:'a.(x = lift y)))`--));

(*
val is_defined_DEF = |- !x. is_defined x = (?y. x = lift y) : thm
*)


val is_defined_lemma = store_thm("is_defined_lemma",
(--`(!x:'a. is_defined (lift x)) /\ ~(is_defined (undefined:'a lift))`--),
REWRITE_TAC[is_defined_DEF,SYM(SPEC_ALL undefined_not_exists_THM)] THEN
GEN_TAC THEN EXISTS_TAC (--`x:'a`--) THEN REFL_TAC);

(*
val is_defined_lemma =
  |- (!x. is_defined (lift x)) /\ ~(is_defined undefined) : thm
*)

val is_defined_is_not_undefined = store_thm("is_defined_is_not_undefined",
(--`!x:'a lift.is_defined x = ~(x = undefined)`--),
REWRITE_TAC[undefined_not_exists_THM,is_defined_DEF]);

(*
val is_defined_is_not_undefined = |- !x. is_defined x = ~(x = undefined) : thm
*)


val lower_DEF =
       new_recursive_definition
         {name = "lower_DEF",
	  fixity = Prefix,
	  rec_axiom = lift_Axiom,
	  def = (--`!x:'a. lower (lift x) = x`--)};

(*
val lower_DEF = |- !x. lower (lift x) = x :thm
*)


val lift_lower_THM = store_thm ("lift_lower_THM",
(--`(!y:'a lift.(lift (lower y) = y) = is_defined y)`--),
GEN_TAC THEN EQ_TAC THEN DISCH_TAC THENL
[FIRST_ASSUM (fn thm => PURE_ONCE_REWRITE_TAC [SYM thm]) THEN
 REWRITE_TAC [is_defined_lemma],
 POP_ASSUM (fn thm => STRIP_ASSUME_TAC
	              (REWRITE_RULE [is_defined_DEF]thm)) THEN
 ASM_REWRITE_TAC [lower_DEF]]);

(*
val lift_lower_THM = |- !y. (lift (lower y) = y) = is_defined y : thm
*)


val lower_ONE_ONE = store_thm("lower_ONE_ONE",
(--`!x y:'a lift. (is_defined x /\ is_defined y) ==>
    ((lower x = lower y) = (x = y))`--),
REPEAT GEN_TAC THEN
REWRITE_TAC[SYM(SPEC_ALL lift_lower_THM)] THEN STRIP_TAC THEN
EQ_TAC THENL
[DISCH_THEN
 (fn th => let val th1 = AP_TERM (--`lift:'a -> 'a lift`--) th
	   in ASSUME_TAC th1 THEN UNDISCH_TAC (concl th1) end) THEN
 ASM_REWRITE_TAC[],
 DISCH_TAC THEN ASM_REWRITE_TAC[]]);

(*
val lower_ONE_ONE =
  |- !x y. is_defined x /\ is_defined y ==> ((lower x = lower y) = x = y) : thm
*)

val _ = export_theory ();
