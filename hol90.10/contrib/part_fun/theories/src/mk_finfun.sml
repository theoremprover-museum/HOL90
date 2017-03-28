(* ===================================================================== *)
(* FILE          : mk_finfun.sml                                         *)
(* DESCRIPTION   : Theory of finite functions.                           *)
(*                                                                       *)
(* AUTHOR        : Elsa L. Gunter, AT&T Bell Laboratories                *)
(* DATE          : 94.10.11                                              *)
(*                                                                       *)
(* ===================================================================== *)

(* Copyright 1994 by AT&T Bell Laboratories *)
(* Share and Enjoy *)

val _ = new_theory "finite_functions";

load_library {lib = utils_lib, theory = "-"};
open ExtraGeneralFunctions;

local
    val path = (!HOLdir)^"contrib/part_fun/theories/"^
	       SysParams.theory_file_type^"/"
in
    val _ = theory_path := path :: (!theory_path)
end;

val _ = new_parent "partial_functions";
val _ = add_theory_to_sml "partial_functions";
val _ = add_theory_to_sml "lift";

val _ = load_library {lib = set_lib, theory = "-"};
val _ = add_theory_to_sml "set";

val finfun_exists_lemma = prove(
(--`?f:'a -> 'b lift. FINITE({x|part_fun_domain f x})`--),
EXISTS_TAC (--`empty_part_fun:'a -> 'b lift`--) THEN
REWRITE_TAC[part_fun_domain_DEF,empty_part_fun_DEF,
	    is_defined_is_not_undefined] THEN
(SUPPOSE_TAC (--`GSPEC(\x:'a.(x,F)) = {}`--) THENL
 [ASM_REWRITE_TAC[FINITE_EMPTY],ALL_TAC]) THEN
REWRITE_TAC[EXTENSION,NOT_IN_EMPTY] THEN
CONV_TAC (DEPTH_CONV Gspec.SET_SPEC_CONV) THEN REWRITE_TAC[]);

(*
val finfun_exists_lemma = |- ?f. FINITE {x | part_fun_domain f x} : thm
*)


val finfun_TY_DEF =
    new_type_definition
    {name = "finfun",
     pred = (--`\f:'a -> 'b lift.FINITE{x|part_fun_domain f x}`--),
     inhab_thm = prove((--`?f.(\f:'a -> 'b lift.
			       FINITE{x|part_fun_domain f x})f`--),
		       BETA_TAC THEN ACCEPT_TAC finfun_exists_lemma)};

(*
val finfun_TY_DEF =
  |- ?rep. TYPE_DEFINITION (\f. FINITE {x | part_fun_domain f x}) rep : thm
*)


val finfun_REP_ABS_DEF =
     define_new_type_bijections
     {name = "finfun_REP_ABS_DEF",
      ABS = "finfun", REP = "finfun_apply",
      tyax = finfun_TY_DEF};

(*
val finfun_REP_ABS_DEF =
  |- (!a. finfun (finfun_apply a) = a) /\
     (!r.
       (\f. FINITE {x | part_fun_domain f x}) r = finfun_apply (finfun r) = r)
  : thm
*)

fun reduce thm = REWRITE_RULE[](BETA_RULE thm);

val finfun_ONE_ONE = reduce(prove_abs_fn_one_one finfun_REP_ABS_DEF);

(*
val finfun_ONE_ONE =
  |- !r r'.
       FINITE {x | part_fun_domain r x} ==>
       FINITE {x | part_fun_domain r' x} ==>
       ((finfun r = finfun r') = r = r') : thm
*)


val finfun_ONTO = reduce(prove_abs_fn_onto finfun_REP_ABS_DEF);

(*
val finfun_ONTO = |- !a. ?r. (a = finfun r) /\ FINITE {x | part_fun_domain r x}
  : thm
*)


val finfun_apply_ONE_ONE = prove_rep_fn_one_one finfun_REP_ABS_DEF;

(*
val finfun_apply_ONE_ONE =
  |- !a a'. (finfun_apply a = finfun_apply a') = a = a' : thm
*)


val finfun_apply_ONTO = reduce(prove_rep_fn_onto finfun_REP_ABS_DEF);

(*
val finfun_apply_ONTO =
  |- !r. FINITE {x | part_fun_domain r x} = (?a. r = finfun_apply a) : thm
*)



val delete_lemma = store_thm("delete_lemma",
(--`!(f:'a -> 'b lift) x.~(part_fun_domain (update_fun f x undefined) x)`--),
REWRITE_TAC[part_fun_domain_DEF,update_fun_DEF] THEN BETA_TAC THEN
REWRITE_TAC[is_defined_lemma]);

(*
val delete_lemma = |- !f x. ~(part_fun_domain (update_fun f x undefined) x)
  : thm
*)


val delete_smaller = store_thm("delete_smaller",
(--`!(f:'a -> 'b lift) y.
 (FINITE {x | part_fun_domain f x} /\ part_fun_domain f y ) ==>
     (CARD {x | part_fun_domain f x} =
      SUC(CARD {x | part_fun_domain (update_fun f y undefined) x}))`--),
REPEAT STRIP_TAC THEN
SUPPOSE_TAC (--`{x | part_fun_domain (f:'a -> 'b lift) x} =
   y INSERT {x | part_fun_domain (update_fun f y undefined) x}`--) THENL
[(UNDISCH_TAC (--`FINITE {x | part_fun_domain (f:'a -> 'b lift) x}`--) THEN
  ASM_REWRITE_TAC[FINITE_INSERT] THEN
  DISCH_THEN (fn th => REWRITE_TAC [MATCH_MP CARD_INSERT th]) THEN
  CONV_TAC (DEPTH_CONV Gspec.SET_SPEC_CONV) THEN REWRITE_TAC[delete_lemma]),
 (REWRITE_TAC[EXTENSION,IN_INSERT,update_fun_DEF] THEN
  CONV_TAC (DEPTH_CONV Gspec.SET_SPEC_CONV) THEN
  GEN_TAC THEN (ASM_CASES_TAC (--`(x:'a) = y`--) THEN ASM_REWRITE_TAC[]) THEN
  REWRITE_TAC[part_fun_domain_DEF] THEN BETA_TAC THEN
  FIRST_ASSUM (fn th => REWRITE_TAC[CONV_RULE(RAND_CONV SYM_CONV) th]))]);

(*
val delete_smaller =
  |- !f y.
       FINITE {x | part_fun_domain f x} /\ part_fun_domain f y ==>
       (CARD {x | part_fun_domain f x} =
        SUC (CARD {x | part_fun_domain (update_fun f y undefined) x})) : thm
*)


val empty_part_fun_domain_EMPTY = store_thm("empty_part_fun_domain_EMPTY",
(--`{x | part_fun_domain (empty_part_fun:'a -> 'b lift) x} = {}`--),
REWRITE_TAC[EXTENSION,part_fun_domain_DEF,empty_part_fun_DEF,
	    is_defined_lemma] THEN
GEN_TAC THEN CONV_TAC (DEPTH_CONV Gspec.SET_SPEC_CONV) THEN
REWRITE_TAC[NOT_IN_EMPTY]);

(*
val empty_part_fun_domain_EMPTY =
  |- {x | part_fun_domain empty_part_fun x} = {} : thm
*)

val EMPTY_part_fun_domain_imp_empty_part_fun =
store_thm("EMPTY_part_fun_domain_imp_empty_part_fun",
(--`!f:'a -> 'b lift.
 ({x | part_fun_domain f x} = {}) ==> (f = empty_part_fun)`--),
GEN_TAC THEN
REWRITE_TAC[EXTENSION, part_fun_domain_DEF, empty_part_fun_DEF] THEN
CONV_TAC (DEPTH_CONV (Gspec.SET_SPEC_CONV ORELSEC FUN_EQ_CONV)) THEN
BETA_TAC THEN REWRITE_TAC[NOT_IN_EMPTY,is_defined_is_not_undefined]);

(*
val EMPTY_part_fun_domain_imp_empty_part_fun =
  |- !f. ({x | part_fun_domain f x} = {}) ==> (f = empty_part_fun) : thm
*)


val GEN_INDUCTION1 = prove (
(--`!P.(!n. (!m. m < n ==> P m) ==> P n) ==> (!n. P n)`--),
GEN_TAC THEN DISCH_TAC THEN
MATCH_MP_TAC (theorem "arithmetic" "GEN_INDUCTION") THEN
CONJ_TAC THENL [ALL_TAC, FIRST_ASSUM ACCEPT_TAC] THEN
FIRST_ASSUM MATCH_MP_TAC THEN
REWRITE_TAC [(theorem "prim_rec" "NOT_LESS_0")]);

(*
val GEN_INDUCTION1 = |- !P. (!n. (!m. m < n ==> P m) ==> P n) ==> (!n. P n)
  : thm
*)

val GEN_INDUCTION2 = prove (
(--`!P. P 0 /\ (!k. (!m. m <= k ==> P m) ==> P (SUC k)) ==> (!n. P n)`--),
GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC GEN_INDUCTION1 THEN GEN_TAC THEN 
STRIP_ASSUME_TAC (SPEC (--`n:num`--)(theorem "arithmetic" "num_CASES")) THEN
ASM_REWRITE_TAC[theorem "arithmetic" "LESS_EQ_MONO",
		theorem "arithmetic" "LESS_EQ"]);

(*
val GEN_INDUCTION2 =
  |- !P. P 0 /\ (!k. (!m. m <= k ==> P m) ==> P (SUC k)) ==> (!n. P n) : thm
*)


val finfun_induction_lemma = prove(
(--`!P. (!f n. ((CARD {x | part_fun_domain (finfun_apply f) x} = n) /\
		(!g. CARD {x | part_fun_domain (finfun_apply g) x} < n ==>
		    P g)) ==> P f) ==>
 (!f:('a,'b)finfun. P f)`--),
REPEAT STRIP_TAC THEN
SUPPOSE_TAC
  (--`!n f:('a,'b)finfun. (CARD {x | part_fun_domain (finfun_apply f) x} = n)
   ==> P f`--) THENL
[(FIRST_ASSUM MATCH_MP_TAC THEN
  (fn gl as (_,goal) => EXISTS_TAC (lhs(#Body(dest_exists goal))) gl) THEN
  REFL_TAC),
 ((fn gl as (_,goal) =>
   MATCH_MP_TAC(BETA_RULE(SPEC(rand goal)GEN_INDUCTION1)) gl) THEN
  REPEAT STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
  (fn gl as (_,goal) =>
   EXISTS_TAC (lhs(#conj1(dest_conj(#Body(dest_exists goal))))) gl) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  FIRST_ASSUM (fn th1 => (FIRST_ASSUM (fn th2 =>
    MATCH_MP_TAC (MATCH_MP th2 th1)))) THEN REFL_TAC)]);

(*
val finfun_induction_lemma =
  |- !P.
       (!f n.
         (CARD {x | part_fun_domain (finfun_apply f) x} = n) /\
         (!g. CARD {x | part_fun_domain (finfun_apply g) x} < n ==> P g) ==>
         P f) ==>
       (!f. P f) : thm
*)


val gen_finfun_induction = store_thm("gen_finfun_induction",
(--`!P.
  (!f.(!g. CARD {x | part_fun_domain (finfun_apply g) x} <
	   CARD {x | part_fun_domain (finfun_apply f) x} ==> P g) ==> P f) ==>
  (!f:('a,'b)finfun. P f)`--),
GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC finfun_induction_lemma THEN
REPEAT GEN_TAC THEN
DISCH_THEN (fn th => FIRST_ASSUM MATCH_MP_TAC THEN STRIP_ASSUME_TAC th) THEN
ASM_REWRITE_TAC[]);

(*
val gen_finfun_induction =
  |- !P.
       (!f.
         (!g.
           CARD {x | part_fun_domain (finfun_apply g) x} <
           CARD {x | part_fun_domain (finfun_apply f) x} ==>
           P g) ==>
         P f) ==>
       (!f. P f) : thm
*)

val _ = export_theory();
