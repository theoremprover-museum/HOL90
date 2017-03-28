(* =====================================================================*)
(* FILE		: mk_option.ml						*)
(* DESCRIPTION   : Creates a theory of SML like options         	*)
(* WRITES FILES	: option.th						*)
(*									*)
(* AUTHOR	: (c) D. Syme 1988					*)
(* DATE		: 95.04.25						*)
(* REVISED	:       						*)
(* TRANSLATED   :                                                       *)
(* =====================================================================*)

val _ = load_library_in_place simp_lib;
open Simplifier;
infix ++;

(* Set the path to write the theory to. *)
local
    val path = (!Globals.HOLdir)^"library/option/theories/"^
               SysParams.theory_file_type^"/"
in
    val _ =  theory_path := path::(!theory_path)
end;

(* ---------------------------------------------------------------------*)
(* Create the new theory						*)
(* ---------------------------------------------------------------------*)
new_theory "option";

val option_Axiom = define_type {
	fixities=[Term.Prefix,Term.Prefix], 
	name="option_Axiom", 
	type_spec= `option = SOME of 'a | NONE`};

val option_Induct = save_thm("option_Induct", 
			Rec_type_support.prove_induction_thm option_Axiom);


val SOME_11 = save_thm("SOME_11", 
		Rec_type_support.prove_constructors_one_one option_Axiom);

val (NOT_NONE_SOME,NOT_SOME_NONE) = 
    let val thm = Rec_type_support.prove_constructors_distinct option_Axiom in
        (save_thm("NOT_NONE_SOME",GSYM thm), 
         save_thm("NOT_SOME_NONE",thm))
    end;

val option_CASES = save_thm("option_CASES", 
		Rec_type_support.prove_cases_thm option_Induct);


val option_CASE_DEF = new_recursive_definition {name="option_CASE_DEF",
         fixity=Term.Prefix,
         rec_axiom=option_Axiom,
         def=(--`(option_CASE (u:'b) f (SOME (x:'a)) = f x) /\ 
                 (option_CASE u f NONE = u)`--)};

val option_APPLY_DEF = new_recursive_definition {name="option_APPLY_DEF",
         fixity=Term.Prefix,
         rec_axiom=option_Axiom,
         def=(--`(option_APPLY (f:'a->'b) (SOME x) = SOME (f x)) /\ 
                 (option_APPLY f NONE = NONE)`--)};

val IS_SOME_DEF = new_recursive_definition {name="IS_SOME_DEF",
         fixity=Term.Prefix,
         rec_axiom=option_Axiom,
         def=(--`(IS_SOME (SOME (x:'a)) = T) /\ (IS_SOME NONE = F)`--)};

val IS_NONE_DEF = new_recursive_definition {name="IS_NONE_DEF",
         fixity=Term.Prefix,
         rec_axiom=option_Axiom,
         def=(--`(IS_NONE (SOME (x:'a)) = F) /\ (IS_NONE NONE = T)`--)};

val THE_DEF = new_recursive_definition {name="THE_DEF",
         fixity=Term.Prefix,
         rec_axiom=option_Axiom,
         def=(--`(THE (SOME (x:'a)) = x)`--)};

val option_defs_ss = 
    hol_ss ++
    rewrites [IS_SOME_DEF, THE_DEF, IS_NONE_DEF, option_CASES,
              NOT_NONE_SOME,NOT_SOME_NONE, SOME_11, option_CASE_DEF,
              option_APPLY_DEF];

fun OPTION_CASES_TAC t = STRUCT_CASES_TAC (ISPEC t option_CASES);

val IS_NONE_EQ_NONE = prove(
(--`!x:'a option. IS_NONE x = (x = NONE)`--),
    GEN_TAC 
    THEN OPTION_CASES_TAC (--`(x :'a option)`--) 
    THEN ASM_SIMP_TAC option_defs_ss []
);

val NOT_IS_SOME_EQ_NONE = prove((--`!x:'a option. ~(IS_SOME x) = (x = NONE)`--),
    GEN_TAC 
    THEN OPTION_CASES_TAC (--`(x :'a option)`--) 
    THEN ASM_SIMP_TAC option_defs_ss []
);

val IS_SOME_EQ_EXISTS = prove(
(--`!x:'a option. IS_SOME x = (?v. x = SOME v)`--),
    GEN_TAC 
    THEN OPTION_CASES_TAC (--`(x :'a option)`--) 
    THEN ASM_SIMP_TAC option_defs_ss []
);


val IS_SOME_IMP_SOME_THE_CANCEL = prove(
(--`!x:'a option. IS_SOME x ==> (SOME (THE x) = x)`--),
    GEN_TAC 
    THEN OPTION_CASES_TAC (--`(x :'a option)`--) 
    THEN ASM_SIMP_TAC option_defs_ss []
);

val option_CASE_ID = prove(
(--`!x:'a option. option_CASE NONE SOME x = x`--),
    GEN_TAC 
    THEN OPTION_CASES_TAC (--`(x :'a option)`--) 
    THEN ASM_SIMP_TAC option_defs_ss []
);

val IS_SOME_option_CASE_SOME = prove(
(--`!x:'a option. IS_SOME x ==> (option_CASE e SOME x = x)`--),
    GEN_TAC 
    THEN OPTION_CASES_TAC (--`(x :'a option)`--) 
    THEN ASM_SIMP_TAC option_defs_ss []
);

val option_CASE_SOME_ID = prove(
(--`!x:'a option. (option_CASE x SOME x = x)`--),
    GEN_TAC 
    THEN OPTION_CASES_TAC (--`(x :'a option)`--) 
    THEN ASM_SIMP_TAC option_defs_ss []
);

val IS_SOME_option_CASE = prove(
(--`!x:'a option. IS_SOME x ==> (option_CASE e (f:'a->'b) x = f (THE x))`--),
    GEN_TAC 
    THEN OPTION_CASES_TAC (--`(x :'a option)`--) 
    THEN ASM_SIMP_TAC option_defs_ss []
);


val IS_NONE_option_CASE = prove(
(--`!x:'a option. IS_NONE x ==> (option_CASE e f x = (e:'b))`--),
    GEN_TAC 
    THEN OPTION_CASES_TAC (--`(x :'a option)`--) 
    THEN ASM_SIMP_TAC option_defs_ss []
);


val option_CLAUSES = save_thm("option_CLAUSES", 
     LIST_CONJ ([SOME_11,THE_DEF,NOT_NONE_SOME,NOT_SOME_NONE]@
                (CONJUNCTS IS_SOME_DEF)@
                [IS_NONE_EQ_NONE,
                 NOT_IS_SOME_EQ_NONE,
                 IS_SOME_IMP_SOME_THE_CANCEL,
                 option_CASE_ID,
                 option_CASE_SOME_ID,
                 IS_NONE_option_CASE,
                 IS_SOME_option_CASE,
                 IS_SOME_option_CASE_SOME]@
                (CONJUNCTS option_CASE_DEF)@
                (CONJUNCTS option_APPLY_DEF)));


close_theory();
export_theory();
