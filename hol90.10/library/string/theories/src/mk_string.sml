(* =====================================================================*)
(* FILE		: mk_string.ml						*)
(* DESCRIPTION  : Creates the theory `string.th`.			*)
(*									*)
(* PARENTS	: ascii.th						*)
(* WRITES FILES	: string.th						*)
(*									*)
(* AUTHOR	: (c) T. Melham 1988					*)
(* DATE		: 87.07.27						*)
(* REVISED	: 90.10.27						*)
(* TRANSLATED   : Konrad Slind, University of Calgary                   *)
(* =====================================================================*)

(* ---------------------------------------------------------------------*)
(* Create the new theory						*)
(* ---------------------------------------------------------------------*)
new_theory "string";

(* ---------------------------------------------------------------------*)
(* Parent theories							*)
(* ---------------------------------------------------------------------*)
if Lib.mem "ascii" (Theory.ancestry "string") then ()
else new_parent "ascii";

(* ---------------------------------------------------------------------*)
(* define the type :string						*)
(* ---------------------------------------------------------------------*)
val string_Axiom = define_type{name="string_Axiom",
                         type_spec=`string = ""
                                           | STRING of ascii => string`,
                         fixities = [Prefix,Prefix]};

Globals.assert_strings_defined();

(* ---------------------------------------------------------------------*)
(* Make tok an abbreviation for string, for compatibility with old code *)
(* ---------------------------------------------------------------------*)
(* new_type_abbrev("tok", ==`:string`==); *)

(* ---------------------------------------------------------------------*)
(* prove "induction" theorem for :string.				*)
(* ---------------------------------------------------------------------*)
val string_Induct = 
   save_thm ("string_Induct",prove_induction_thm string_Axiom);

(* ---------------------------------------------------------------------*)
(* prove cases theorem for :string.					*)
(* ---------------------------------------------------------------------*)
val string_CASES = 
    save_thm ("string_CASES", prove_cases_thm string_Induct);

(* ---------------------------------------------------------------------*)
(* prove that the constructor STRING is one-to-one			*)
(* ---------------------------------------------------------------------*)
val STRING_11 = 
    save_thm ("STRING_11", prove_constructors_one_one string_Axiom);

(* ---------------------------------------------------------------------*)
(* prove that the constructors empty_string and STRING are distinct	*)
(* ---------------------------------------------------------------------*)
val NOT_STRING_EMPTY = 
    save_thm ("NOT_STRING_EMPTY", prove_constructors_distinct string_Axiom);

close_theory();

export_theory();
