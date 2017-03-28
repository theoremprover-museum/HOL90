(* File: MLexconenv.sml *)

 (* the exname used as first arg to constructor EXCONENV is the first
    unused exception name *)

val exconenv_Axiom =
    define_type{name = "exconenv_Axiom",
		fixities = [Prefix],
		type_spec =
		`exconenv = EXCONENV of ((excon#exname)list) finmap`};

val EXCONENV_arg_DEF = new_recursive_definition
    {name = "EXCONENV_arg_DEF", fixity = Prefix, rec_axiom = exconenv_Axiom,
     def = --`EXCONENV_arg (EXCONENV f) = f`--}

val exconenv_induction_thm =
    save_thm("exconenv_induction_thm",prove_induction_thm exconenv_Axiom)
val exconenv_cases_thm =
    save_thm("exconenv_cases_thm",prove_cases_thm exconenv_induction_thm)
val exconenv_constructors_one_one =
    save_thm("exconenv_constructors_one_one",
             prove_constructors_one_one exconenv_Axiom)

val empty_exconenv_DEF = new_definition
("empty_exconenv_DEF", --`empty_exconenv = EXCONENV empty_finmap`--)

val lookupexcon_exconenv_DEF = new_recursive_definition
    {name = "lookupexcon_exconenv_DEF", fixity = Prefix,
     rec_axiom = exconenv_Axiom,
     def = --`lookupexcon_exconenv (EXCONENV fm) ec = finmap_lookup ec fm`--}

val insert_into_exconenv_DEF = new_recursive_definition
    {name = "insert_into_exconenv_DEF", fixity = Prefix,
     rec_axiom = exconenv_Axiom,
     def = --`insert_into_exconenv (EXCONENV fm) excon exname =
	      EXCONENV (finmap_insert less_excon excon exname fm)`--}

(* add_exconenv e1 e2 implements e1 + e2 as defined on pg 17 *)

val add_exconenv_DEF = new_definition
("add_exconenv_DEF",
 --`add_exconenv e1 e2 = 
    EXCONENV (finmap_modify less_excon (EXCONENV_arg e1) (EXCONENV_arg e2))`--)
(* These are needed in the Modules systems. *)

(* gathering the exception constructors from the exception constructor
   environment *)

val excons_from_exconenv_DEF = new_recursive_definition
 {name = "excons_from_exconenv_DEF",
  fixity = Prefix,
  rec_axiom = exconenv_Axiom,
  def = (--`excons_from_exconenv (EXCONENV e) = finmap_dom e`--)};

(* cutting down the exception constructor environment *)

val cut_exconenv_DEF = new_recursive_definition
 {name = "cut_exconenv_DEF",
  fixity = Prefix,
  rec_axiom = exconenv_Axiom,
  def = (--`cut_exconenv (EXCONENV e) excons =
	    EXCONENV (restrict_finmap e excons)`--)};
