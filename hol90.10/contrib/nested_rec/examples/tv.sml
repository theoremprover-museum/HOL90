(* File: tv.sml *)

val _ = new_theory "test2";

val _ = load_library_in_place(find_library "nested_rec");

val _ = add_theory_to_sml "list";

val prod_Axiom =
    prove((--`!f. ?!g. !(x:'a) (y:'b).((g(x,y)):'c) = (f x y)`--),
          GEN_TAC THEN CONV_TAC EXISTS_UNIQUE_CONV THEN
          REPEAT STRIP_TAC THENL
          [(EXISTS_TAC (--`UNCURRY (f:'a -> 'b -> 'c)`--) THEN
            REWRITE_TAC [definition "pair" "UNCURRY_DEF"]),
           (CONV_TAC FUN_EQ_CONV THEN GEN_TAC THEN
            PURE_ONCE_REWRITE_TAC
            [SYM(SPEC_ALL (theorem "pair" "PAIR"))] THEN
            ASM_REWRITE_TAC[])]);



(* Supplied by Brian Graham *)

local
structure C3  : NestedRecTypeInputSig =
    struct
	structure DefTypeInfo = DefTypeInfo
	open DefTypeInfo
	    
	(* test2 ::= terminal2 | nonterminal2 (('a * test2) list)  *)
	    
	val def_type_spec =
	    [{type_name = "test2",
	      constructors =
	      [{name = "terminal2",
		arg_info = []},
	       {name = "nonterminal2",
		arg_info = [type_op{Tyop = "list",
				    Args = [type_op
					    {Tyop = "prod",
					     Args =
					     [existing (==`:'a`==),
					      being_defined "test2"]}]}]}
	       ]}];

	val recursor_thms = [prod_Axiom,list_Axiom]
	val New_Ty_Existence_Thm_Name = "test2_existence_thm"
	val New_Ty_Induct_Thm_Name = "test2_induction_thm"
	val New_Ty_Uniqueness_Thm_Name = "test2_uniqueness_thm"
	val Constructors_Distinct_Thm_Name = "test2_constructors_one_one"
	val Constructors_One_One_Thm_Name = "test2_constructors_distinct"
	val Cases_Thm_Name = "test2_cases"
    end (* struct *)
in
structure test2 = NestedRecTypeFunc (C3)
end
