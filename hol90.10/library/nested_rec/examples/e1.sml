(* File: e1.sml *)
(*
val _ = new_theory "test";

val _ = load_library_in_place(find_library "nested_rec");
*)

(*
   t0 is an example of a simple nesting
   t1 is an example of nesting within nesting of the same type constructor
   t2 is an example of nesting within nesting of the different type
      constructors.
   t3 is an example using the prod type constuctor.  Here you have to
      create your own recursion theorem.
   e0 is an example of a fairly typical nesting, with multiple cases.
      It has irrelevant recursor theorems, num_Axiom and sum_Axiom.
   e1 is the same as e0, but without the irrelevant theorem.
   e2 is an example without any actual nesting at all.
   e3 is an example with polymorphism
*)

(* An example of a simple nesting *)

local
    structure t0 : NestedRecTypeInputSig =
	struct
	    structure DefTypeInfo = DefTypeInfo
	    open DefTypeInfo
		
	    (* "Alist = mkA of Alist list" *)
		
	    val def_type_spec =
		[{type_name = "Alist",
		  constructors =
		  [{name = "mkA",
		    arg_info =
		    [type_op {Tyop = "list",
			      Args = [being_defined "Alist"]}]}]}]
	    val recursor_thms = [theorem "list" "list_Axiom"]
	    val New_Ty_Existence_Thm_Name = "t0_existence"
	    val New_Ty_Induct_Thm_Name = "t0_induct"
	    val New_Ty_Uniqueness_Thm_Name = "t0_unique"
	    val Constructors_Distinct_Thm_Name = "t0_distinct"
	    val Constructors_One_One_Thm_Name = "t0_one_one"
	    val Cases_Thm_Name = "t0_cases"
	end
in
    structure t0_Def = NestedRecTypeFunc (t0)
end;


(* An example of nesting within nesting *)

local
    structure t1 : NestedRecTypeInputSig =
	struct
	    structure DefTypeInfo = DefTypeInfo
	    open DefTypeInfo
		
	    (* Blist := mkB of Blist list list *)
		
	    val def_type_spec =
		[{type_name = "Blist",
		  constructors =
		  [{name = "mkB",
		    arg_info =
		    [type_op {Tyop = "list",
			      Args =
			      [type_op {Tyop = "list",
					Args = [being_defined "Blist"]}]}]}]}]
		
	    val recursor_thms = [theorem "list" "list_Axiom"]
	    val New_Ty_Existence_Thm_Name = "t1_existence"
	    val New_Ty_Induct_Thm_Name = "t1_induct"
	    val New_Ty_Uniqueness_Thm_Name = "t1_unique"
	    val Constructors_Distinct_Thm_Name = "t1_distinct"
	    val Constructors_One_One_Thm_Name = "t1_one_one"
	    val Cases_Thm_Name = "t1_cases"
	end
in
    structure t1_Def = NestedRecTypeFunc (t1)
end;


(* An example of nesting within nesting of the different type constructors. *)
local
    structure t2 : NestedRecTypeInputSig =
	struct
	    structure DefTypeInfo = DefTypeInfo
	    open DefTypeInfo
		
	    (* sAlist := smk of (sAlist list) + (sAlist list) *)
	    val def_type_spec =
		[{type_name = "sAlist",
		  constructors =
		  [{name = "smk",
		    arg_info =
		    [type_op {Tyop = "sum",
			      Args = [type_op {Tyop = "list",
					       Args =
					       [being_defined "sAlist"]},
				      type_op {Tyop = "list",
					       Args =
					       [being_defined "sAlist"]}]}]}]}]
		
	    val recursor_thms = [theorem "list" "list_Axiom",
				 theorem "sum" "sum_Axiom"]
	    val New_Ty_Existence_Thm_Name = "t2_existence"
	    val New_Ty_Induct_Thm_Name = "t2_induct"
	    val New_Ty_Uniqueness_Thm_Name = "t2_unique"
	    val Constructors_Distinct_Thm_Name = "t2_distinct"
	    val Constructors_One_One_Thm_Name = "t2_one_one"
	    val Cases_Thm_Name = "t2_cases"
		
	end
in
    structure t2_Def = NestedRecTypeFunc (t2)
end;


(* An example with prod *)

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


local
    structure t3 : NestedRecTypeInputSig =
	struct
	    structure DefTypeInfo = DefTypeInfo
	    open DefTypeInfo
		
	    (* Aprod := End | pmk of (Aprod # Aprod) *)
		
	    val def_type_spec =
		[{type_name = "Aprod",
		  constructors =
		  [{name = "End", arg_info = []},
		   {name = "pmk",
		    arg_info =
		    [type_op {Tyop = "prod",
			      Args = [being_defined "Aprod",
				      being_defined "Aprod"]}]}]}]
		
	    val recursor_thms = [prod_Axiom]
	    val New_Ty_Existence_Thm_Name = "t3_existence"
	    val New_Ty_Induct_Thm_Name = "t3_induct"
	    val New_Ty_Uniqueness_Thm_Name = "t3_unique"
	    val Constructors_Distinct_Thm_Name = "t3_distinct"
	    val Constructors_One_One_Thm_Name = "t3_one_one"
	    val Cases_Thm_Name = "t3_cases"
	end
in    
    structure t3_Def = NestedRecTypeFunc (t3)
end;


local
    structure t4 : NestedRecTypeInputSig = 
        struct
            structure DefTypeInfo = DefTypeInfo
            open DefTypeInfo
		
            (*
             state = State of (num # value) list
             env = Env of (num # value) list | AltEnv of (num # value) list
             value = Base of 'a | Ind of num env | Ref of (state # value)
             *)
            val def_type_spec = 
                [{type_name = "state",
                  constructors =
                  [{name = "State",
                    arg_info =
                    [type_op {Tyop = "list",
                              Args =
                              [type_op {Tyop = "prod",
                                        Args =
                                        [existing (==`:num`==),
                                         being_defined "value"]}]}]}]},
                 {type_name = "env",
                  constructors =
                  [{name = "Env1",
                    arg_info =
                    [type_op {Tyop = "list",
                              Args =
                              [type_op {Tyop = "prod",
                                        Args =
                                        [existing (==`:num`==),
                                         being_defined "value"]}]}]},
                   {name = "Env2",
                    arg_info =
                    [type_op {Tyop = "list",
                              Args =
                              [type_op {Tyop = "prod",
                                        Args =
                                        [existing (==`:num`==),
                                         being_defined "value"]}]}]}]},
                 {type_name = "value",
                  constructors =
                  [{name = "Base", arg_info = [existing (==`:'a`==)]},
                   {name = "Ind", arg_info = [being_defined "env"]},
                   {name = "Ref",
                    arg_info =
                    [type_op {Tyop = "prod",
                              Args =
                              [being_defined "state",
                               being_defined "value"]}]}]}]
            val recursor_thms = [theorem "list" "list_Axiom",prod_Axiom]
	    val New_Ty_Existence_Thm_Name = "t4_existence"
	    val New_Ty_Induct_Thm_Name = "t4_induct"
	    val New_Ty_Uniqueness_Thm_Name = "t4_unique"
	    val Constructors_Distinct_Thm_Name = "t4_distinct"
	    val Constructors_One_One_Thm_Name = "t4_one_one"
	    val Cases_Thm_Name = "t4_cases"
        end
in
    structure t4_Def = NestedRecTypeFunc (t4)
end;



(* An example of irrelevant recursor theorems *)

local
    structure e0 : NestedRecTypeInputSig = 
        struct
            structure DefTypeInfo = DefTypeInfo
            open DefTypeInfo
                
            (* "BBlist = mkBB of BBlist list | mkBB1 of num" *)
                
            val def_type_spec =
                [{type_name = "BBlist",
                  constructors =
                  [(* {name = "mkBB",
                    arg_info =
                    [type_op {Tyop = "list",
                    Args = [being_defined "BBlist"]}]},*)
                   {name = "mkBB1",
                    arg_info = [existing (==`:num`==)]}]}]
            val recursor_thms = [theorem "list" "list_Axiom",
                                 theorem "prim_rec" "num_Axiom",
                                 theorem "sum" "sum_Axiom"]
	    val New_Ty_Existence_Thm_Name = "e0_existence"
	    val New_Ty_Induct_Thm_Name = "e0_induct"
	    val New_Ty_Uniqueness_Thm_Name = "e0_unique"
	    val Constructors_Distinct_Thm_Name = "e0_distinct"
	    val Constructors_One_One_Thm_Name = "e0_one_one"
	    val Cases_Thm_Name = "e0_cases"
        end
in
    structure e0_Def = NestedRecTypeFunc (e0)
end;

(* e0 with the irrelevant theorems removed *)

local
    structure e1 : NestedRecTypeInputSig = 
        struct
            structure DefTypeInfo = DefTypeInfo
            open DefTypeInfo
                
            (* "BClist = mkBC of BClist list | mkBC1 of num" *)
                
            val def_type_spec =
                [{type_name = "BClist",
                  constructors =
                  [(* {name = "mkBC",
                    arg_info =
                    [type_op {Tyop = "list",
                    Args = [being_defined "BClist"]}]},*)
                   {name = "mkBC1",
                    arg_info = [existing (==`:num`==)]}]}]
            val recursor_thms = [theorem "list" "list_Axiom"]
	    val New_Ty_Existence_Thm_Name = "e1_existence"
	    val New_Ty_Induct_Thm_Name = "e1_induct"
	    val New_Ty_Uniqueness_Thm_Name = "e1_unique"
	    val Constructors_Distinct_Thm_Name = "e1_distinct"
	    val Constructors_One_One_Thm_Name = "e1_one_one"
	    val Cases_Thm_Name = "e1_cases"
        end
in
    structure e1_Def = NestedRecTypeFunc (e1)
end;


(* An example with no actual nesting *)

local
    structure e2 : NestedRecTypeInputSig = 
        struct
	    structure DefTypeInfo = DefTypeInfo
	    open DefTypeInfo
		
	    (* "AB = mkAB1 of num" *)
		
	    val def_type_spec =
		[{type_name = "AB",
		  constructors =
		  [{name = "mkAB1",
		    arg_info = [existing (==`:num`==)]}]}]
	    val recursor_thms = []
	    val New_Ty_Existence_Thm_Name = "e2_existence"
	    val New_Ty_Induct_Thm_Name = "e2_induct"
	    val New_Ty_Uniqueness_Thm_Name = "e2_unique"
	    val Constructors_Distinct_Thm_Name = "e2_distinct"
	    val Constructors_One_One_Thm_Name = "e2_one_one"
	    val Cases_Thm_Name = "e2_cases"
        end
in
    structure e2 = NestedRecTypeFunc (e2)
end;

(* An exapmle with polymorphism *)
    
local
    structure e3 : NestedRecTypeInputSig = 
        struct
            structure DefTypeInfo = DefTypeInfo
            open DefTypeInfo
                
            (* "CClist = mkCC of CClist list | mkCC1 of 'a" *)
                
            val def_type_spec =
                [{type_name = "CClist",
                  constructors =
                  [{name = "mkCC",
                    arg_info =
                    [type_op {Tyop = "list",
                              Args = [being_defined "CClist"]}]},
                   {name = "mkCC1",
                    arg_info = [existing (==`:'a`==)]}]}]
            val recursor_thms = [theorem "list" "list_Axiom"]
	    val New_Ty_Existence_Thm_Name = "e3_existence"
	    val New_Ty_Induct_Thm_Name = "e3_induct"
	    val New_Ty_Uniqueness_Thm_Name = "e3_unique"
	    val Constructors_Distinct_Thm_Name = "e3_distinct"
	    val Constructors_One_One_Thm_Name = "e3_one_one"
	    val Cases_Thm_Name = "e3_cases"
        end
in
    structure e3 = NestedRecTypeFunc (e3)
end;

