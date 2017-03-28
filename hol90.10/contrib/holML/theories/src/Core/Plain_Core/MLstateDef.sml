(* File: MLstateDef.sml *)

(*
   Definintions of types memory, state, pack, etc.  These used to be
   a  part of the mutual recursion defining environments, but they didn't
   need to be.
*)


(* Memory functions *)
(* mem ::= MEM (((addr#val)list) finmap) *)

val mem_Axiom = define_type
    {name= "mem_Axiom", fixities = [Prefix],
     type_spec = `mem = MEM of (((addr#val)list) finmap)`}

val mem_induction_thm =
    save_thm("mem_induction_thm", prove_induction_thm mem_Axiom)
val mem_cases_thm =
    save_thm("mem_cases_thm", prove_cases_thm mem_induction_thm)
val mem_constructors_one_one =
    save_thm("mem_constructors_one_one",
    prove_constructors_one_one mem_Axiom)

val lookupaddr_mem_DEF = new_recursive_definition
    {name = "lookupaddr_mem_DEF", fixity = Prefix,
     rec_axiom = mem_Axiom,
     def = --`lookupaddr_mem (MEM fm) a = finmap_lookup a fm`--}

val MEM_arg_DEF = new_recursive_definition 
    {name = "MEM_arg_DEF", fixity = Prefix, rec_axiom = mem_Axiom,
     def = --`(MEM_arg (MEM fm) = fm)`--};

(* state functions *)

val state_Axiom = define_type{name= "state_Axiom", fixities = [Prefix],
			      type_spec = `state = STATE of mem=>exnameset`};

val state_induction_thm =
    save_thm("state_induction_thm", prove_induction_thm state_Axiom)
val state_cases_thm =
    save_thm("state_cases_thm", prove_cases_thm state_induction_thm)
val state_constructors_one_one =
    save_thm("state_constructors_one_one",
    prove_constructors_one_one state_Axiom)

val STATE_arg1_DEF = new_recursive_definition 
    {name = "STATE_arg1_DEF", fixity = Prefix, rec_axiom = state_Axiom,
     def = --`STATE_arg1 (STATE m ens) = m`--};

val STATE_arg2_DEF = new_recursive_definition 
    {name = "STATE_arg2_DEF", fixity = Prefix, rec_axiom = state_Axiom,
     def = --`STATE_arg2 (STATE m ens) = ens`--};

val lookupaddr_DEF = new_recursive_definition
    {name = "lookupaddr_DEF", fixity = Prefix, rec_axiom = state_Axiom,
     def = (--`lookupaddr_state (STATE m ens) a = lookupaddr_mem m a`--)};

(* new_exname gives the smallest unused exname -- this might be just a
   temporary definition, as I might change the definition of exnameset *)
val new_exname_DEF = new_recursive_definition 
    {name = "new_exname_DEF", fixity = Prefix,
     rec_axiom = exnameset_Axiom,
     def = --`new_exname (EXNAMESET es) = 
              @en. ~(en IN es) /\ 
                    (!en'. less_exname en' en ==> en' IN es)`--};

(* "add_exname exname state" adds the exname into the exception name set of 
   the state *)
val add_exname_DEF = new_recursive_definition
    {name = "add_exname_DEF", fixity = Prefix, rec_axiom = state_Axiom,
     def = --`add_exname exname (STATE m ens) = 
         STATE m (EXNAMESET (exname INSERT (EXNAMESET_arg ens)))`--};

(* the following is a proof that ADDR and ADDR_arg form a bijection between
   the type addr and num *)
local
    val temp = ISPEC (--`\n. b = ADDR n`--) SELECT_AX;
    val temp2 = PURE_REWRITE_RULE [FORALL_IMP_CONV (concl temp)] temp
    val select2 = SPEC (--`b:addr`--) (BETA_RULE (GEN_ALL temp2))
    val foo1 = MP select2 (SPEC (--`b:addr`--) addr_cases_thm)
    val foo2 = PURE_REWRITE_RULE [ADDR_arg_DEF]
	(AP_TERM (--`ADDR_arg`--) foo1)
in
    val addr_arg_bij = TAC_PROOF
	(([], --`bij_inv ADDR ADDR_arg`--),
	 PURE_REWRITE_TAC [bij_inv_DEF] THEN REPEAT CONJ_TAC THENL
	 [REWRITE_TAC [ONE_ONE_DEF, addr_constructors_one_one],
	  REWRITE_TAC [ONTO_DEF, addr_cases_thm],
	  REWRITE_TAC [ADDR_arg_DEF],
	  GEN_TAC THEN ONCE_REWRITE_TAC [foo2] THEN
	  SUBST_OCCS_TAC [([2], foo1)] THEN REFL_TAC])
end


(* new_addr gives the smallest unused address in the domain of the memory *)
val new_addr_DEF = new_recursive_definition
    {name = "new_addr_DEF", fixity = Prefix, rec_axiom = state_Axiom,
     def = --`new_addr (STATE m ens) = next_dom less_addr (MEM_arg m)`--};

(*
val new_ref_DEF =
    new_recursive_definition{name = "new_ref_DEF",
			     fixity = Prefix,
			     rec_axiom = state_Axiom,
			     def = (--`new_ref (STATE m ens) a v = 
      STATE (MEM (next_addr (MEM_arg1 m))
		     (SOMEmemmap a v (MEM_arg2 m))) ens`--)};

val update_ref_DEF =
    new_recursive_definition{name = "update_ref_DEF",
			     fixity = Prefix,
			     rec_axiom = state_Axiom,
			     def = (--`update_ref (STATE m ens) a v = 
     STATE (MEM (MEM_arg1 m) (SOMEmemmap a v (MEM_arg2 m))) ens`--)};
*)

(* We put the smallest first with insert_into_record *)
val insert_into_mem_DEF = new_recursive_definition
    {name = "insert_into_mem_DEF", rec_axiom = mem_Axiom,
     fixity = Prefix,
     def = --`insert_into_mem (MEM f) a v =
                  MEM (finmap_insert less_addr a v f)`--}

val insert_into_state_mem_DEF = new_recursive_definition
    {name = "insert_into_state_mem_DEF", fixity = Prefix,
     rec_axiom = state_Axiom,
     def = --`insert_into_state_mem (STATE m ens) a v = 
	    STATE (insert_into_mem m a v) ens`--};
