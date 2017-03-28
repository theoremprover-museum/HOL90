signature IndDefLibSig =
sig
 type term
 type fixity
 type thm
 type tactic
 type thm_tactic
 type monoset        (*      monoset = (string * tactic) list       *)


    val new_inductive_definition
	: {name:string, fixity:fixity,patt:term*term list,
	   rules: {hypotheses : term list,side_conditions : term list,
		   conclusion: term} list}
	-> thm * thm * thm
    val RULE_INDUCT_THEN : thm -> thm_tactic -> tactic
	
    val prove_nonschematic_inductive_relations_exist : monoset -> term -> thm

    val prove_monotonicity_hyps : monoset -> thm -> thm
    val prove_inductive_relations_exist : monoset -> term -> thm
    val gen_new_inductive_definition : monoset -> term -> (thm * thm * thm)

    val bool_monoset : monoset
    val MONO_TAC : monoset -> tactic

    val new_simple_inductive_definition : term list -> thm * thm * thm

end;
