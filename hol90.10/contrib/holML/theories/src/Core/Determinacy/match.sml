(* the theorem that I would like to prove: *)

(* INVERSION doesn't seem to be quite the thing to do

(* rules_sat is a theorem whose conclusion has the form:
   (!<vars>. <some hypothesis> ==> rel_k1 <some terms involving vars>) /\
   (!<vars>. <some hypothesis> ==> rel_k2 <some terms involving vars>) /\
	...
   (!<vars>. <some hypothesis> ==> rel_k3 <some terms involving vars>)
   where each conjunct specifies one of the rules that the relations
   (the rel_k1 ... are among the relations defined by the rules)
   satisfies *)

fun mk_invert_goal rules_sat =

let val conjuncts = strip_conj (concl rules_sat)
    val stripped_conjs = map strip_forall conjuncts
    val filtered_conjs = filter (fn x => is_imp (snd x)) stripped_conjs
    fun convert_conj (parameters, implication) =
	let val {ant, conseq} = dest_imp implication
	in
	    list_mk_forall (parameters,
			    mk_imp {ant = conseq, conseq = ant})
	end
in
    list_mk_conj (map convert_conj filtered_conjs)
end

val invert_goal = mk_invert_goal
    (REWRITE_RULE [definition "holML_Plain_Core" "eval_exbind_pred_DEF"]
     EVAL_EXBIND_RULES_SATISFIED)

end of INVERSION *)

(* OK, let's try for something not quite so impressive -- let's try
   defining the goal of the match_theorem, which says, that if rel_k
   holds of some args, then what the forms of those args can be, and what
   other conditions it has to satisfy *)

fun make_match_terms rules_sat = 

let

fun member item (thing::more_things) = 
    if item = thing then true else member item more_things
  | member item [] = false

fun test_list test (thing::more_things) =
    if test thing then true else test_list test more_things
  | test_list test [] = false

fun join (a::a_s) (b::b_s) = (a, b)::(join a_s b_s)
  | join [] [] = []
  | join _ _ = raise HOL_ERR
    {message = "lists of different length", origin_function = "join",
     origin_structure = "make_match_terms"}

fun replace old_item new_item (item::items) =
    if item = old_item then new_item::(replace old_item new_item items)
    else item::(replace old_item new_item items)
  | replace old_item new_item [] = []

fun remove item (hd_item::more_items) =
    if hd_item = item then (remove item more_items)
    else hd_item::(remove item more_items)
  | remove item [] = []

fun elim_duplicates (item::rest) = 
    let val undup = elim_duplicates rest
    in
	if member item undup then undup
	else item::undup
    end
  | elim_duplicates [] = []

fun bad_error () = raise HOL_ERR
    {message = "this case should never happen, real problem here!",
     origin_function = "anything...",
     origin_structure = "make_match_terms"}

(* if neither A_list nor B_list have any duplicates, but possibly
   A_list and B_list have some common elements, then the result will 
   be a list with no common elements *)
fun append_no_dup (A_list, B_list) =
    let fun helper (A::As) B_list As_to_add =
	    if member A B_list then helper As B_list As_to_add
	    else helper As B_list (A::As_to_add)
	  | helper [] B_list As_to_add = (rev As_to_add)@B_list
    in
	helper A_list B_list []
    end

fun break_down_rule rule_term =
    let val (parameters, term1) = strip_forall rule_term
	val term_is_imp = is_imp term1
	val hypo_data = if term_is_imp then SOME (#ant (dest_imp term1))
			else NONE
	val applied_reltn = if term_is_imp then #conseq (dest_imp term1)
			    else term1
	val (rel, rel_args) = strip_comb applied_reltn
    in
	{params = parameters, hypo_data = hypo_data,
	 rel = rel, rel_args = rel_args}
    end

val rule_data = map break_down_rule (strip_conj (concl rules_sat))

val the_relations = elim_duplicates (map #rel rule_data)

val divided_rule_data = map
    (fn rel => (filter (fn x => #rel x = rel) rule_data)) the_relations

type rule_type = {params:term list, hypo_data:term option, 
		  rel:term, rel_args:term list}

(* there are no bound vars in the conclusion and all free vars in the
   conclusion are in the params, so all the vars are essentially
   params@(all_vars hyp) *)
fun get_vars_in_rule (rule_data:rule_type) =
    case (#hypo_data rule_data) of
	SOME tm => append_no_dup ((#params rule_data), (all_vars tm))
      | NONE => (#params rule_data)

(* if ftn_type is a1_ty -> a2_ty ->  ... -> an_ty, this function returns
   the "argument" types, [a1_ty, a2_ty, ... a(n-1)_ty] *)
fun get_arg_types ftn_type =
    let fun helper the_type arg_types =
	let val {Tyop = tyop, Args = args} = dest_type the_type
	in
	    if (tyop = "fun") andalso (args <> []) then
		helper (nth (args, 1)) ((hd args)::arg_types)
	    else
		rev arg_types
	end
    in helper ftn_type []
    end

(* make up variable names for all the arguments of the relations *)
fun make_vars_for_reltn rules_list =
    let val reltn = (#rel (hd rules_list))
	val vars_in_rule = 
	    fold append_no_dup (map get_vars_in_rule rules_list) []
	val arg_types = get_arg_types (type_of reltn)
	fun at_most_3 str = substring (str, 0, min (size str, 3))
	fun mk_var_name arg_ty = mk_var
	    {Name = at_most_3 (#Tyop (dest_type arg_ty)),
	     Ty = arg_ty}
	val potential_vars = map mk_var_name arg_types
	fun helper (pot_name::names) good_names vars_to_avoid =
	    let val name = variant vars_to_avoid pot_name
	    in
		helper names (name::good_names) (name::vars_to_avoid)
	    end
	  | helper [] good_names _ = rev good_names
    in
	helper potential_vars [] vars_in_rule
    end    

val vars_for_resulting_thm =
    map make_vars_for_reltn divided_rule_data

fun get_hyp_vars (SOME tm) = all_vars tm
  | get_hyp_vars NONE = []

(* the following function expects the rule to have type rule_type
   The original rule looked like:  !<params>. hypo_data ==> rel <rel_args>
   forall_vars is the list of variables that all the match terms will be
   quantified over *)

fun make_disj_for_rule forall_vars (rule:rule_type) =
    let val {params = params, rel_args = rel_args, hypo_data = hyp_data,
	     rel = rel} = rule
	(* rename vars in the rule to be what the forall_vars are *)
	fun rename_vars var_num (forall_var::more_vars) all_rel_args
	                params hyp_data =
	    let val this_arg = nth (all_rel_args, var_num)
	    in
		if (is_var this_arg) andalso (forall_var <> this_arg) then
		    let val new_params = remove this_arg params
			val sub_info = [{redex = this_arg,
					 residue = forall_var}]
			val new_rel_args = map
			    (fn tm => subst sub_info tm) all_rel_args
			val new_hyp_data =
			    case hyp_data of 
				SOME tm => SOME (subst sub_info tm)
			      | NONE => NONE
		    in
			rename_vars (var_num + 1) more_vars new_rel_args
			new_params new_hyp_data
		    end
		else if (is_var this_arg) andalso
		    (forall_var = this_arg) then
		    rename_vars (var_num + 1) more_vars all_rel_args
		    (remove this_arg params) hyp_data 
	        else
		    rename_vars (var_num + 1) more_vars all_rel_args
		    params hyp_data 
	    end
	  | rename_vars var_num [] all_rel_args params hyp_data =
	    (all_rel_args, params, hyp_data)
	val (rel_args, params, hyp_data) = rename_vars 0 forall_vars
	    rel_args params hyp_data
        (* now to make the disjunct associated with this rule --
	   following function returns the conjs as a list *)
	fun mk_match_conjs (forall_var::more_vars) (rel_arg::more_args)
	    conj_list =
	    if (forall_var = rel_arg) then
		mk_match_conjs more_vars more_args conj_list
	    else
		mk_match_conjs more_vars more_args 
		(mk_eq {lhs = forall_var, rhs = rel_arg}::conj_list)
	  | mk_match_conjs [] [] conj_list = rev conj_list
	  | mk_match_conjs _ _ _ = bad_error ()
	val conj_list = mk_match_conjs forall_vars rel_args []
        (* now add to this the hypothesis *)
	val conj_list = 
	    case hyp_data of 
		SOME tm => conj_list@(strip_conj tm)
	      | NONE => conj_list
        (* now make the list into a conjunction *)
	val conjs = list_mk_conj conj_list
        (* now we only need quantify over the rest of the parameters
	   (the variables that are free in the relation args) and we're 
	   done *)
    in
	list_mk_exists (params, conjs)
    end

fun mk_match_for_reltn reltn forall_vars rule_data =
    let fun make_big_disj (rule::[]) =
	    make_disj_for_rule forall_vars rule
	  | make_big_disj (rule::rules) = 
	    mk_disj {disj1 = make_disj_for_rule forall_vars rule,
		     disj2 = make_big_disj rules}
	  | make_big_disj [] = bad_error ()
	val big_disj = make_big_disj rule_data
	(* need to make variable for match relation *)
	val {Name = rel_name, Ty = rel_ty} = dest_const reltn
	val rel_match_var = 
	    mk_var {Name = rel_name ^ "_match", Ty = rel_ty}
	val applied_reltn = list_mk_comb (rel_match_var, forall_vars)
	val eq_tm = mk_eq {lhs = applied_reltn, rhs = big_disj}
    in
	list_mk_forall (forall_vars, eq_tm)
    end

fun mk_match_term_list (reltn::more_relations)
    (vars_for_this_reltn::more_vars) (rules_for_this_reltn::more_rules) =
    (mk_match_for_reltn reltn vars_for_this_reltn rules_for_this_reltn)::
    mk_match_term_list more_relations more_vars more_rules
  | mk_match_term_list [] [] [] = []
  | mk_match_term_list _ _ _ = bad_error ()

in

mk_match_term_list the_relations vars_for_resulting_thm divided_rule_data

end
