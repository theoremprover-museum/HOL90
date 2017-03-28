(* I presume we've just read in exbind_det.sml, since I'll be using 
   functions from there *)

local 
    val rules_sat = (* pat_rules_satisfied for now *)
	REWRITE_RULE [eval_pat_pred_DEF]
	EVAL_PAT_RULES_SATISFIED
    val match_term_list = make_match_terms rules_sat
    val conjs = CONJUNCTS rules_sat
    fun not_imp thm1 = not (is_imp (snd (strip_forall (concl thm1))))
    fun is_an_imp thm1 = is_imp (snd (strip_forall (concl thm1)))
    val non_imps = filter not_imp conjs
    val imps = filter is_an_imp conjs
in
    val accept_pat_axiom = MAP_FIRST MATCH_ACCEPT_TAC non_imps
    val speced_pat_imps = map SPEC_ALL imps
    val eval_atpat_match_DEF =
	new_definition ("eval_atpat_match_DEF", nth (match_term_list, 0))
    val eval_patrow_match_DEF =
	new_definition ("eval_patrow_match_DEF", nth (match_term_list, 1))
    val eval_pat_match_DEF =
	new_definition ("eval_pat_match_DEF", nth (match_term_list, 2))
end

val atpat_eval_ind = TAC_PROOF (([],
--`!atpat_prop patrow_prop pat_prop.
    eval_pat_pred atpat_prop patrow_prop pat_prop ==>
    (!ap s1 e v s2 vef. eval_atpat ap s1 e v s2 vef ==>
                        atpat_prop ap s1 e v s2 vef)`--),
(PURE_ONCE_REWRITE_TAC [eval_atpat_DEF]) THEN
(REPEAT GEN_TAC) THEN (DISCH_TAC) THEN (REPEAT GEN_TAC) THEN
(DISCH_THEN IMP_RES_TAC));

val patrow_eval_ind = TAC_PROOF (([],
--`!atpat_prop patrow_prop pat_prop.
    eval_pat_pred atpat_prop patrow_prop pat_prop ==>
    (!pr s1 e r s2 vef. eval_patrow pr s1 e r s2 vef ==>
                        patrow_prop pr s1 e r s2 vef)`--),
(PURE_ONCE_REWRITE_TAC [eval_patrow_DEF]) THEN
(REPEAT GEN_TAC) THEN (DISCH_TAC) THEN (REPEAT GEN_TAC) THEN
(DISCH_THEN IMP_RES_TAC));

val pat_eval_ind = TAC_PROOF (([],
--`!atpat_prop patrow_prop pat_prop.
    eval_pat_pred atpat_prop patrow_prop pat_prop ==>
    (!p s1 e v s2 vef. eval_pat p s1 e v s2 vef ==>
                       pat_prop p s1 e v s2 vef)`--),
(PURE_ONCE_REWRITE_TAC [eval_pat_DEF]) THEN
(REPEAT GEN_TAC) THEN (DISCH_TAC) THEN (REPEAT GEN_TAC) THEN
(DISCH_THEN IMP_RES_TAC));

val sym_pat_distinct = PURE_ONCE_REWRITE_RULE [EQ_SYM_EQ] pat_distinct

val sym_varenv_fail_constructors_distinct =
    PURE_ONCE_REWRITE_RULE [EQ_SYM_EQ] varenv_fail_constructors_distinct

fun match_term_op pat_tm tm =
    SOME (match_term pat_tm tm) handle e => NONE
fun find_match_op pat_tm tm =
    SOME (find_match {pattern = pat_tm, term = tm}) handle e => NONE

local
    val thm1 = REWRITE_RULE [] (DISJ_IMP (ASSUME (--`~A \/ B`--)))
    val thm2 = IMP_ELIM (ASSUME (--`A ==> B`--))
in
    val imp_thm = 
	TAC_PROOF (([], --`!A B. (A ==> B) = (~A \/ B)`--),
		   REPEAT GEN_TAC THEN EQ_TAC THEN DISCH_TAC THENL
		   [REWRITE_TAC [thm2], REWRITE_TAC [thm1]])
end

val convert_thm = TAC_PROOF
(([], --`!A B C. ((A ==> C) /\ (B ==> C)) = ((A \/ B) ==> C)`--),
 REPEAT GEN_TAC THEN REWRITE_TAC [imp_thm, DE_MORGAN_THM, RIGHT_OR_OVER_AND])

fun bad_error () = raise HOL_ERR
    {message = "this case should never happen, real problem here!",
     origin_function = "anything...",
     origin_structure = "pat_det"}

fun match_pat_imps gl =
    let fun mk_matched_thm thm1 =
	case match_term_op (#conseq(dest_imp (concl thm1))) gl of
	    SOME (term_substitution,type_substitution) =>
		SOME (STRONG_INST_TY_TERM
		      {term_substitution=term_substitution,
		       type_substitution=type_substitution,
		       theorem=thm1})
          | NONE => NONE
	fun put_together [] = bad_error ()
	  | put_together (thm1::nil) = thm1
	  | put_together (thm1::more) = 
		REWRITE_RULE [convert_thm] (CONJ thm1 (put_together more))
	val thm_ops = map mk_matched_thm speced_pat_imps
	val filtered_list = filter (fn NONE => false | SOME x => true) thm_ops
	val matching_thms = map (fn SOME x => x) filtered_list
	val imp_thm = put_together matching_thms
    in
	imp_thm
    end

fun match_pat_imps_tac (asms, gl) =
    MATCH_MP_TAC (match_pat_imps gl) (asms, gl)

fun test_list test (thing::more_things) =
    if test thing then true else test_list test more_things
  | test_list test [] = false;

local 
    val [distinct1, distinct3, distinct2] = CONJ_LIST 3 pat_distinct
    val [sdistinct1, sdistinct3, sdistinct2] = CONJ_LIST 3 sym_pat_distinct
    val [one1, one3, one2] = CONJ_LIST 3 pat_one_one
    val info_list =
	[(--`eval_atpat_match`--, 
	  (eval_atpat_match_DEF,
	   [distinct1, sdistinct1, varenv_fail_constructors_distinct,
	    sym_varenv_fail_constructors_distinct,
	    varenv_fail_constructors_one_one, one1])),
	 (--`eval_patrow_match`--, 
	  (eval_patrow_match_DEF,
	   [distinct2, sdistinct2, varenv_fail_constructors_distinct,
	    sym_varenv_fail_constructors_distinct,
	    varenv_fail_constructors_one_one, one2])),
	 (--`eval_pat_match`--, 
	  (eval_pat_match_DEF,
	   [distinct3, sdistinct3, varenv_fail_constructors_distinct,
	    sym_varenv_fail_constructors_distinct,
	    varenv_fail_constructors_one_one, one3]))]
in
    (* this returns the match definition as well as the theorems needed
       to eliminate disjunctions and simplify the term resulting from
       rewriting with the definition *)
    fun get_info tm =
	snd (Lib.first (fn pr => fst pr = tm) info_list)
end;

fun in_list item (item2::more_items) =
    if item = item2 then
	true
    else
	in_list item more_items
  | in_list item [] = false

fun append_no_dup A_list B_list =
    let fun helper (A::As) B_list As_to_add =
            if in_list A B_list then helper As B_list As_to_add
            else helper As B_list (A::As_to_add)
          | helper [] B_list As_to_add = (rev As_to_add)@B_list
    in
        helper A_list B_list []
    end

fun collect_vars terms = fold 
    (fn (tm, vars) => append_no_dup (free_vars tm) vars) terms []

(* This function is a kludge. The problem is that when I do SPECL in 
   rewrite_match below, variable names that clash with the free vars
   of the terms I'm specializing to are renamed to avvoid clashing with 
   the term, but not to avoid clashing with bound variables! So I will
   rename variables that clash before doing SPECL. This function returns
   the thm with renamed vars. *)
fun avoid_clash thm1 vars =
    let fun lookup_change var ((pr as (old_var, new_var))::more_pairs) =
	    if var = old_var then 
		SOME pr 
	    else 
		lookup_change var more_pairs
	  | lookup_change var [] = NONE
	fun change_it term change_list vars_to_avoid =
	    if is_comb term then 
		let val {Rator = rator, Rand = rand} = dest_comb term in
		    mk_comb {Rator = change_it rator change_list vars_to_avoid,
			     Rand = change_it rand change_list vars_to_avoid}
		end
	    else if is_var term then
		case lookup_change term change_list of
		    SOME (old_var, new_var) => new_var
                  | NONE => term
	    else if is_const term then term
	    else (* the only choice is an astraction *)
		let val {Bvar = bvar, Body = body} = dest_abs term in
		    if not (in_list bvar vars_to_avoid) then
			mk_abs {Bvar = bvar, 
				Body = change_it body change_list
			        vars_to_avoid}
		    else
			let val total_vars = (all_vars body)@vars_to_avoid
			    val new_bvar = variant total_vars bvar 
			in
			    mk_abs {Bvar = new_bvar,
				    Body = change_it body
				    ((bvar, new_bvar)::change_list)
				    (new_bvar::vars_to_avoid)}
			end
		end
	val new_concl = change_it (concl thm1) [] vars
    in
	TAC_PROOF (([], new_concl), REWRITE_TAC [thm1])
    end

fun is_subterm subt tm =
    if (is_var tm) orelse (is_const tm) then
	subt = tm
    else if is_abs tm then
	let val {Bvar = bvar, Body = body} = dest_abs tm in
	    (bvar = subt) orelse (subt = body) orelse
	    (is_subterm subt body)
	end
    else (* must be combination *)
	let val {Rator = rator, Rand = rand} = dest_comb tm in
	    (subt = rator) orelse (subt = rand) orelse
	    (is_subterm subt rator) orelse (is_subterm subt rand) 
	end

fun select_the_var old_var ({redex = rx, residue = rs}::more) =
    if rx = old_var then rs 
    else select_the_var old_var more
  (* if no sub for this var, then this var doesn't change *)
  | select_the_var old_var [] = old_var
fun refl old_var (arg1::more_args1) (arg2::more_args2) =
    if (is_subterm old_var arg1) then
	select_the_var old_var (fst (match_term arg1 arg2))
    else
	refl old_var more_args1 more_args2
  | refl old_var _ _ = bad_error ()
    
val break_conjs = REPEAT CONJ_TAC THEN TRY
    (FIRST_ASSUM ACCEPT_TAC ORELSE REFL_TAC);

val eval_rel_list = 
    [--`eval_exbind`--, --`eval_atpat`--, --`eval_patrow`--, --`eval_pat`--,
     --`eval_atexp`--, --`eval_exprow`--, --`eval_exp`--, --`eval_dec`--,
     --`eval_valbind`--, --`eval_match`--, --`eval_mrule`--]

(* This is a complicated function. It tries to figure out how to intantiate
   existential variables. The idea is this: we expect the goal to have the 
   form:   ?exists_vars. T1 /\ T2 /\ ... /\ TN
   Now, these conjuncts are going to tell us how to instantiate the 
   variables. Let tm2 be a term continaing a variable we want to 
   instantiate. It will either be 
            ftn <args1> = ftn <args2>
   (in which case we match up the args to find the proper variable to
   instantiate to) or
            eval_*** args      or     some-other-form.
   If some-other-form, then we match it aginst the assumptions to find
   what to instantiate the variable (we do this by matching them and
   extracting the result from the substitution list). This is done by
   match_asms2. Now if the form is eval_*** args, then we also match
   against the assumptions to find the right way to instantiate, but
   there are catches. One is that more than one of the assumptions may
   match. We solve this problem by making sure that the first arg in the
   assumption is the same as the first arg in the goal (by the time we do
   this function, these args are instantiated to the correct things).
   This is done by function eval_rel_match_asms. Now there's still one
   more possibility, and that is that thru' the rewriting by the
   assumptions, the goal has gotten more specialized than the
   assumptions. In this case, we match them, using the assumption as the
   pattern and the goal as the term, and if there is a match we reverse
   the substitution list and then grab the result. If none of this works
   then we just fail. *)
fun do_exists2 (asms, gl) =
    let val (exists_vars, tm) = strip_exists gl
	val conjs = strip_conj tm
	fun switch {redex = rx, residue = rs} = {redex = rs, residue = rx}
	(* now we assume that tm2, the term in the goal, is more
	   specialized than the corresponding term in the asms,
	   we try to match them that way *)
	fun one_final_attempt old_var tm2 (assum::more_asms) =
	    (case match_term_op assum tm2 of
		 SOME (sub_list, _) => 
		     select_the_var old_var (map switch sub_list)
	       | NONE => one_final_attempt old_var tm2 more_asms)
	  (* give up *)
	  | one_final_attempt old_var tm2 [] = bad_error ()
	(* if we're trying to match against an eval_*** term, then make
           sure the first arg is the same *)
	fun eval_rel_match_asms old_var rel arg1 tm2 (assum::more_asms) =
	    if is_comb assum then
		let val (ftn, arg2::more_args) = strip_comb assum
		in
		    if (rel = ftn) andalso (arg1 = arg2) then
			(case match_term_op tm2 assum of
			     SOME (sub_list, _) => 
				 select_the_var old_var sub_list
			   | NONE => eval_rel_match_asms old_var rel arg1 
				 tm2 more_asms)
		    else eval_rel_match_asms old_var rel arg1 tm2 more_asms
		end
	    else eval_rel_match_asms old_var rel arg1 tm2 more_asms
	  | eval_rel_match_asms old_var rel arg1 tm2 [] = 
	    one_final_attempt old_var tm2 asms
	(* just match and don't worry about particular args *)
	fun match_asms2 old_var tm2 (assum::more_asms) =
	    (case match_term_op tm2 assum of
		 SOME (sub_list, _) => select_the_var old_var sub_list
	       | NONE => match_asms2 old_var tm2 more_asms)
	  | match_asms2 old_var tm2 []  = one_final_attempt old_var tm2 asms
	fun match_asms old_var tm2 =
	    let val (ftn, arg1::more_args) = strip_comb tm2
	    in
		if in_list ftn eval_rel_list then
		    eval_rel_match_asms old_var ftn arg1 tm2 asms
		else
		    match_asms2 old_var tm2 asms
	    end
	fun try_refl old_var tm2 = 
	    let val {lhs = left, rhs = right} = dest_eq tm2
		val (term1, term2) = 
		    if (is_subterm old_var left) then (left, right)
		    else (right, left)
		val (ftn1, args1) = strip_comb term1
		val (ftn2, args2) = strip_comb term2
	    in
		if ftn1 = ftn2 then refl old_var args1 args2
		else if (args1 = []) andalso (args2 = []) then ftn2
		else match_asms old_var tm2
	    end
	fun get_new_var old_var =
	    let val tm2 = Lib.first (fn tm => is_subterm old_var tm) conjs
	    in (* have to decide if it's a refl-type or something we have
		   to match again the assumptions *)
		if is_eq tm2 then
		    try_refl old_var tm2
		else match_asms old_var tm2
	    end
	val new_vars = map get_new_var exists_vars
    in
	exists_list new_vars (asms, gl)
    end;

(* look thru conjs under existential, if we find
   var = exists_var, instanitate exists_var to var
   ow, check to see if it's hidden under some args,
   ow, instantiate it to itself *)
fun new_do_exists (asms, gl) =
    let val (exists_vars, tm) = strip_exists gl
	val conjs = strip_conj tm
	fun try_matching (conj::more_conjs) old_var =
	    if (is_eq conj) andalso (is_comb (rhs conj)) andalso
		(is_subterm old_var (rhs conj)) then
		let val {lhs = left, rhs = right} = dest_eq conj
		    val (ftn1, args1) = strip_comb right
		    val (ftn2, args2) = strip_comb left
		in
		    if ftn1 = ftn2 then refl old_var args1 args2
		    else (* just instantiate var to itself *) old_var
		end
	    else try_matching more_conjs old_var
	  | try_matching [] old_var = old_var (* give up & instantiate *)
	fun get_new_var (conj::more_conjs) old_var =
	    if (is_eq conj) andalso (rhs conj = old_var) andalso
		(is_var (lhs conj)) then lhs conj
	    else get_new_var more_conjs old_var
	  | get_new_var [] old_var = try_matching conjs old_var
	val new_vars = map (get_new_var conjs) exists_vars
    in
	exists_list new_vars (asms, gl)
    end

(* the only case that ought to be left after this is a goal that
   is over_specialized, need to find the assumption that matches
   it and rewrite the assumption *)
fun last_ditch (asms, gl) =
    let fun help_tac (assum::more_assums) =
	    (case find_match_op assum gl of
		 SOME _ => 
		     let val new_asms = filter (fn a => a <> assum) asms
			 val asm_thms = map ASSUME new_asms
			 val maybe_goal = REWRITE_RULE asm_thms (ASSUME assum)
		     in
			 if gl = concl maybe_goal then
			     (ACCEPT_TAC maybe_goal)
			 else
			     help_tac more_assums
		     end
               | NONE => help_tac more_assums)
         | help_tac [] = FAIL_TAC "doesn't match"
    in
	(help_tac asms) (asms, gl)
    end
		    
fun simple_solve (asms, gl) =
    if is_exists gl then 
	(do_exists2 THEN break_conjs THEN last_ditch) (asms, gl)
    else (* must be eval_.... *)
	(FIRST_ASSUM ACCEPT_TAC ORELSE last_ditch) (asms, gl)

fun choice_tac (asms, gl) =
    if is_disj gl then 
       ((DISJ1_TAC THEN simple_solve) ORELSE 
	(DISJ2_TAC THEN choice_tac)) (asms, gl)
    else simple_solve (asms, gl)

fun pat_helper_tac (asms, gl) =
    let val imp_thm = match_pat_imps gl
    in
	if is_disj (#ant (dest_imp (concl imp_thm))) then
	    (MATCH_MP_TAC imp_thm THEN choice_tac) (asms, gl)
	else
	    (MATCH_MP_TAC imp_thm THEN break_conjs THEN 
	     simple_solve) (asms, gl)
    end

fun pat_solve_it (asms, gl) = 
    if is_exists gl then 
	(new_do_exists THEN break_conjs THEN pat_solve_it) (asms, gl)
    else (* must be eval_.... *)
	(PURE_ASM_REWRITE_TAC [] THEN
	 (accept_pat_axiom ORELSE pat_helper_tac))
	(asms, gl);

fun match_tms_in_term match_list tm list_so_far =
    if is_var tm then list_so_far
    else if is_const tm then
	if in_list tm match_list then
	    if in_list tm list_so_far then list_so_far
	    else tm::list_so_far
	else list_so_far
    else if is_abs tm then match_tms_in_term match_list
	(body tm) list_so_far
    else 
	let val new_list = match_tms_in_term match_list 
	    (rator tm) list_so_far
	in
	    match_tms_in_term match_list (rand tm) new_list
	end

val pat_match_tms_in_term = match_tms_in_term 
    [--`eval_atpat_match`--, --`eval_patrow_match`--, --`eval_pat_match`--]

fun pat_rewrite_matches (asms, gl) =
    let val match_tms = pat_match_tms_in_term gl []
	val rewrites1 = map get_info match_tms
	val rewrites = fold 
	    (fn ((def, thms), thm_list) => def::(thms@thm_list)) rewrites1 []
    in
	REWRITE_TAC rewrites (asms, gl)
    end;
	    
val finish_axiom_tac =
    exists_no_prime THEN REPEAT CONJ_TAC THEN REFL_TAC

(* this isn't the most efficient way to solve this, but since there are 
   very few axioms, I'll use it *)
fun axiom_disj_tac (asms, gl) =
    if is_disj gl then 
       ((DISJ1_TAC THEN finish_axiom_tac) ORELSE 
	(DISJ2_TAC THEN axiom_disj_tac)) (asms, gl)
    else finish_axiom_tac (asms, gl)    

fun pat_axiom_tac (asms, gl) =
    let val (match_tm, _) = strip_comb gl
	val (match_tm_def, _) = get_info match_tm
    in
	(REWRITE_TAC [match_tm_def] THEN axiom_disj_tac) (asms, gl)
    end;

fun match_types tm1 tm2 =
    if (is_var tm1 andalso is_var tm2) orelse
       (is_const tm1 andalso is_const tm2) then
	type_of tm1 = type_of tm2
    else if is_abs tm1 andalso is_abs tm2 then
        (type_of tm1 = type_of tm2) andalso
        (type_of (bvar tm1) = type_of (bvar tm2)) andalso
	(match_types (body tm1) (body tm2))
    else if is_comb tm1 andalso is_comb tm2 then
	(type_of tm1 = type_of tm2) andalso
        (match_types (rator tm1) (rator tm2)) andalso
	(match_types (rand tm1) (rand tm2))
    else
	false

fun conjs_OK (conj::conjs) =
    let val {lhs = left, rhs = right} = dest_eq conj
	val left_cons = fst (strip_comb left)
	val right_cons = fst (strip_comb right)
    in  
	(left_cons = right_cons) andalso
	(match_types left right) andalso (conjs_OK conjs)
    end
  | conjs_OK [] = true

fun pick_correct_disj (asms, gl) =
    if not (is_disj gl) then ALL_TAC (asms, gl)
    else
	let val disj1 = #disj1 (dest_disj gl)
	    val (_, tm1) = strip_exists disj1
	    val conjs = strip_conj tm1
	    val (tm_to_check::other_conjs) = rev conjs
	in
	    (if (conjs_OK other_conjs) andalso 
		(match_types tm_to_check (hd asms)) then DISJ1_TAC
	     else DISJ2_TAC THEN pick_correct_disj) (asms, gl)
	end;

fun undisch_hd_asms (asms, gl) =
    UNDISCH_TAC (hd asms) (asms, gl)

fun pat_rule_tac (asms, gl) =
    let val app_match_tm = #conseq (dest_imp gl)
	val (match_tm, args) = strip_comb app_match_tm
	val (match_tm_def, rewrites) = get_info match_tm
	(* kludge -- avoid name clashes in theorem *)
	val new_match_tm_def = (avoid_clash match_tm_def (collect_vars args))
    in
	(DISCH_TAC THEN PURE_ONCE_REWRITE_TAC [new_match_tm_def] THEN 
	 pick_correct_disj THEN REWRITE_TAC rewrites THEN
	 new_do_exists THEN break_conjs THEN undisch_hd_asms THEN
	 pat_rewrite_matches THEN REPEAT STRIP_TAC THEN pat_solve_it)
	(asms, gl)
    end

fun pat_solve_match_tac (asms, gl) =
    (if is_imp gl then pat_rule_tac else pat_axiom_tac) (asms, gl)

val pat_lemma = TAC_PROOF 
  (([], --`eval_pat_pred eval_atpat_match eval_patrow_match eval_pat_match`--),
   PURE_ONCE_REWRITE_TAC [eval_pat_pred_DEF] THEN REPEAT CONJ_TAC THEN
   REPEAT GEN_TAC THEN pat_solve_match_tac)

val eval_atpat_match_thm = save_thm
("eval_atpat_match_thm",
 REWRITE_RULE [eval_atpat_match_DEF]
 (MP (SPECL [(--`eval_atpat_match`--), (--`eval_patrow_match`--),
	     (--`eval_pat_match`--)] atpat_eval_ind) pat_lemma));

val eval_pat_match_thm = save_thm
("eval_pat_match_thm",
 REWRITE_RULE [eval_pat_match_DEF]
 (MP (SPECL [(--`eval_atpat_match`--), (--`eval_patrow_match`--),
	     (--`eval_pat_match`--)] pat_eval_ind) pat_lemma));

val eval_patrow_match_thm = save_thm
("eval_patrow_match_thm",
 REWRITE_RULE [eval_patrow_match_DEF]
 (MP (SPECL [(--`eval_atpat_match`--), (--`eval_patrow_match`--),
	     (--`eval_pat_match`--)] patrow_eval_ind) pat_lemma));

val sval_constructors_one_one = prove_constructors_one_one sval_Axiom
val sval_constructors_distinct = prove_constructors_distinct sval_Axiom
val sym_sval_constructors_distinct = PURE_ONCE_REWRITE_RULE [EQ_SYM_EQ]
    sval_constructors_distinct
val sym_scon_constructors_distinct = PURE_ONCE_REWRITE_RULE [EQ_SYM_EQ]
    scon_constructors_distinct

local
    fun mk_rewrite asm =
	let val prop = rand asm
	    val temp1 = ISPEC prop SELECT_AX
	    val temp2 = PURE_REWRITE_RULE [FORALL_IMP_CONV (concl temp1)] temp1
	    val tm = lhs (#Body (dest_abs prop))
	    val select1 = SPEC tm (BETA_RULE (GEN_ALL temp2))
	in
	    MP select1 (ASSUME asm)
	end
in
    fun rewrite_SELECT (asms, gl) =
	ONCE_REWRITE_TAC (map mk_rewrite asms) (asms, gl)
end

val value_of_one_one = TAC_PROOF
    (([], --`!scon1 scon2. 
      (value_of scon1 = value_of scon2) = scon1 = scon2`--),
     REPEAT GEN_TAC THEN EQ_TAC THENL
     [DISJ_CASES_TAC (SPEC (--`scon1:scon`--) scon_cases_thm) THEN
      DISJ_CASES_TAC (SPEC (--`scon2:scon`--) scon_cases_thm) THEN
      rewrite_SELECT THEN 
      REWRITE_TAC [value_of_DEF, sval_constructors_one_one,
		   scon_constructors_one_one, scon_constructors_distinct,
		   sval_constructors_distinct,
		   sym_sval_constructors_distinct,
		   sym_scon_constructors_distinct],
      DISCH_TAC THEN AP_TERM_TAC THEN FIRST_ASSUM ACCEPT_TAC])


local
    val lst = CONJUNCTS env_cases
    val varenv_cases = nth (lst, length lst - 1)
    val record_cases = nth (lst, 6)
    fun get_rewrite_thm thm1 =
	let val prop = rand (concl thm1)
	    val temp1 = ISPEC prop SELECT_AX
	    val temp2 = PURE_REWRITE_RULE [FORALL_IMP_CONV (concl temp1)] temp1
	    val tm = lhs (#Body (dest_abs prop))
	    val select1 = SPEC tm (BETA_RULE (GEN_ALL temp2))
	in
	    MP select1 thm1
	end
    fun sub_first thm1 (asms, gl) =
	SUBST_OCCS_TAC [([1], thm1)] (asms, gl);
    val select_case1 = get_rewrite_thm (SPEC (--`VE:varenv`--) varenv_cases)
    val select_case2 = get_rewrite_thm (SPEC (--`r:record`--) record_cases)
in
    val add_empty_varenv_thm = TAC_PROOF
	(([], --`!VE. add_varenv empty_varenv VE = VE`--),
	 GEN_TAC THEN sub_first select_case1 THEN
	 REWRITE_TAC [add_varenv_DEF, empty_varenv_DEF, VARENV_arg_DEF,
		      empty_finmap_is_zero, SYM select_case1])
    val add_empty_record_thm = TAC_PROOF
	(([], --`!r. add_record empty_record r = r`--),
	 GEN_TAC THEN sub_first select_case2 THEN
	 REWRITE_TAC [add_record_DEF, empty_record_DEF, RECORD_arg_DEF,
		      empty_finmap_is_zero, SYM select_case2])
end

val atpat_prop = 
    --`\ap s1 e v s2 vef. !s2' vef'.
       eval_atpat ap s1 e v s2' vef' ==> (s2 = s2') /\ (vef = vef')`--

val patrow_prop = 
    --`\pr s1 e v s2 vef. !s2' vef'.
       eval_patrow pr s1 e v s2' vef' ==> (s2 = s2') /\ (vef = vef')`--

val pat_prop = 
    --`\p s1 e v s2 vef. !s2' vef'.
       eval_pat p s1 e v s2' vef' ==> (s2 = s2') /\ (vef = vef')`--;

local 
    val [distinct1, distinct3, distinct2] = CONJ_LIST 3 pat_distinct
    val [sdistinct1, sdistinct3, sdistinct2] = CONJ_LIST 3 sym_pat_distinct
    val [one1, one3, one2] = CONJ_LIST 3 pat_one_one
    val info_list =
	[(--`eval_atpat`--, (eval_atpat_match_thm,
			     [distinct1, sdistinct1, one1])),
	 (--`eval_patrow`--, (eval_patrow_match_thm,
			      [distinct2, sdistinct2, one2])),
	 (--`eval_pat`--, (eval_pat_match_thm,
			   [distinct3, sdistinct3, one3]))]
in
    fun get_info2 tm =
	snd (Lib.first (fn pr => fst pr = tm) info_list)
end

(* this function returns 
      (entire_assumption, relation, args_of_relation)
   for the assumption that looks like 
      eval_**** <args_of_relation>
   where the eval_**** is one of the relations in rel_list *)
fun find_right_asm rel_list (asm::more_asms) =
    if is_comb asm then
        let val (ftn, args) = strip_comb asm
        in
            if in_list ftn rel_list then
                (asm, ftn, args)
            else find_right_asm rel_list more_asms
        end
    else find_right_asm rel_list more_asms
  | find_right_asm rel_list [] = bad_error ()

val pat_find_right_asm = find_right_asm 
    [--`eval_atpat`--, --`eval_patrow`--, --`eval_pat`--]

(* this tactic finds the "eval_**** <args>" assumption, uses the match
   theorem to find out what that means in terms of what the forms of the
   args can be, and what the corresponding hypotheses could be, and adds
   this info to the assumptions *)
fun pat_assume_match (asms, gl) =
    let val (rator_and_args, ftn, args) = pat_find_right_asm asms
	val (match_thm, rewrites) = get_info2 ftn
	(* kludge -- avoid name clashes in theorem *)
	val thm1 = SPECL args (avoid_clash match_thm (collect_vars args))
	val thm2 = REWRITE_RULE
	    (rewrites@[varenv_fail_constructors_distinct,
                       sym_varenv_fail_constructors_distinct,
                       option_constructors_distinct,
                       sym_option_constructors_distinct]) thm1
	val thm3 = MP thm2 (ASSUME rator_and_args)
    in
	STRIP_ASSUME_TAC thm3 (asms, gl)
    end

fun pat_do_axioms (asms, gl) =
    if is_forall gl then
	ALL_TAC (asms, gl)
    else
	(pat_assume_match THEN ASM_REWRITE_TAC []) (asms, gl)

fun more_processing_tac (asms, gl) =
    if is_forall gl then (REPEAT GEN_TAC THEN DISCH_TAC) (asms, gl)
    else ALL_TAC (asms, gl)

fun find_op predicate (t::ts) = if predicate t then (SOME t)
				else find_op predicate ts
  | find_op predicate [] = NONE

fun do_false_v (asms, gl) = 
    let val (v_eq_tm, right, _) = find_eq_lhs (--`v:val`--) asms
	val not_v_eq_tm = Lib.first 
	    (fn asm => (is_comb asm) andalso (rator asm = (--`~`--))) asms
	val v_eq_tm2 = rand not_v_eq_tm
	val tm1 = rand (rand right)
	val tm2 = rand (rand (rhs v_eq_tm2))
	val concl_wanted = mk_eq {lhs = tm2, rhs = tm1}
	val rewrite_thm = 
	    if in_list concl_wanted asms then ASSUME concl_wanted
	    else SYM (ASSUME (mk_eq {lhs = tm1, rhs = tm2}))
	val not_v_eq_tm2 = PURE_ONCE_REWRITE_RULE [rewrite_thm] 
	    (ASSUME not_v_eq_tm)
	val contra = REWRITE_RULE [SYM (ASSUME v_eq_tm)] not_v_eq_tm2
    in
	CONTR_TAC contra (asms, gl)
    end

fun do_false_lookup (asms, gl) =
    let val (eq_tm1, rhs1, _) = find_eq_lhs 
	    (--`lookuplongexcon_env E longexcon`--) asms
	val (eq_tm2, rhs2, _) = find_eq_lhs 
	    (--`lookuplongexcon_env E longexcon'`--) asms
	val thm1 = PURE_ONCE_REWRITE_RULE 
	    [ASSUME (--`(longexcon:excon long) = longexcon'`--)] 
	    (ASSUME eq_tm1)
	val thm2 = PURE_ONCE_REWRITE_RULE [thm1] (ASSUME eq_tm2)
	val thm3 = PURE_REWRITE_RULE [lower_DEF] 
	    (AP_TERM (--`lower:exname lift -> exname`--) thm2)
	val (eq_tm3, _, _) = find_eq_lhs 
	    (--`EXVALval (NAMEexval en)`--) asms
	val thm4 = PURE_REWRITE_RULE [env_constructors_one_one] 
	    (ASSUME eq_tm3)
	val not_tm = Lib.first 
	    (fn asm => (is_comb asm) andalso (rator asm = (--`~`--))) asms
	val thm5 =
	    if lhs (rand not_tm) = lhs (concl thm4) then thm4
	    else SYM thm4
	val thm6 = 
	    if rhs (concl thm5) = lhs (concl thm3) then thm3
	    else SYM thm3
	val thm7 = TRANS thm5 thm6
	val thm8 = REWRITE_RULE [thm7] (ASSUME not_tm)
    in
	CONTR_TAC thm8 (asms, gl)
    end

fun RECORDval_tac (asms, gl) =
    let val (eval_term, args, _) = find_comb (--`eval_patrow`--) asms 
	val (eq_term, _, _) = find_eq_lhs (--`SOME (patrow:patrow)`--) asms
	val eq_thm = PURE_REWRITE_RULE [option_constructors_one_one]
	    (ASSUME eq_term)
	val eval_thm = PURE_REWRITE_RULE [SYM eq_thm] (ASSUME eval_term)
        (* now need to get r' = r *)
	val (v_term', _, rest) = find_eq_lhs (--`v:val`--) asms
	val (v_term, _, _) = find_eq_lhs (--`v:val`--) rest
	val rec_thm = PURE_REWRITE_RULE 
	    [env_constructors_one_one, add_empty_record_thm]
	    (TRANS (SYM (ASSUME v_term')) (ASSUME v_term))
	val eval_thm2 = PURE_REWRITE_RULE [rec_thm] eval_thm
	val forall_thm = ASSUME (Lib.first (fn asm => is_forall asm) asms)
	val result = MATCH_MP forall_thm eval_thm2
	val rewrites = CONJUNCTS
	    (PURE_REWRITE_RULE [varenv_fail_constructors_one_one] 
	     (MATCH_MP forall_thm eval_thm2))
	val test_thm = REWRITE_RULE
	    [varenv_fail_constructors_distinct, 
	     sym_varenv_fail_constructors_distinct] (CONJUNCT2 result)
	    
    in
	if concl test_thm = (--`F`--) then
            CONTR_TAC test_thm (asms, gl)
        else
            REWRITE_TAC rewrites (asms, gl)
    end

fun simple_mp_eval_pat (asms, gl) = 
    let val (eval_term, args, _) = find_comb (--`eval_pat`--) asms 
	val eq_thm = SYM (ASSUME (--`(pat:pat) = pat'`--))
	val forall_thm = ASSUME (Lib.first (fn asm => is_forall asm) asms)
	val result = MATCH_MP forall_thm (PURE_ONCE_REWRITE_RULE [eq_thm]
			     (ASSUME eval_term))
    in
	ACCEPT_TAC result (asms, gl)
    end

fun simple_mp_eval_atpat (asms, gl) = 
    let val (eval_term, args, _) = find_comb (--`eval_atpat`--) asms 
	val eq_thm = SYM (ASSUME (--`(atpat:atpat) = atpat'`--))
	val forall_thm = ASSUME (Lib.first (fn asm => is_forall asm) asms)
	val result = MATCH_MP forall_thm (PURE_ONCE_REWRITE_RULE [eq_thm]
			     (ASSUME eval_term))
    in
	ACCEPT_TAC result (asms, gl)
    end

fun mp_eval_pat (asms, gl) = 
    let val (eval_term, _, _) = find_comb (--`eval_pat`--) asms 
	val eq_thm = SYM (ASSUME (--`(pat:pat) = pat'`--))
	val eq_thm2 = SYM (ASSUME (--`(lab:label) = lab'`--))
	val forall_thm = ASSUME (Lib.first is_forall (rev asms))
	val mp_result = MATCH_MP forall_thm 
	    (PURE_ONCE_REWRITE_RULE [eq_thm, eq_thm2] (ASSUME eval_term))
        val (eq_term3, _, _) = find_eq_lhs (--`vef':varenv_fail`--) asms
	val result2 = REWRITE_RULE [ASSUME eq_term3] mp_result
	val test_thm = REWRITE_RULE
	    [varenv_fail_constructors_distinct, 
	     sym_varenv_fail_constructors_distinct] result2
    in
	if concl test_thm = (--`F`--) then
            CONTR_TAC test_thm (asms, gl)
        else
            REWRITE_TAC [result2] (asms, gl)
    end

fun pat_patrow_tac (asms, gl) =
    let val (eval_pat_tm, _, _) = find_comb (--`eval_pat`--) asms 
	val (eval_patrow_tm, _, _) = find_comb (--`eval_patrow`--) asms
	val rewrites1 = [SYM (ASSUME (--`(pat:pat) = pat'`--)),
			 SYM (ASSUME (--`(lab:label) = lab'`--))]
	val eval_pat_thm = REWRITE_RULE rewrites1 (ASSUME eval_pat_tm)
	val rev_asms = rev asms
	val forall_pat_thm = ASSUME (hd rev_asms)
	val forall_patrow_thm = ASSUME (hd (tl rev_asms))
	val pat_result = MATCH_MP forall_pat_thm eval_pat_thm
	val rewrites2 = REWRITE_RULE [varenv_fail_constructors_one_one]
	    (CONJUNCT2 pat_result)
	val rewrites3 = [SYM (ASSUME (--`(patrow:patrow) = patrow'`--)),
			 SYM (CONJUNCT1 pat_result)]
	val eval_patrow_thm = REWRITE_RULE rewrites3 (ASSUME eval_patrow_tm)
	val patrow_result = MATCH_MP forall_patrow_thm eval_patrow_thm
	val rewrites4 = rewrites2::
	    [REWRITE_RULE [varenv_fail_constructors_one_one] patrow_result]
	val test_thm = REWRITE_RULE
	    [varenv_fail_constructors_distinct, 
	     sym_varenv_fail_constructors_distinct] patrow_result
    in
	if concl test_thm = (--`F`--) then
            CONTR_TAC test_thm (asms, gl)
        else
            REWRITE_TAC rewrites4 (asms, gl)
    end

fun special_tac (asms, gl) =
    let val (v_tm1, _, rest) = find_eq_lhs (--`v:val`--) asms
	val (v_tm2, _, _) = find_eq_lhs (--`v:val`--) rest
	val eq_thm = CONJUNCT2 (PURE_REWRITE_RULE 
	    [ASSUME v_tm1, env_constructors_one_one] (ASSUME v_tm2))
	val rewrites1 = [SYM (ASSUME (--`(atpat:atpat) = atpat'`--)), eq_thm]
	val (eval_atpat_tm, _, _) = find_comb (--`eval_atpat`--) asms 
	val eval_atpat_thm = REWRITE_RULE rewrites1 (ASSUME eval_atpat_tm)
	val result = MATCH_MP 
	    (ASSUME (Lib.first is_forall asms)) eval_atpat_thm
    in
	ACCEPT_TAC result (asms, gl)
    end

fun do_false_assum (asms, gl) =
    let val asm1 = ASSUME (--`long_base longcon = (con:con)`--)
	val asm2 = PURE_ONCE_REWRITE_RULE
	    [SYM (ASSUME (--`(longcon:con long) = longcon'`--))]
	    (ASSUME (--`long_base longcon' = (con':con)`--))
	val con_eq_thm = PURE_ONCE_REWRITE_RULE [asm2] asm1
	val (v_tm1, _, _) = find_eq_lhs (--`v:val`--) asms
	val not_v_tm = Lib.first is_forall asms
	val false_thm = REWRITE_RULE [ASSUME v_tm1, con_eq_thm]
	    (SPEC (--`v':val`--) (ASSUME not_v_tm))
    in
	CONTR_TAC false_thm (asms, gl)
    end

fun do_false_assum2 (asms, gl) =
    let val asm1 = ASSUME (--`lookuplongexcon_env E longexcon = lift en`--)
	val asm2 = PURE_ONCE_REWRITE_RULE
	    [SYM (ASSUME (--`(longexcon:excon long) = longexcon'`--))]
	    (ASSUME (--`lookuplongexcon_env E longexcon' = lift en'`--))
	val en_eq_thm = PURE_REWRITE_RULE [asm2, lift_ONE_ONE] asm1
	val (v_tm1, _, _) = find_eq_lhs (--`v:val`--) asms
	val not_v_tm = Lib.first is_forall asms
	val false_thm = REWRITE_RULE [ASSUME v_tm1, en_eq_thm]
	    (SPEC (--`v':val`--) (ASSUME not_v_tm))
    in
	CONTR_TAC false_thm (asms, gl)
    end

fun do_false_ref (asms, gl) =
    let val rewrite1 = if in_list (--`longcon = BASE (CON "ref")`--) asms then
	    ASSUME (--`longcon = BASE (CON "ref")`--)
	    else SYM (ASSUME (--`BASE (CON "ref") = longcon`--))
        val thm1 = REWRITE_RULE [rewrite1, long_base_DEF]
	    (ASSUME (--`long_base longcon = (con:con)`--))
	val false_thm = REWRITE_RULE [thm1] 
	    (ASSUME (--`~(con = CON "ref")`--))
    in
	CONTR_TAC false_thm (asms, gl)
    end

fun mp_eval_atpat (asms, gl) = 
    let val (eval_term, args, _) = find_comb (--`eval_atpat`--) asms 
	val eq_thm = SYM (ASSUME (--`(atpat:atpat) = atpat'`--))
	val (v_tm1, _, rest) = find_eq_lhs (--`v:val`--) asms
	val (v_tm2, _, _) = find_eq_lhs (--`v:val`--) rest
	val eq_thm2 = CONJUNCT2 (REWRITE_RULE
	    [ASSUME v_tm1, env_constructors_one_one] (ASSUME v_tm2))
	val eval_atpat_thm = PURE_REWRITE_RULE [eq_thm, eq_thm2]
	    (ASSUME eval_term)
	val result = MATCH_MP (ASSUME (Lib.first is_forall asms))
	    eval_atpat_thm
    in
	ACCEPT_TAC result (asms, gl)
    end	    

fun mp_eval_atpat2 (asms, gl) = 
    let val (eval_term, _, _) = find_comb (--`eval_atpat`--) asms
	val s_eq = ASSUME (--`(s:state) = s2'`--)
	val rewrites = [SYM (ASSUME (--`(atpat:atpat) = atpat'`--)), SYM s_eq]
	val (eq_tm1, _, _) = find_eq_rhs (--`lift (v:val)`--) asms
	val (eq_tm2, _, _) = find_eq_rhs (--`lift (v':val)`--) asms
	val addr_eq = PURE_ONCE_REWRITE_RULE [env_constructors_one_one]
	    (ASSUME (--`ADDRval a = ADDRval a'`--))
        val eq_thm1 = PURE_REWRITE_RULE [s_eq, addr_eq] (ASSUME eq_tm1)
	val v_eq = PURE_REWRITE_RULE [ASSUME eq_tm2, lift_ONE_ONE] eq_thm1
	val eval_atpat_thm = PURE_REWRITE_RULE (v_eq::rewrites)
	    (ASSUME eval_term)
	val result = CONJUNCT2
	    (MATCH_MP (ASSUME (Lib.first is_forall asms))
	     eval_atpat_thm)
    in
	ACCEPT_TAC result (asms, gl)
    end	    

fun mp_eval_pat2 (asms, gl) =
    let val (eval_term, _, _) = find_comb (--`eval_pat`--) asms
	val eval_thm = PURE_ONCE_REWRITE_RULE
	    [SYM (ASSUME (--`(pat:pat) = pat'`--))] (ASSUME eval_term)
	val result = MATCH_MP (ASSUME (Lib.first is_forall asms))
	    eval_thm
	val result2 = PURE_ONCE_REWRITE_RULE 
	    [varenv_fail_constructors_one_one] result
	val test_thm = REWRITE_RULE 
	    [varenv_fail_constructors_distinct,
	     sym_varenv_fail_constructors_distinct] result
    in
	if concl test_thm = (--`F`--) then
            CONTR_TAC test_thm (asms, gl)
        else
	    REWRITE_TAC [result2] (asms, gl)
    end

val lemma2 = TAC_PROOF
(([], --`eval_pat_pred ^atpat_prop ^patrow_prop ^pat_prop`--),
 PURE_REWRITE_TAC [eval_pat_pred_DEF] THEN BETA_TAC THEN 
 REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
 more_processing_tac THEN pat_assume_match THEN 
 ASM_REWRITE_TAC [varenv_fail_constructors_distinct,
		  sym_varenv_fail_constructors_distinct] THENL
 (* 40 subgoals *)
 [(* goal 1 *)
  do_false_v,
  (* goal 2 *)
  do_false_v,
  (* goal 3 *)
  do_false_v,
  (* goal 4 *)
  do_false_v,
  (* goal 5 *)
  do_false_lookup,
  (* goal 6 *)
  do_false_lookup,
  (* goal 7 *)
  RECORDval_tac,
  (* goal 8 *)
  RECORDval_tac,
  (* goal 9 *)
  RECORDval_tac,
  (* goal 10 *)
  RECORDval_tac,
  (* goal 11 *)
  simple_mp_eval_pat,
  (* goal 12 *)
  mp_eval_pat,
  (* goal 13 *)
  mp_eval_pat,
  (* goal 14 *)
  mp_eval_pat,
  (* goal 15 *)
  mp_eval_pat,
  (* goal 16 *)
  mp_eval_pat,
  (* goal 17 *)
  mp_eval_pat,
  (* goal 18 *)
  mp_eval_pat,
  (* goal 19 *)
  mp_eval_pat,
  (* goal 20 *)
  pat_patrow_tac,
  (* goal 21 *)
  pat_patrow_tac,
  (* goal 22 *)
  mp_eval_pat,
  (* goal 23 *)
  pat_patrow_tac,
  (* goal 24 *)
  pat_patrow_tac,
  (* goal 25 *)
  simple_mp_eval_atpat,
  (* goal 26 *)
  special_tac,
  (* goal 27 *)
  do_false_assum,
  (* goal 28 *)
  do_false_ref,
  (* goal 29 *)
  do_false_assum,
  (* goal 30 *)
  do_false_ref,
  (* goal 31 *)
  mp_eval_atpat,
  (* goal 32 *)
  do_false_assum2,
  (* goal 33 *)
  do_false_assum2,
  (* goal 34 *)
  do_false_ref,
  (* goal 35 *)
  do_false_ref,
  (* goal 36 *)
  mp_eval_atpat2,
  (* goal 37 *)
  mp_eval_pat2,
  (* goal 38 *)
  mp_eval_pat2,
  (* goal 39 *)
  mp_eval_pat2,
  (* goal 40 *)
  mp_eval_pat2])

val lemma3 = BETA_RULE (MATCH_MP atpat_eval_ind lemma2)
val lemma4 = BETA_RULE (MATCH_MP pat_eval_ind lemma2)
val lemma5 = BETA_RULE (MATCH_MP patrow_eval_ind lemma2)

fun my_special_tactic (asms, gl) =
    let val (result'::s2'::rest) = rev (fst (strip_forall gl))
    in
        (REPEAT GEN_TAC THEN CONV_TAC ANTE_CONJ_CONV THEN DISCH_TAC THEN
         SPEC_TAC (result', result') THEN SPEC_TAC (s2', s2') THEN
	 undisch_hd_asms THEN
         (MAP_EVERY (fn var => SPEC_TAC (var, var)) rest) THEN
         (ACCEPT_TAC lemma3 ORELSE ACCEPT_TAC lemma4 ORELSE
	  ACCEPT_TAC lemma5)) (asms, gl)
    end

val eval_atpat_det = save_thm 
("eval_atpat_det",
 TAC_PROOF
 (([], --`!ap s1 E v s2 vef s2' vef'.
   (eval_atpat ap s1 E v s2 vef /\ eval_atpat ap s1 E v s2' vef') ==>
       (s2 = s2') /\ (vef = vef')`--),
  my_special_tactic))

val eval_pat_det = save_thm 
("eval_pat_det",
 TAC_PROOF
 (([], --`!p s1 E v s2 vef s2' vef'.
   (eval_pat p s1 E v s2 vef /\ eval_pat p s1 E v s2' vef') ==>
       (s2 = s2') /\ (vef = vef')`--),
  my_special_tactic))

val eval_patrow_det = save_thm 
("eval_patrow_det",
 TAC_PROOF
 (([], --`!pr s1 E r s2 vef s2' vef'.
   (eval_patrow pr s1 E r s2 vef /\ eval_patrow pr s1 E r s2' vef') ==>
       (s2 = s2') /\ (vef = vef')`--),
  my_special_tactic))
