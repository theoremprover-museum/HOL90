(* file exp_det.sml *)

fun bad_error () = raise HOL_ERR
    {message = "this case should never happen, real problem here!",
     origin_function = "anything...",
     origin_structure = "exp_det"}

local
    val rules_sat = (* expression rules satisfied for now *)
	REWRITE_RULE [eval_pred_DEF]
	EVAL_RULES_SATISFIED
    val conjs = CONJUNCTS rules_sat
    fun not_imp thm1 = not (is_imp (snd (strip_forall (concl thm1))))
    val non_imps = filter not_imp conjs
    fun is_an_imp thm1 = is_imp (snd (strip_forall (concl thm1)))
    val imps = filter is_an_imp conjs
    val match_term_list = make_match_terms rules_sat
in
    val speced_exp_imps = map SPEC_ALL imps
    val accept_exp_axiom = MAP_FIRST MATCH_ACCEPT_TAC non_imps
    val eval_atexp_match_DEF =
	new_definition ("eval_atexp_match_DEF", nth (match_term_list, 0))
    val eval_exprow_match_DEF =
	new_definition ("eval_exprow_match_DEF", nth (match_term_list, 1))
    val eval_exp_match_DEF =
	new_definition ("eval_exp_match_DEF", nth (match_term_list, 2))
    val eval_match_match_DEF =
	new_definition ("eval_match_match_DEF", nth (match_term_list, 3))
    val eval_mrule_match_DEF =
	new_definition ("eval_mrule_match_DEF", nth (match_term_list, 4))
    val eval_dec_match_DEF =
	new_definition ("eval_dec_match_DEF", nth (match_term_list, 5))
    val eval_valbind_match_DEF =
	new_definition ("eval_valbind_match_DEF", nth (match_term_list, 6));
end

val atexp_eval_ind = TAC_PROOF (([],
--`!atexp_prop exprow_prop exp_prop match_prop mrule_prop
    dec_prop valbind_prop.
   eval_pred atexp_prop exprow_prop exp_prop match_prop mrule_prop
    dec_prop valbind_prop ==>
   (!ae s1 e s2 vp. eval_atexp ae s1 e s2 vp ==>
                    atexp_prop ae s1 e s2 vp)`--),
(PURE_ONCE_REWRITE_TAC [eval_atexp_DEF]) THEN
(REPEAT GEN_TAC) THEN (DISCH_TAC) THEN (REPEAT GEN_TAC) THEN
(DISCH_THEN IMP_RES_TAC));

val exprow_eval_ind = TAC_PROOF (([],
--`!atexp_prop exprow_prop exp_prop match_prop mrule_prop
    dec_prop valbind_prop.
   eval_pred atexp_prop exprow_prop exp_prop match_prop mrule_prop
    dec_prop valbind_prop ==>
   (!er s1 e s2 rp. eval_exprow er s1 e s2 rp ==>
                    exprow_prop er s1 e s2 rp)`--),
(PURE_ONCE_REWRITE_TAC [eval_exprow_DEF]) THEN
(REPEAT GEN_TAC) THEN (DISCH_TAC) THEN (REPEAT GEN_TAC) THEN
(DISCH_THEN IMP_RES_TAC));

val exp_eval_ind = TAC_PROOF (([],
--`!atexp_prop exprow_prop exp_prop match_prop mrule_prop
    dec_prop valbind_prop.
   eval_pred atexp_prop exprow_prop exp_prop match_prop mrule_prop
    dec_prop valbind_prop ==>
   (!ex s1 e s2 vp. eval_exp ex s1 e s2 vp ==>
                    exp_prop ex s1 e s2 vp)`--),
(PURE_ONCE_REWRITE_TAC [eval_exp_DEF]) THEN
(REPEAT GEN_TAC) THEN (DISCH_TAC) THEN (REPEAT GEN_TAC) THEN
(DISCH_THEN IMP_RES_TAC));

val match_eval_ind = TAC_PROOF
 (([],
--`!atexp_prop exprow_prop exp_prop match_prop mrule_prop
    dec_prop valbind_prop.
   eval_pred atexp_prop exprow_prop exp_prop match_prop mrule_prop
    dec_prop valbind_prop ==>
   (!m s1 v e s2 vpf. eval_match m s1 v e s2 vpf ==>
                    match_prop m s1 v e s2 vpf)`--),
(PURE_ONCE_REWRITE_TAC [eval_match_DEF]) THEN
(REPEAT GEN_TAC) THEN (DISCH_TAC) THEN (REPEAT GEN_TAC) THEN
(DISCH_THEN IMP_RES_TAC));

val mrule_eval_ind = TAC_PROOF
 (([],
--`!atexp_prop exprow_prop exp_prop match_prop mrule_prop
    dec_prop valbind_prop.
   eval_pred atexp_prop exprow_prop exp_prop match_prop mrule_prop
    dec_prop valbind_prop ==>
   (!mr s1 v e s2 vpf. eval_mrule mr s1 v e s2 vpf ==>
                    mrule_prop mr s1 v e s2 vpf)`--),
(PURE_ONCE_REWRITE_TAC [eval_mrule_DEF]) THEN
(REPEAT GEN_TAC) THEN (DISCH_TAC) THEN (REPEAT GEN_TAC) THEN
(DISCH_THEN IMP_RES_TAC));

val dec_eval_ind = TAC_PROOF
 (([],
--`!atexp_prop exprow_prop exp_prop match_prop mrule_prop
    dec_prop valbind_prop.
   eval_pred atexp_prop exprow_prop exp_prop match_prop mrule_prop
    dec_prop valbind_prop ==>
   (!d s1 e s2 ep. eval_dec d s1 e s2 ep ==>
                    dec_prop d s1 e s2 ep)`--),
(PURE_ONCE_REWRITE_TAC [eval_dec_DEF]) THEN
(REPEAT GEN_TAC) THEN (DISCH_TAC) THEN (REPEAT GEN_TAC) THEN
(DISCH_THEN IMP_RES_TAC));

val valbind_eval_ind = TAC_PROOF
 (([],
--`!atexp_prop exprow_prop exp_prop match_prop mrule_prop
    dec_prop valbind_prop.
   eval_pred atexp_prop exprow_prop exp_prop match_prop mrule_prop
    dec_prop valbind_prop ==>
   (!vb s1 e s2 vep. eval_valbind vb s1 e s2 vep ==>
                    valbind_prop vb s1 e s2 vep)`--),
(PURE_ONCE_REWRITE_TAC [eval_valbind_DEF]) THEN
(REPEAT GEN_TAC) THEN (DISCH_TAC) THEN (REPEAT GEN_TAC) THEN
(DISCH_THEN IMP_RES_TAC));

fun match_exp_imps gl =
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
        val thm_ops = map mk_matched_thm speced_exp_imps
        val filtered_list = filter (fn NONE => false | SOME x => true) thm_ops
        val matching_thms = map (fn SOME x => x) filtered_list
        val imp_thm = put_together matching_thms
    in
        imp_thm
    end

fun match_exp_imps_tac (asms, gl) =
    MP_IMP_TAC (match_exp_imps gl) (asms, gl)

val sym_val_pack_constructors_distinct = PURE_ONCE_REWRITE_RULE
    [EQ_SYM_EQ] val_pack_constructors_distinct
val sym_record_pack_constructors_distinct = PURE_ONCE_REWRITE_RULE
    [EQ_SYM_EQ] record_pack_constructors_distinct
val sym_val_pack_fail_constructors_distinct = PURE_ONCE_REWRITE_RULE
    [EQ_SYM_EQ] val_pack_fail_constructors_distinct
val sym_env_pack_constructors_distinct = PURE_ONCE_REWRITE_RULE
    [EQ_SYM_EQ] env_pack_constructors_distinct
val sym_varenv_pack_constructors_distinct = PURE_ONCE_REWRITE_RULE
    [EQ_SYM_EQ] varenv_pack_constructors_distinct

val sym_gram_distinct = PURE_ONCE_REWRITE_RULE [EQ_SYM_EQ] gram_distinct

local
    val distinct = CONJ_LIST 7 gram_distinct
    val sdistinct = CONJ_LIST 7 sym_gram_distinct
    val ones = CONJ_LIST 10 gram_one_one
    val env_one_one = CONJ_LIST 16 env_constructors_one_one
    val env_distinct = CONJ_LIST 5 env_constructors_distinct
in
    val atexp_distinct = [nth (distinct, 0), nth (sdistinct, 0)]
    val exp_distinct = [nth (distinct, 2), nth (sdistinct, 2)]
    val dec_distinct = [nth (distinct, 1), nth (sdistinct, 1)]
    val valbind_distinct = [nth (distinct, 5), nth (sdistinct, 5)]
    val atexp_one_one = nth (ones, 0)
    val exprow_one_one = nth (ones, 3)
    val exp_one_one = nth (ones, 2)
    val match_one_one = nth (ones, 5)
    val mrule_one_one = nth (ones, 7)
    val dec_one_one = nth (ones, 1)
    val valbind_one_one = nth (ones, 8)
    val one_one_thms = [nth (ones, 0), nth (ones, 3), nth (ones, 2),
			nth (ones, 5), nth (ones, 7), nth (ones, 1),
			nth (ones, 8)]
    val val_constructors_one_one = nth (env_one_one, 11)
    val val_constructors_distinct = nth (env_distinct, 3)
    val sym_val_constructors_distinct = PURE_ONCE_REWRITE_RULE
	[EQ_SYM_EQ] val_constructors_distinct
    val exval_constructors_one_one = nth (env_one_one, 2)
    val closure_one_one = hd env_one_one
    val record_one_one = nth (env_one_one, 6)
end

local 
    val info_list2 =
	[(--`eval_atexp`--, 
	  [val_pack_constructors_distinct,
	   sym_val_pack_constructors_distinct,
	   val_pack_constructors_one_one]),
	 (--`eval_exprow`--, 
	  [record_pack_constructors_distinct, 
	   sym_record_pack_constructors_distinct,
	   record_pack_constructors_one_one]),
	 (--`eval_exp`--, 
	   [val_pack_constructors_distinct,
	    sym_val_pack_constructors_distinct,
	    val_pack_constructors_one_one]),
	 (--`eval_match`--, 
	   [val_pack_fail_constructors_distinct,
	    sym_val_pack_fail_constructors_distinct,
	    val_pack_fail_constructors_one_one]),
	 (--`eval_mrule`--,
	   [val_pack_fail_constructors_distinct,
	    sym_val_pack_fail_constructors_distinct,
	    val_pack_fail_constructors_one_one]),
	 (--`eval_dec`--, 
	   [env_pack_constructors_distinct, 
	    sym_env_pack_constructors_distinct,
	    env_pack_constructors_one_one]),
	 (--`eval_valbind`--, 
	   [varenv_pack_constructors_distinct, 
	    sym_varenv_pack_constructors_distinct,
	    varenv_pack_constructors_one_one])]
    val info_list3 =
	[(--`eval_atexp_match`--, 
	  (eval_atexp_match_DEF,
	   [val_pack_constructors_distinct,
	    sym_val_pack_constructors_distinct,
	    val_pack_constructors_one_one,
	    pack_constructors_one_one, exval_constructors_one_one,
	    val_constructors_distinct, sym_val_constructors_distinct,
	    atexp_one_one, option_constructors_distinct,
	    sym_option_constructors_distinct,
	    option_constructors_one_one]@atexp_distinct)),
	 (--`eval_exprow_match`--, 
	  (eval_exprow_match_DEF,
	   [record_pack_constructors_distinct, 
	    sym_record_pack_constructors_distinct,
	    record_pack_constructors_one_one, pack_constructors_one_one, 
	    exprow_one_one, option_constructors_distinct,
	    sym_option_constructors_distinct, option_constructors_one_one])),
	 (--`eval_exp_match`--, 
	  (eval_exp_match_DEF,
	   [val_pack_constructors_distinct, sym_val_pack_constructors_distinct,
	    val_pack_constructors_one_one, exval_constructors_one_one,
	    pack_constructors_one_one, val_constructors_distinct,
	    sym_val_constructors_distinct, exp_one_one]@exp_distinct)),
	 (--`eval_match_match`--,
	  (eval_match_match_DEF,
	   [val_pack_fail_constructors_distinct,
	    sym_val_pack_fail_constructors_distinct,
	    val_pack_fail_constructors_one_one,
	    match_one_one, option_constructors_distinct,
	    sym_option_constructors_distinct,
	    option_constructors_one_one, exval_constructors_one_one,
	    pack_constructors_one_one, val_constructors_distinct,
	    sym_val_constructors_distinct])),
	 (--`eval_mrule_match`--,
	  (eval_mrule_match_DEF,
	   [val_pack_fail_constructors_distinct,
	    sym_val_pack_fail_constructors_distinct,
	    val_pack_fail_constructors_one_one, mrule_one_one,
	    exval_constructors_one_one, pack_constructors_one_one,
	    val_constructors_distinct, sym_val_constructors_distinct])),
	 (--`eval_dec_match`--,
	  (eval_dec_match_DEF,
	   [env_pack_constructors_distinct, 
	    sym_env_pack_constructors_distinct,
	    env_pack_constructors_one_one, dec_one_one,
	    pack_constructors_one_one]@dec_distinct)),
	 (--`eval_valbind_match`--, 
	  (eval_valbind_match_DEF,
	   [varenv_pack_constructors_distinct, 
	    sym_varenv_pack_constructors_distinct,
	    varenv_pack_constructors_one_one, valbind_one_one,
	    option_constructors_distinct, sym_option_constructors_distinct,
	    option_constructors_one_one, 
	    pack_constructors_one_one]@valbind_distinct))]
in
    (* in the process of solving subgoals for the proof of determinism, we
       end up matching assumptions
           eval_exp exp s' (add_env E E') s2' (VALvp v'))
       against
           !s2' vp'.
              eval_exp exp s' (add_env E E') s2' vp' ==>
              (s2 = s2') /\ (VALvp v = vp')
       getting results of 
           (s2 = s2') /\ (VALvp v = VALvp v')
       get_info2 returns the information necessary to rewrite this to
           (s2 = s2') /\ (v = v')   *)
    fun get_info2 tm =
	snd (Lib.first (fn pr => fst pr = tm) info_list2)
    (* get_info3 is used to retrieve the match property definition, as well
       as the rewrites that will eliminate the unsatisfiable disjunctions
       after I rewrite a term with this definition *)
    fun get_info3 tm =
	snd (Lib.first (fn pr => fst pr = tm) info_list3)
end

(* by this point we should have either:
      existentials
      negations
      eval_....
   should not be an equality *)
fun check_form (asms, gl) =
    if is_eq gl then (FAIL_TAC "bad form") (asms, gl) 
    else ALL_TAC (asms, gl)

(* MP_IMP_TAC (match_exp_imps (snd (top_goal ())))
   PURE_ASM_REWRITE_TAC [] THEN TRY accept_exp_axiom
  *)

fun helper_tac (asms, gl) =
    let val imp_thm = match_exp_imps gl
    in
	if is_disj (#ant (dest_imp (concl imp_thm))) then
	    (MP_IMP_TAC imp_thm THEN choice_tac) (asms, gl)
	else
	    (MP_IMP_TAC imp_thm THEN break_conjs THEN 
	     simple_solve) (asms, gl)
    end

fun solve_it (asms, gl) = 
    if is_exists gl then 
	(new_do_exists THEN break_conjs THEN check_form THEN
	solve_it) (asms, gl)
    else (* must be eval_.... *)
	(PURE_ASM_REWRITE_TAC [] THEN (accept_exp_axiom ORELSE helper_tac))
	(asms, gl)

fun axiom_tac (asms, gl) =
    let val (match_tm, _) = strip_comb gl
	val (match_tm_def, _) = get_info3 match_tm
    in
	(REWRITE_TAC [match_tm_def] THEN axiom_disj_tac) (asms, gl)
    end

val exp_match_list = [--`eval_atexp_match`--, --`eval_exprow_match`--,
		      --`eval_exp_match`--, --`eval_match_match`--,
		      --`eval_mrule_match`--, --`eval_dec_match`--,
		      --`eval_valbind_match`--]

val exp_match_tms_in_term = match_tms_in_term exp_match_list

fun rewrite_matches (asms, gl) =
    let val match_tms = exp_match_tms_in_term gl []
	val rewrites1 = map get_info3 match_tms
	val rewrites = fold 
	    (fn ((def, thms), thm_list) => def::(thms@thm_list)) rewrites1 []
    in
	REWRITE_TAC rewrites (asms, gl)
    end
	    
fun rule_tac (asms, gl) =
    let val app_match_tm = #conseq (dest_imp gl)
	val (match_tm, _) = strip_comb app_match_tm
	val (match_tm_def, rewrites) = get_info3 match_tm
    in
	(DISCH_TAC THEN PURE_ONCE_REWRITE_TAC [match_tm_def] THEN 
	 pick_correct_disj THEN REWRITE_TAC rewrites THEN
	 new_do_exists THEN break_conjs THEN undisch_hd_asms THEN
	 rewrite_matches THEN REPEAT STRIP_TAC THEN solve_it)
	(asms, gl)
    end

fun solve_match_tac (asms, gl) =
    (if is_imp gl then rule_tac else axiom_tac) (asms, gl)

val exp_lemma = TAC_PROOF
   (([], --`eval_pred eval_atexp_match eval_exprow_match eval_exp_match
     eval_match_match eval_mrule_match eval_dec_match 
     eval_valbind_match`--),
    PURE_ONCE_REWRITE_TAC [eval_pred_DEF] THEN REPEAT CONJ_TAC THEN
    REPEAT GEN_TAC THEN solve_match_tac)

val spec_list = [--`eval_atexp_match`--, --`eval_exprow_match`--,
		 --`eval_exp_match`--, --`eval_match_match`--,
		 --`eval_mrule_match`--, --`eval_dec_match`--,
		 --`eval_valbind_match`--]

val eval_atexp_match_thm = save_thm 
("eval_atexp_match_thm",
 REWRITE_RULE [eval_atexp_match_DEF]
 (MP (SPECL spec_list atexp_eval_ind) exp_lemma));
val eval_exprow_match_thm = save_thm 
("eval_exprow_match_thm",
 REWRITE_RULE [eval_exprow_match_DEF]
 (MP (SPECL spec_list exprow_eval_ind) exp_lemma));
val eval_exp_match_thm = save_thm 
("eval_exp_match_thm",
 REWRITE_RULE [eval_exp_match_DEF]
 (MP (SPECL spec_list exp_eval_ind) exp_lemma));
val eval_match_match_thm = save_thm 
("eval_match_match_thm",
 REWRITE_RULE [eval_match_match_DEF]
 (MP (SPECL spec_list match_eval_ind) exp_lemma));
val eval_mrule_match_thm = save_thm 
("eval_mrule_match_thm",
 REWRITE_RULE [eval_mrule_match_DEF]
 (MP (SPECL spec_list mrule_eval_ind) exp_lemma));
val eval_dec_match_thm = save_thm 
("eval_dec_match_thm",
 REWRITE_RULE [eval_dec_match_DEF]
 (MP (SPECL spec_list dec_eval_ind) exp_lemma));
val eval_valbind_match_thm = save_thm 
("eval_valbind_match_thm",
 REWRITE_RULE [eval_valbind_match_DEF]
 (MP (SPECL spec_list valbind_eval_ind) exp_lemma));

local
    val distinct = CONJ_LIST 7 gram_distinct
    val sdistinct = CONJ_LIST 7 sym_gram_distinct
    val ones = CONJ_LIST 10 gram_one_one
    val info_list =
	[(--`eval_atexp`--, 
	  (eval_atexp_match_thm,
	   [nth (distinct, 0), nth (sdistinct, 0), nth (ones, 0), 
	    val_pack_constructors_distinct,
	    sym_val_pack_constructors_distinct,
	    option_constructors_distinct, option_constructors_one_one,
	    sym_option_constructors_distinct])),
	 (--`eval_exprow`--, 
	  (eval_exprow_match_thm,
	   [nth (ones, 3), record_pack_constructors_distinct, 
	    sym_record_pack_constructors_distinct,
	    option_constructors_distinct, option_constructors_one_one,
	    sym_option_constructors_distinct])),	
	 (--`eval_exp`--, 
	  (eval_exp_match_thm,
	   [nth (distinct, 2), nth (sdistinct, 2), nth (ones, 2),
	    val_pack_constructors_distinct,
	    sym_val_pack_constructors_distinct])),
	 (--`eval_match`--, 
	  (eval_match_match_thm,
	   [nth (ones, 5), val_pack_fail_constructors_distinct,
	    sym_val_pack_fail_constructors_distinct,
	    option_constructors_distinct, option_constructors_one_one,
	    sym_option_constructors_distinct])),
	 (--`eval_mrule`--,
	  (eval_mrule_match_thm,
	   [nth (ones, 7), val_pack_fail_constructors_distinct,
	    sym_val_pack_fail_constructors_distinct])),
	 (--`eval_dec`--, 
	  (eval_dec_match_thm,
	   [nth (distinct, 1), nth (sdistinct, 1), nth (ones, 1),
	    env_pack_constructors_distinct, 
	    sym_env_pack_constructors_distinct])),
	 (--`eval_valbind`--, 
	  (eval_valbind_match_thm,
	   [nth (distinct, 5), nth (sdistinct, 5), nth (ones, 8),
	    varenv_pack_constructors_distinct, 
	    sym_varenv_pack_constructors_distinct,
	    option_constructors_distinct, option_constructors_one_one,
	    sym_option_constructors_distinct]))]
in
    (* this returns the match theorem for the appropriate evaluation
       relation, and also the theorems needed to eliminate unsatisfiable
       disjunctions and simplify the term resulting from rewriting with
       the match theorem *)
    fun get_info4 tm =
	snd (Lib.first (fn pr => fst pr = tm) info_list)
end

val atexp_prop = --`\ae s1 e s2 vp. !s2' vp'.
    eval_atexp ae s1 e s2' vp' ==> (s2 = s2') /\ (vp = vp')`--
val exprow_prop = --`\er s1 e s2 rp. !s2' rp'.
    eval_exprow er s1 e s2' rp' ==> (s2 = s2') /\ (rp = rp')`--
val exp_prop = --`\ex s1 e s2 vp. !s2' vp'.
    eval_exp ex s1 e s2' vp' ==> (s2 = s2') /\ (vp = vp')`--
val match_prop = --`\m s1 v e s2 vpf. !s2' vpf'.
    eval_match m s1 v e s2' vpf' ==> (s2 = s2') /\ (vpf = vpf')`--
val mrule_prop = --`\mr s1 v e s2 vpf. !s2' vpf'.
    eval_mrule mr s1 v e s2' vpf' ==> (s2 = s2') /\ (vpf = vpf')`--
val dec_prop = --`\d s1 e s2 ep. !s2' ep'.
    eval_dec d s1 e s2' ep' ==> (s2 = s2') /\ (ep = ep')`--
val valbind_prop = --`\vb s1 e s2 vep. !s2' vep'.
    eval_valbind vb s1 e s2' vep' ==> (s2 = s2') /\ (vep = vep')`--

val exp_find_right_asm = find_right_asm 
    [--`eval_atexp`--, --`eval_exprow`--, --`eval_exp`--,
     --`eval_match`--, --`eval_mrule`--, --`eval_dec`--,
     --`eval_valbind`--]

(* this tactic finds the "eval_**** <args>" assumption, uses the match
   theorem to find out what that means in terms of what the forms of the
   args can be, and what the corresponding hypotheses could be, and adds
   this info to the assumptions *)
fun assume_match (asms, gl) =
    let val (rator_and_args, ftn, args) = exp_find_right_asm asms
        val (match_thm, rewrites) = get_info4 ftn
        (* kludge -- avoid name clashes in theorem *)
        val thm1 = SPECL args (avoid_clash match_thm (collect_vars args))
        val thm2 = REWRITE_RULE rewrites thm1
	val thm3 = MP thm2 (ASSUME rator_and_args)
    in
        STRIP_ASSUME_TAC thm3 (asms, gl)
    end

fun do_axioms (asms, gl) =
    if is_forall gl then
	ALL_TAC (asms, gl)
    else
	(assume_match THEN ASM_REWRITE_TAC []) (asms, gl)

(* going to need a lemma that says: 
      !l l' f. ONE_ONE f ==> ((nonempty_MAP f l = nonempty_MAP f l') = l = l')
   in order to show that 
      nonempty_MAP lift E_1_n = nonempty_MAP lift E_1_n'
   implies E_1_n = E_1_n'
   File one_map.sml does this, defines nonempty_MAP_thm which is the lemma
   needed *)


val one_one_lift_thm = TAC_PROOF
    (([], --`ONE_ONE (lift:env->env lift)`--),
     REWRITE_TAC [ONE_ONE_DEF, lift_ONE_ONE])

val nonempty_MAP_thm2 = MP
    (ISPECL [--`E_1_n:env nonemptylist`--, --`E_1_n':env nonemptylist`--, 
	     --`lift:env -> env lift`--] nonempty_MAP_thm)
    one_one_lift_thm

fun lookup_tac (asms, gl) =
    let val first_assum = hd asms
	val last_assum = nth (asms, length asms - 1)
	fun last_arg tm = hd (rev (snd (strip_comb tm)))
	val tm1 = last_arg (lhs first_assum)
	val tm2 = last_arg (lhs last_assum)
	val thm1 = PURE_ONCE_REWRITE_RULE
	    [ASSUME (mk_eq {lhs = tm2, rhs = tm1})] (ASSUME last_assum)
	val thm2 = PURE_ONCE_REWRITE_RULE [thm1] (ASSUME first_assum)
	val thm3 = if is_comb (lhs (concl thm2)) then
	    PURE_ONCE_REWRITE_RULE [lift_ONE_ONE] thm2
	    else thm2
        (* this last bit applies to only one case... *)
	val thm4 = 
	    if is_comb (lhs (concl thm3)) then
		REWRITE_RULE [nonempty_MAP_thm2] thm3
	    else thm3
    in
	ASM_REWRITE_TAC [thm4] (asms, gl)
    end

fun add_prime var =
    let val {Name = name, Ty = ty} = dest_var var
    in
	mk_var {Name = name^"'", Ty = ty}
    end

fun get_and_process_asm rel arg1 arg1' result1 (assum::more_asms) =
    if (not (is_eq assum)) andalso (is_comb assum) then
	let val (new_rel, new_arg1::more_args) = strip_comb assum
	in
	    if (new_rel = rel) andalso (arg1' = new_arg1) then
		let val sym_result1 =
		    map (PURE_ONCE_REWRITE_RULE [EQ_SYM_EQ]) result1
		    val thm1 = SYM (ASSUME (mk_eq {lhs = arg1, rhs = arg1'}))
		in
		    PURE_REWRITE_RULE (thm1::sym_result1) (ASSUME assum)
		end
	    else get_and_process_asm rel arg1 arg1' result1 more_asms
	end
    else get_and_process_asm rel arg1 arg1' result1 more_asms
  | get_and_process_asm _ _ _ _ [] = bad_error ()

fun get_and_process_asm2 rel arg1' rewrites (assum::more_asms) =
    if (not (is_eq assum)) andalso (is_comb assum) then
	let val (new_rel, new_arg1::more_args) = strip_comb assum
	in
	   if (new_rel = rel) andalso (arg1' = new_arg1) then
		let val sym_rewrites =
		    map (PURE_ONCE_REWRITE_RULE [EQ_SYM_EQ]) rewrites
		in
		    PURE_REWRITE_RULE sym_rewrites (ASSUME assum)
		end
	    else get_and_process_asm2 rel arg1' rewrites more_asms
	end
    else get_and_process_asm2 rel arg1' rewrites more_asms
  | get_and_process_asm2 _ _ _ [] = bad_error ()

val not_ref_tm = --`~(c = CON "ref")`--
val not_ref_thm = ASSUME not_ref_tm
val sym_not_ref_thm = PURE_ONCE_REWRITE_RULE [EQ_SYM_EQ] not_ref_thm

fun get_result_thm1 forall_assum asms result1 =
    let fun is_comb_lhs_or_rhs tm =
	    let val {rhs = right, lhs = left} = dest_eq tm in
		    (is_comb left) orelse (is_comb right)
	    end
	val (rel, arg1::_) = 
	    strip_comb (#ant (dest_imp (snd (strip_forall forall_assum))))
	val thm1 = get_and_process_asm rel arg1 (add_prime arg1) result1 asms
        (* thm2 looks somthing like (s2 = s2') /\ (VALvp v = VALvp v') *)
	val thm2 = MATCH_MP (ASSUME forall_assum) thm1
        (* thm3 looks somthing like (s2 = s2') /\ (v = v') *)
	val thm3 = REWRITE_RULE (get_info2 rel) thm2
	(* if the result is a value, simplify it by getting rid of 
           value constructors, or getting F is the constructors are
           different *)
	val thm4 = 
	    if (is_conj (concl thm3)) andalso
		(is_comb_lhs_or_rhs (#conj2 (dest_conj (concl thm3)))) then
		REWRITE_RULE
		[val_constructors_one_one, val_constructors_distinct,
		 sym_val_constructors_distinct, 
		 pack_constructors_one_one] thm3
	    else thm3
	(* to take care of the possibility that we have thm4 specifying that
           the result is "ref", while there's an assumption saying that it
	   isn't "ref" *)
	val thm5 =
	    if (is_conj (concl thm4)) andalso (rel = --`eval_exp`--) andalso 
		(in_list not_ref_tm asms) andalso
		(is_subterm (--`CON "ref"`--) (concl thm4)) then
		 REWRITE_RULE [not_ref_thm] 
		 (PURE_ONCE_REWRITE_RULE [EQ_SYM_EQ] thm4)
	    else thm4
    in
	thm5
    end

fun get_result_thm2 pat_or_exbind_asm asms result1 =
    let val (rel, arg1::more_args) = strip_comb pat_or_exbind_asm
	val thm1 = get_and_process_asm rel arg1 (add_prime arg1) result1 asms
	val det_thm = 
	    if rel = --`eval_exbind`-- then eval_exbind_det
	    else eval_pat_det
	val thm2 = CONJ (ASSUME pat_or_exbind_asm) thm1
	val thm3 = MATCH_MP det_thm thm2
	val rewrites =
	    if rel = --`eval_exbind`-- then 
		[exconenv_pack_constructors_distinct,
		 sym_exconenv_pack_constructors_distinct,
		 exconenv_pack_constructors_one_one]
	    else
		[varenv_fail_constructors_distinct,
		 sym_varenv_fail_constructors_distinct,
		 varenv_fail_constructors_one_one]
    in
	REWRITE_RULE rewrites thm3
    end

fun is_pat_or_exbind tm =
    let val rel = fst (strip_comb tm)
    in
	(rel = --`eval_exbind`--) orelse (rel = --`eval_pat`--)
    end

val F = --`F`--
local
    val not_tm = --`~`--
in
    fun is_not tm = (is_comb tm) andalso (rator tm = not_tm)
end

(* result1 will either be a one_element list (a thm giving results
   of previous work runs thru' the function), or empty (indicating that
   this is the first time thru', and there are no results yet) *)
fun eval_imp_tac rev_assums result1 (asms, gl) =
    let val last_assum = hd rev_assums
    in
	if not ((is_forall last_assum) orelse 
		(is_pat_or_exbind last_assum) orelse (is_not last_assum)) then
	    ASM_REWRITE_TAC result1 (asms, gl)
	else if is_not last_assum then
	    let val result2 = REWRITE_RULE 
		    [not_ref_thm, sym_not_ref_thm] (hd result1)
	    in
		if concl result2 = F then
		    CONTR_TAC result2 (asms, gl)
		else eval_imp_tac (tl rev_assums) [result2] (asms, gl)
	    end
	else
	    let val result2 = 
		    if is_forall last_assum then
			get_result_thm1 last_assum asms result1
		    else
			get_result_thm2 last_assum asms result1
	    in
		if concl result2 = F then
		    CONTR_TAC result2 (asms, gl)
		else eval_imp_tac (tl rev_assums) [result2] (asms, gl)
	    end
    end

(* e (eval_imp_tac (rev (fst (top_goal ()))) [])   *)

(* unfortunately I can't use eval_imp_tac for this one because results 
   from the first match-up (which would correspond to the first iteration
   thru' eval_imp_tac) must be used for the THIRD match-up, not the 
   second... *)
fun do_ftn_eval rev_assums (asms, gl) =
    let val (assum1::assum2::assum3::_) = rev_assums
	val result1 = get_result_thm1 assum1 asms []
	val result1' = REWRITE_RULE
	    [val_constructors_one_one, val_constructors_distinct,
	     sym_val_constructors_distinct, closure_one_one] result1
    in
	if concl result1' = F then
	    CONTR_TAC result1' (asms, gl)
	else
	    let val result2 = get_result_thm1 assum2 asms [CONJUNCT1 result1']
	    in
		if concl result2 = F then
		    CONTR_TAC result2 (asms, gl)
		else
		    let val (rel, arg1::_) = strip_comb
			    (#ant (dest_imp (snd (strip_forall assum3))))
			val thm1 = get_and_process_asm2 rel (add_prime arg1)
			    [result2, CONJUNCT2 result1'] asms
			val thm2 = MATCH_MP (ASSUME assum3) thm1
			val thm3 = REWRITE_RULE (get_info2 rel) thm2
		    in
			if concl thm3 = F then
			    CONTR_TAC thm3 (asms, gl)
			else
			    ASM_REWRITE_TAC [thm3] (asms, gl)
		    end
	    end
    end

(* e (do_ftn_eval (rev (fst (top_goal ()))))   *)

fun do_it_tac (asms, gl) = 
    let val rev_asms = rev asms
    in
	if is_eq (hd rev_asms) andalso is_eq (hd asms) then
	    lookup_tac (asms, gl)
	else if (is_forall (nth (rev_asms, 1))) andalso 
	    (is_forall (nth (rev_asms, 2))) then
	    do_ftn_eval rev_asms (asms, gl)
	else
	    eval_imp_tac rev_asms [] (asms, gl)
    end

(* subgoal with goal ENVep (add_env E1 E2') = ENVep (add_env E1' E2') *)
fun double_dec_tac (asms, gl) = 
    let val (forall_dec1::forall_dec2::_) = rev asms
	val result1 = get_result_thm1 forall_dec1 asms []
	val result2 = get_result_thm1 forall_dec2 asms [result1]
    in
	REWRITE_TAC [CONJUNCT2 result1, CONJUNCT2 result2] (asms, gl)
    end

(* subgoal involving apply, with goal v' = vp' *)
fun apply_tac (asms, gl) = 
    let val (forall_tm1::forall_tm2::_) = rev asms
	val result1 = get_result_thm1 forall_tm1 asms []
	val result2 = get_result_thm1 forall_tm2 asms [CONJUNCT1 result1]
    in
	REWRITE_TAC [CONJUNCT2 result1, CONJUNCT2 result2,
		     SYM (ASSUME (--`apply b v = v'`--)),
		     SYM (ASSUME (--`apply b' v'' = vp'`--))] (asms, gl)
    end

val record_rep_thm = TAC_PROOF 
(([], --`!a v. 
  (insert_into_record
   (insert_into_record empty_record (LABEL "1") (ADDRval a))
   (LABEL "2") v) =
  RECORD (FINMAP [(LABEL "1", ADDRval a); (LABEL "2", v)])`--),
 REPEAT GEN_TAC THEN
 REWRITE_TAC [empty_record_DEF, empty_finmap_DEF, insert_into_record_DEF,
	      finmap_insert_DEF, list_insert_DEF] THEN
 BETA_TAC THEN 
 REWRITE_TAC [insert_into_record_DEF, finmap_insert_DEF, list_insert_DEF] THEN
 BETA_TAC THEN 
 REWRITE_TAC [string_CONV (--`"1"`--), string_CONV (--`"2"`--),
	      less_label_DEF, ltstring_DEF, first_char_DEF, LABEL_arg_DEF,
	      theorem "ascii" "ASCII_11", ltascii_DEF] THEN
 BETA_TAC THEN
 REWRITE_TAC [bit1_DEF, bit2_DEF, bit3_DEF, bit4_DEF, bit5_DEF,
	      bit6_DEF, bit7_DEF])

(* subgoal insert_into_state_mem s''' a v = insert_into_state_mem s''' a' v' *)
fun assign_tac (asms, gl) = 
    let val snd_thm = theorem "pair" "SND"
	val (forall_tm1::forall_tm2::_) = rev asms
	val result1 = get_result_thm1 forall_tm1 asms []
	val result2 = get_result_thm1 forall_tm2 asms [result1]
	val result3 = REWRITE_RULE 
	    [record_rep_thm, val_constructors_one_one, record_one_one, 
	     finmap_constructors_one_one]
	    (CONJUNCT2 result2)
	val result4 = REWRITE_RULE [HD]
	    (AP_TERM (--`HD:(label#val) list -> (label#val)`--) result3)
	val result5 = REWRITE_RULE [snd_thm, val_constructors_one_one]
	    (AP_TERM (--`SND:(label#val) -> val`--) result4)
	val result6 = REWRITE_RULE [TL]
	    (AP_TERM (--`TL:(label#val)list -> (label#val)list`--) result3)
	val result7 = REWRITE_RULE [HD]
	    (AP_TERM (--`HD:(label#val) list -> (label#val)`--) result6)
	val result8 = REWRITE_RULE [snd_thm]
	    (AP_TERM (--`SND:(label#val) -> val`--) result7)
    in
	REWRITE_TAC [result5, result8] (asms, gl)
    end

(* subgoal VALvp (EXVALval (NAMEVALexval en v')) =
           VALvp (EXVALval (NAMEVALexval en' v')) *)
fun en_v_tac (asms, gl) = 
    let val (forall_tm1::forall_tm2::_) = rev asms
	val result1 = get_result_thm1 forall_tm1 asms []
	val result1' = REWRITE_RULE 
	    [val_constructors_one_one, exval_constructors_one_one]
	    (CONJUNCT2 result1)
	val result2 = get_result_thm1 forall_tm2 asms [CONJUNCT1 result1]
    in
	REWRITE_TAC [result1', CONJUNCT2 result2] (asms, gl)
    end

(* subgoal VALvp (APPCONval c v') = VALvp (APPCONval c' v') *)
fun appcon_tac (asms, gl) =
    let val forall_tm1 = hd (rev asms)
	val result1 = REWRITE_RULE [val_constructors_one_one]
	    (CONJUNCT2 (get_result_thm1 forall_tm1 asms []))
    in
	REWRITE_TAC [result1] (asms, gl)
    end

(* subgoal 
   RECORDrp (add_record (insert_into_record empty_record lab' v) r') =
   RECORDrp (add_record (insert_into_record empty_record lab' v') r') *)
fun recordrp_tac (asms, gl) = 
    let val (forall_tm1::forall_tm2::_) = rev asms
	val result1 = get_result_thm1 forall_tm1 asms []
	val result2 = get_result_thm1 forall_tm2 asms [CONJUNCT1 result1]
    in
	REWRITE_TAC [CONJUNCT2 result1, CONJUNCT2 result2] (asms, gl)
    end

(* subgoal PACKvp (PACK e) = PACKvp (PACK e') *)
fun packvp_tac (asms, gl) = 
    let val (forall_tm1::forall_tm2::_) = rev asms
	val result1 = get_result_thm1 forall_tm1 asms []
    in
	REWRITE_TAC [CONJUNCT2 result1] (asms, gl)
    end

(* subgoal VARENVvep (add_varenv VE VE''') = 
           VARENVvep (add_varenv VE'' VE''') *)
fun varenvvep_tac (asms, gl) = 
    let val (forall_tm1::pat_tm::forall_tm2::_) = rev asms
	val result1 = get_result_thm1 forall_tm1 asms []
	val result2 = get_result_thm2 pat_tm asms [result1]
	val result3 = get_result_thm1 forall_tm2 asms [CONJUNCT1 result2]

    in
	REWRITE_TAC [CONJUNCT2 result2, CONJUNCT2 result3] (asms, gl)
    end

val lemma2 = TAC_PROOF
(([], --`eval_pred ^atexp_prop ^exprow_prop ^exp_prop ^match_prop
  ^mrule_prop ^dec_prop ^valbind_prop`--),
 PURE_REWRITE_TAC [eval_pred_DEF] THEN BETA_TAC THEN
 REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
 do_axioms THEN REPEAT GEN_TAC THEN DISCH_TAC THEN assume_match THEN
 (TRY do_it_tac) THENL (* only 8 subgoals! *)
 [recordrp_tac,
  appcon_tac,
  en_v_tac,
  assign_tac,
  apply_tac,
  packvp_tac,
  double_dec_tac,
  varenvvep_tac])

val lemma_list = 
    [BETA_RULE (MATCH_MP atexp_eval_ind lemma2),
     BETA_RULE (MATCH_MP exprow_eval_ind lemma2),
     BETA_RULE (MATCH_MP exp_eval_ind lemma2),
     BETA_RULE (MATCH_MP match_eval_ind lemma2),
     BETA_RULE (MATCH_MP mrule_eval_ind lemma2),
     BETA_RULE (MATCH_MP dec_eval_ind lemma2),
     BETA_RULE (MATCH_MP valbind_eval_ind lemma2)]

fun my_special_tactic (asms, gl) =
    let val (result'::s2'::rest) = rev (fst (strip_forall gl))
    in
        (REPEAT GEN_TAC THEN CONV_TAC ANTE_CONJ_CONV THEN DISCH_TAC THEN
         SPEC_TAC (result', result') THEN SPEC_TAC (s2', s2') THEN
         undisch_hd_asms THEN
         (MAP_EVERY (fn var => SPEC_TAC (var, var)) rest) THEN
	 (MAP_FIRST ACCEPT_TAC lemma_list)) (asms, gl)
    end

val eval_atexp_det = save_thm
("eval_atexp_det",
 TAC_PROOF
 (([], --`!ae s1 e s2 vp s2' vp'. 
   (eval_atexp ae s1 e s2 vp /\ eval_atexp ae s1 e s2' vp') ==>
       (s2 = s2') /\ (vp = vp')`--),
  my_special_tactic))

val eval_exprow_det = save_thm
("eval_exprow_det",
 TAC_PROOF
 (([], --`!er s1 e s2 rp s2' rp'.
   (eval_exprow er s1 e s2 rp /\ eval_exprow er s1 e s2' rp') ==>
       (s2 = s2') /\ (rp = rp')`--),
  my_special_tactic))

val eval_exp_det = save_thm
("eval_exp_det",
 TAC_PROOF
 (([], --`!ex s1 e s2 vp s2' vp'.
   (eval_exp ex s1 e s2 vp /\ eval_exp ex s1 e s2' vp') ==>
       (s2 = s2') /\ (vp = vp')`--),
  my_special_tactic))

val eval_match_det = save_thm
("eval_match_det",
 TAC_PROOF
 (([], --`!m s1 v e s2 vpf s2' vpf'.
    (eval_match m s1 v e s2 vpf /\ eval_match m s1 v e s2' vpf') ==>
	(s2 = s2') /\ (vpf = vpf')`--),
  my_special_tactic))

val eval_mrule_det = save_thm
("eval_mrule_det",
 TAC_PROOF
 (([], --`!mr s1 v e s2 vpf s2' vpf'.
    (eval_mrule mr s1 v e s2 vpf /\ eval_mrule mr s1 v e s2' vpf') ==>
	(s2 = s2') /\ (vpf = vpf')`--),
  my_special_tactic))

val eval_dec_det = save_thm
("eval_dec_det",
 TAC_PROOF
 (([], --`!d s1 e s2 ep s2' ep'.
    (eval_dec d s1 e s2 ep /\ eval_dec d s1 e s2' ep') ==> 
	(s2 = s2') /\ (ep = ep')`--),
  my_special_tactic))

val eval_valbind_det = save_thm
("eval_valbind_det",
 TAC_PROOF
 (([], --`!vb s1 e s2 vep s2' vep'.
    (eval_valbind vb s1 e s2 vep /\ eval_valbind vb s1 e s2' vep') ==>
	(s2 = s2') /\ (vep = vep')`--),
  my_special_tactic))

