val rules_sat =
    PURE_ONCE_REWRITE_RULE [eval_exbind_pred_DEF] EVAL_EXBIND_RULES_SATISFIED

val imps = CONJUNCTS rules_sat

(* theorems are: exbind_existence, exbind_induct, exbind_unique, 
   exbind_distinct, exbind_one_one, exbind_cases *)

val match_term_list = make_match_terms rules_sat

val eval_exbind_match_DEF = 
    new_definition ("eval_exbind_match_DEF", hd match_term_list)

val sym_exbind_distinct = PURE_ONCE_REWRITE_RULE [EQ_SYM_EQ] exbind_distinct

val sym_exconenv_pack_constructors_distinct =
    PURE_ONCE_REWRITE_RULE [EQ_SYM_EQ]
    exconenv_pack_constructors_distinct

val option_constructors_distinct = theorem "more_list" 
    "option_constructors_distinct"

val sym_option_constructors_distinct =
    PURE_ONCE_REWRITE_RULE [EQ_SYM_EQ]
    option_constructors_distinct

(* looks thru' the assumptions for one like "tm2 = tm", then rewrites
   the goal with "tm = tm2" *)
fun sym_rewrite_term tm (asms, gl) =
    let val eq_asm =
            Lib.first
            (fn assum => if is_eq assum then tm = rhs assum
                         else false)
            asms
            val thm1 = PURE_ONCE_REWRITE_RULE [EQ_SYM_EQ] (ASSUME eq_asm)
    in
        (REWRITE_TAC [thm1]) (asms, gl)
    end;

(* does exists for a list of terms *)
fun exists_list (tm::terms) = EXISTS_TAC tm THEN (exists_list terms)
  | exists_list [] = ALL_TAC

(* val match_with_imps = MAP_FIRST (fn th => MATCH_MP_IMP_TAC th) imps; *)
val match_with_imps = MAP_FIRST (fn th => MATCH_MP_TAC th) imps;

val exbind_eval_ind = TAC_PROOF (([],
--`!exbind_prop. eval_exbind_pred exbind_prop ==>
    (!eb s1 e s2 eep. eval_exbind eb s1 e s2 eep ==>
                        exbind_prop eb s1 e s2 eep)`--),
(PURE_ONCE_REWRITE_TAC [eval_exbind_DEF]) THEN
(GEN_TAC) THEN (DISCH_TAC) THEN (REPEAT GEN_TAC) THEN
(DISCH_THEN IMP_RES_TAC));

(* takes one existential variable in goal, and instantiates it to the 
   same variable *)
fun var_exists (asm, gl) =
    EXISTS_TAC (#Bvar (dest_exists gl)) (asm, gl)

(* takes all existential variables in goal, and instantiates them to the 
   same variable *)
fun multi_var_exists (asm, gl) =
    let val (vars, tm) = strip_exists gl
    in
        fold
        (fn (var, tac) => (EXISTS_TAC var) THEN tac)
        vars
        ALL_TAC
        (asm, gl)
    end;

(* looks at the existential quantified vars in the goal and instantiates
   them to the same vars, but without the primes *)
fun exists_no_prime (asms, gl) =
    let val ex_vars = fst (strip_exists gl)
	fun remove_prime var = 
	    let val {Name = s, Ty = ht} = dest_var var
		val new_name = 
		    implode (filter (fn c => c <> "'") (explode s))
	    in
		mk_var {Name = new_name, Ty = ht}
	    end
	val vars = map remove_prime ex_vars
    in
	exists_list vars (asms, gl)
    end

(* effectively does ASM_REWRITE_TAC, except that it excludes the given
   assumption *)
fun asm_rewrite_except tm (asms, gl) =
    let val new_asms = filter (fn asm => asm <> tm) asms
	val thms = map ASSUME new_asms
    in
	REWRITE_TAC thms (asms, gl)
    end

val exbind_eval_ind = TAC_PROOF (([],
--`!exbind_prop. eval_exbind_pred exbind_prop ==>
    (!eb s1 e s2 eep. eval_exbind eb s1 e s2 eep ==>
                        exbind_prop eb s1 e s2 eep)`--),
(PURE_ONCE_REWRITE_TAC [definition "holML_Plain_Core" "eval_exbind_DEF"]) THEN
(GEN_TAC) THEN (DISCH_TAC) THEN (REPEAT GEN_TAC) THEN
(DISCH_THEN IMP_RES_TAC));

val exbind_lemma = TAC_PROOF (([], --`eval_exbind_pred eval_exbind_match`--),
  (REWRITE_TAC [eval_exbind_match_DEF, eval_exbind_pred_DEF,
                exbind_distinct, sym_exbind_distinct,
                exconenv_pack_constructors_distinct,
                sym_exconenv_pack_constructors_distinct,
		option_constructors_distinct,
		sym_option_constructors_distinct,
		exbind_one_one] THEN
   REPEAT STRIP_TAC THENL (* we get 14 subgoals *)
   [(* goal 1 *)
    exists_no_prime THEN REPEAT CONJ_TAC THEN (REFL_TAC ORELSE
    FIRST_ASSUM ACCEPT_TAC),
    (* goal 2 *)
    exists_no_prime THEN REPEAT CONJ_TAC THEN
    TRY REFL_TAC THEN EXISTS_TAC (--`s':state`--) THEN
    ASM_REWRITE_TAC [] THEN match_with_imps THEN REPEAT CONJ_TAC THEN
    REFL_TAC,
    (* goal 3 *)
    exists_no_prime THEN REPEAT CONJ_TAC THEN TRY REFL_TAC THEN
    var_exists THEN ASM_REWRITE_TAC [] THEN match_with_imps THEN
    EXISTS_TAC (--`s''':state`--) THEN ASM_REWRITE_TAC [],
    (* goal 4 *)
    exists_no_prime THEN REPEAT CONJ_TAC THEN TRY REFL_TAC THEN
    var_exists THEN REPEAT CONJ_TAC THEN 
    TRY (FIRST_ASSUM ACCEPT_TAC) THEN sym_rewrite_term (--`s'':state`--) THEN 
    asm_rewrite_except (--`(s':state) = s''`--) THEN
    match_with_imps THEN (FIRST_ASSUM ACCEPT_TAC),
    (* goal 5 *)
    exists_no_prime THEN REPEAT CONJ_TAC THEN TRY REFL_TAC THEN
    var_exists THEN REPEAT CONJ_TAC THEN TRY (FIRST_ASSUM ACCEPT_TAC)
    THEN asm_rewrite_except (--`s' = add_exname en s`--) THEN
    match_with_imps THEN CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC,
    (* goal 6 *)
    exists_no_prime THEN REPEAT CONJ_TAC THEN TRY REFL_TAC THEN
    multi_var_exists THEN REPEAT CONJ_TAC THEN TRY (FIRST_ASSUM ACCEPT_TAC)
    THEN asm_rewrite_except (--`s' = add_exname en s`--) THEN
    match_with_imps THEN EXISTS_TAC (--`en':exname`--) THEN
    EXISTS_TAC (--`s''':state`--) THEN 
    REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC,
    (* goal 7 *)
    exists_no_prime THEN REPEAT CONJ_TAC THEN TRY REFL_TAC THEN
    multi_var_exists THEN REPEAT CONJ_TAC THEN TRY (FIRST_ASSUM ACCEPT_TAC)
    THEN asm_rewrite_except (--`s' = add_exname en s`--) THEN
    match_with_imps THEN
    EXISTS_TAC (--`en':exname`--) THEN CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC,
    (* goal 8 *)
    exists_no_prime THEN REPEAT CONJ_TAC THEN 
    (REFL_TAC ORELSE (FIRST_ASSUM ACCEPT_TAC)),
    (* goal 9 *)
    exists_no_prime THEN REPEAT CONJ_TAC THEN 
    (TRY (REFL_TAC ORELSE (FIRST_ASSUM ACCEPT_TAC))) THEN
    asm_rewrite_except (--`s' = add_exname en s`--) THEN
    match_with_imps THEN CONJ_TAC THEN 
    (REFL_TAC ORELSE (FIRST_ASSUM ACCEPT_TAC)),
    (* goal 10 *)
    exists_no_prime THEN REPEAT CONJ_TAC THEN 
    (TRY (REFL_TAC ORELSE (FIRST_ASSUM ACCEPT_TAC))) THEN
    asm_rewrite_except (--`s' = add_exname en s`--) THEN
    match_with_imps THEN EXISTS_TAC (--`s'':state`--) THEN
    ASM_REWRITE_TAC [],
    (* goal 11 *)
    exists_no_prime THEN REPEAT CONJ_TAC THEN 
    (TRY (REFL_TAC ORELSE (FIRST_ASSUM ACCEPT_TAC))) THEN
    ASM_REWRITE_TAC [] THEN match_with_imps THEN FIRST_ASSUM ACCEPT_TAC,
    (* goal 12 *)
    exists_no_prime THEN REPEAT CONJ_TAC THEN 
    (TRY (REFL_TAC ORELSE (FIRST_ASSUM ACCEPT_TAC))) THEN
    ASM_REWRITE_TAC [] THEN match_with_imps THEN CONJ_TAC THEN
    FIRST_ASSUM ACCEPT_TAC,
    (* goal 13 *)
    exists_no_prime THEN REPEAT CONJ_TAC THEN TRY REFL_TAC THEN
    var_exists THEN ASM_REWRITE_TAC [] THEN match_with_imps THEN
    EXISTS_TAC (--`en':exname`--) THEN EXISTS_TAC (--`s'':state`--) THEN
    REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC,
    (* goal 14 *)
    exists_no_prime THEN REPEAT CONJ_TAC THEN TRY REFL_TAC THEN
    var_exists THEN ASM_REWRITE_TAC [] THEN match_with_imps THEN
    EXISTS_TAC (--`en':exname`--) THEN CONJ_TAC THEN 
    FIRST_ASSUM ACCEPT_TAC]));

val eval_exbind_match_thm = save_thm
("eval_exbind_match_thm",
 REWRITE_RULE [eval_exbind_match_DEF] 
 (MP (SPEC (--`eval_exbind_match`--) exbind_eval_ind) exbind_lemma))

(* RANDOM FTNS *)

(* returns (rator_applied_to_args, args, rest_of_asms) *)
fun find_comb wanted_rator (item::items) =
    if is_comb item then
        let val (found_rator, args) = strip_comb item
        in
            if found_rator = wanted_rator then
                (item, args, items)
            else
                find_comb wanted_rator items
        end
    else
        find_comb wanted_rator items
  | find_comb _ [] = raise HOL_ERR
    {origin_structure = "exbind_det.sml",
     origin_function = "find_comb",
     message = "item not in list"}

fun find_eq_rhs wanted_rhs (item::items) =
    if is_eq item then
        let val {lhs, rhs} = dest_eq item
        in
            if rhs = wanted_rhs then
                (item, lhs, items)
            else
                find_eq_rhs wanted_rhs items
        end
    else
        find_eq_rhs wanted_rhs items
  | find_eq_rhs _ [] = raise HOL_ERR
    {origin_structure = "exbind_det.sml",
     origin_function = "find_eq_rhs",
     message = "item not in list"}

fun find_eq_lhs wanted_lhs (item::items) =
    if is_eq item then
        let val {lhs, rhs} = dest_eq item
        in
            if lhs = wanted_lhs then
                (item, rhs, items)
            else
                find_eq_lhs wanted_lhs items
        end
    else
        find_eq_lhs wanted_lhs items
  | find_eq_lhs _ [] = raise HOL_ERR
    {origin_structure = "exbind_det.sml",
     origin_function = "find_eq_lhs",
     message = "item not in list"}

(* this is an absurdly specialized tactic, not even worth trying to 
   describe *)
fun do_something_useful (asms, gl) = 
    let val (rel_tm1, args1, _) = find_comb (--`eval_exbind`--) asms
	val (eq_tm1, phrase_tm1, _) = find_eq_rhs (hd args1) asms
	    (* rewrite with SYM (ASSUME eq_tm1) *)
	val rewrite_thms = [SYM (ASSUME eq_tm1)]
	val impl_term = (Lib.first (fn tm => is_forall tm) asms)
	val impl_thm = ASSUME impl_term
	val app_args = #ant (dest_imp (snd (strip_forall (impl_term))))
	val state_arg = nth (snd (strip_comb app_args), 1)
	val rewrite_thms = 
	    if state_arg <> nth (args1, 1) then
		let val (eq_tm2, phrase_tm2, _) = 
			find_eq_lhs (nth (args1, 1)) asms
		    val (en_tm, _, _) = find_eq_lhs (--`en:exname`--) asms
		    val (en'_tm, _, _) = find_eq_lhs (--`en':exname`--) asms
		    val thm1 = REWRITE_RULE 
			[TRANS (ASSUME en'_tm) (SYM (ASSUME en_tm))]
			(ASSUME eq_tm2)
		    val (eq_tm3, phrase_tm3, _) =
			find_eq_lhs (--`s':state`--) asms
		    val thm2 = TRANS thm1 (SYM (ASSUME eq_tm3))
		in  thm2::rewrite_thms  end
	    else rewrite_thms
	val thm3 = REWRITE_RULE rewrite_thms (ASSUME rel_tm1)
	val eq_thm = MATCH_MP impl_thm thm3
	val eq_thm2 = REWRITE_RULE [exconenv_pack_constructors_one_one] eq_thm
	val new_rewrite_thms = CONJUNCTS eq_thm2
	val test_thm =
            REWRITE_RULE [sym_exconenv_pack_constructors_distinct,
                          exconenv_pack_constructors_distinct]
            (CONJUNCT2 eq_thm2)
    in
        if concl test_thm = (--`F`--) then
            CONTR_TAC test_thm (asms, gl)
        else
	    REWRITE_TAC new_rewrite_thms (asms, gl)
    end

fun mk_fun_ty ty1 ty2 =
    mk_type {Tyop = "fun", Args = [ty1, ty2]}

(* this is an absurdly specialized tactic, not even worth trying to 
   describe *)
fun lookup_tac tm1 tm2 (asms, gl) =
    let val tm_type = type_of tm1
        val lift_type = mk_fun_ty tm_type
            (mk_type {Tyop = "lift", Args = [tm_type]})
        val lift_const = mk_const {Name = "lift", Ty = lift_type}
        val rh_tm1 = mk_comb {Rator = lift_const, Rand = tm1}
        val rh_tm2 = mk_comb {Rator = lift_const, Rand = tm2}
        val (eq_tm1, lookup_comb1, _) = find_eq_rhs rh_tm1 asms
        val (eq_tm2, lookup_comb2, _) = find_eq_rhs rh_tm2 asms
        val lookup_tm1 = hd (tl (snd (strip_comb lookup_comb1)))
        val lookup_tm2 = hd (tl (snd (strip_comb lookup_comb2)))
        val (eq_tm3, _, _) = find_eq_lhs lookup_tm1 asms
	val rewrite_thm = ASSUME eq_tm3
        val eq_thm1 = REWRITE_RULE [rewrite_thm] (ASSUME eq_tm1)
        val eq_thm2 = REWRITE_RULE [eq_thm1] (ASSUME eq_tm2)
        val eq_thm3 = REWRITE_RULE [lift_ONE_ONE] eq_thm2
    in
        REWRITE_TAC [eq_thm3] (asms, gl)
    end

(* want to prove: 
   --`!eb s1 E s2 EEp s2' EEp'.
       (eval_exbind eb s1 E s2 EEp /\ eval_exbind eb s1 E s2' EEp') ==>
	   (s2 = s2') /\ (EEp = EEp')`--
   in other words
   --`!eb s1 E s2 EEp. eval_exbind eb s1 E s2 EEp ==>
          (!s2' EEp'. eval_exbind eb s1 E s2' EEp' ==>
	      (s2 = s2') /\ (EEp = EEp'))`-- 
   so our property is
   \eb s1 E s2 EEp. !s2' EEp'. 
     eval_exbind eb s1 E s2' EEp' ==> (s2 = s2') /\ (EEp = EEp')
*)

val spec_ind = BETA_RULE 
    (SPEC 
     (--`\eb s1 E s2 EEp. !s2' EEp'. 
      eval_exbind eb s1 E s2' EEp' ==> (s2 = s2') /\ (EEp = EEp')`--)
     exbind_eval_ind)

(* this tactic finds the "eval_exbind <args>" assumption, uses the match
   theorem to find out what that means in terms of what the forms of the
   args can be, and what the corresponding hypotheses could be, and adds
   this info to the assumptions *)
fun use_match (asms, gl) = 
    let val (rator_and_args, args, _) = find_comb (--`eval_exbind`--) asms
	val thm1 = SPECL args eval_exbind_match_thm
	val thm2 = REWRITE_RULE
	    [exbind_distinct, sym_exbind_distinct,
	     exconenv_pack_constructors_distinct,
	     sym_exconenv_pack_constructors_distinct,
	     option_constructors_distinct,
	     sym_option_constructors_distinct,
	     exbind_one_one] thm1
	val thm3 = MP thm2 (ASSUME rator_and_args)
    in
	STRIP_ASSUME_TAC thm3 (asms, gl)
    end

val lemma2 = TAC_PROOF
(([],
  --`!eb s1 E s2 EEp. eval_exbind eb s1 E s2 EEp ==>
      (!s2' EEp'. eval_exbind eb s1 E s2' EEp' ==>
	  (s2 = s2') /\ (EEp = EEp'))`--),
 MATCH_MP_TAC spec_ind THEN REWRITE_TAC [eval_exbind_pred_DEF] THEN
 BETA_TAC THEN REPEAT CONJ_TAC THEN
 REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN 
 DISCH_TAC THEN use_match THEN ASM_REWRITE_TAC [] THENL
 (* 9 subgoals *)
 [(* goal 1 *)
  do_something_useful,
  (* goal 2 *)
  do_something_useful,
  (* goal 3 *)
  do_something_useful,
  (* goal 4 *)
  do_something_useful,
  (* goal 5 *)
  lookup_tac (--`en:exname`--) (--`en':exname`--),
  (* goal 6 *)
  do_something_useful THEN lookup_tac (--`en:exname`--) (--`en':exname`--),
  (* goal 7 *)
  do_something_useful,
  (* goal 8 *)
  do_something_useful,
  (* goal 9 *)
  do_something_useful])

fun my_special_tactic (asms, gl) =
    let val (EEp'::s2'::rest) = rev (fst (strip_forall gl))
    in
	(REPEAT GEN_TAC THEN CONV_TAC ANTE_CONJ_CONV THEN DISCH_TAC THEN
	 SPEC_TAC (EEp', EEp') THEN SPEC_TAC (s2', s2') THEN 
	 UNDISCH_TAC (--`eval_exbind eb s1 E s2 EEp`--) THEN
	 (MAP_EVERY (fn var => SPEC_TAC (var, var)) rest) THEN
	 (ACCEPT_TAC lemma2)) (asms, gl)
    end

(* and now, for the final theorem *)
val eval_exbind_det = save_thm
("eval_exbind_det",
 TAC_PROOF
 (([], --`!eb s1 E s2 EEp s2' EEp'.
   (eval_exbind eb s1 E s2 EEp /\ eval_exbind eb s1 E s2' EEp') ==>
       (s2 = s2') /\ (EEp = EEp')`--),
  my_special_tactic))
