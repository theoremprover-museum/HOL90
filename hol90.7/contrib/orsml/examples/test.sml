(* File: <HOLdir>/contrib/orsml/examples/test.sml *)

val _ = new_theory "ttree";

val _ = load_library_in_place(find_library "orsml");

val _ = load_library_in_place(find_library "nested_rec");

local
    structure ttree : NestedRecTypeInputSig =
	struct
	    structure DefTypeInfo = DefTypeInfo
	    open DefTypeInfo
(* ttree = Leaf of 'a | Node of (('a ttree) list)) *)
	    val def_type_spec =
		[{type_name = "ttree",
		  constructors =
		  [{name = "Lf", arg_info = [existing (==`:'a`==)]},
		   {name = "Nd",
		    arg_info =
		    [type_op {Tyop = "list",
			      Args = [being_defined "ttree"]}]}]}]
	    val recursor_thms = [theorem "list" "list_Axiom"]
	    val New_Ty_Existence_Thm_Name = "ttree_existence"
	    val New_Ty_Induct_Thm_Name = "ttree_induct"
	    val New_Ty_Uniqueness_Thm_Name = "ttree_unique"
	    val Constructors_Distinct_Thm_Name = "ttree_distinct"
	    val Constructors_One_One_Thm_Name = "ttree_one_one"
	    val Cases_Thm_Name = "ttree_cases"
	end
in
    structure ttree_Def = NestedRecTypeFunc (ttree)
end;


fun get_existential thm =
    let val thm1 = SPEC_ALL thm
    in if is_exists (concl thm1) then thm1 else EXISTENCE thm1
    end

fun universal_types tm = map type_of (#1 (strip_forall tm));

fun existential_types tm = map type_of (#1 (strip_exists tm))

fun dest_fun_ty ty =
    let
	val {Tyop, Args} = dest_type ty
    in if Tyop = "fun" then {Range = hd(tl Args), Domain = hd Args}
	else raise HOL_ERR{message = "Not a function type", 
			   origin_function = "dest_fun_ty",
			   origin_structure = "top"}
    end

fun final_range ty =
    (let val {Range,...} = dest_fun_ty ty
     in final_range Range
     end) handle HOL_ERR _ => ty


local
fun dest_curried_aux (info as {hd,args}) =
    if is_comb hd
	then
	    let val {Rator,Rand} = dest_comb hd
	    in dest_curried_aux {hd = Rator,args = Rand::args}
	    end
    else info
in
fun dest_curried_app tm = dest_curried_aux{hd=tm,args=[]}
end;


fun dest_existential ethm =
    let val (funs, conjuncts) = strip_exists (concl ethm)
	val etys = map ((#Domain) o dest_fun_ty o type_of) funs
	val fun_clauses =
	    map (lhs o (#2) o strip_forall) (strip_conj conjuncts)
	val constructors =
	    map (fn tm =>
		 let val {Rator,Rand} = dest_comb tm
		     val {hd,args} = dest_curried_app Rand
		 in if exists (fn f => f = Rator) funs
		     andalso is_const hd andalso all is_var args
			then hd
		    else raise HOL_ERR
			{origin_structure = "top",
			 origin_function = "dest_existential",
			 message = "Not a theorem of existence."}
		 end)
	    fun_clauses
    in {etys = etys, constructors = constructors}
    end;


local
fun is_exists_unique_for ty tm =
    (let val {Name,Ty} = dest_const(rator tm)
	 val dty = #Domain(dest_fun_ty
                   (#Domain(dest_fun_ty
                   (#Domain(dest_fun_ty Ty)))))
     in Name = "?!" andalso can (match_type dty) ty
     end) handle HOL_ERR _ => false
in
fun is_initial_theorem_for ty
                           (HolDbData.StoredThm {theorem=(_,orig_thm),...}) =
    is_exists_unique_for ty (concl(SPEC_ALL orig_thm))
  | is_initial_theorem_for _ _ = false
end;

fun is_existential_for ty (HolDbData.StoredThm {theorem=(_,orig_thm),...}) =
    let val ethm = SPEC_ALL orig_thm
	val ety = existential_types(concl ethm)
    in
	 case ety of [] => false
                   | _ => 
		(all (can dest_fun_ty) ety
		 andalso
		 exists (fn fty => let val {Range,Domain} = dest_fun_ty fty
				   in (can (match_type Domain) ty) andalso
				       is_vartype Range
				   end)
		 ety
		 andalso
		 fold
		 (fn (tm,b) => b andalso  is_eq(#2(strip_forall tm)))
		 (strip_conj (#2(strip_exists(concl ethm))))
		 true)
		handle HOL_ERR _ => false
    end
  | is_existential_for _ _ = false;

fun is_uniqueness_for (HolDbData.StoredThm {theorem=(_,ex_thm),...})
                              (HolDbData.StoredThm {theorem=(_,u_thm),...}) =
    (let val body = #2(strip_exists(#2(strip_forall (concl ex_thm))))
	 val (clauses,eqs) = strip_imp(#2(strip_forall(concl u_thm)))
     in all (fn tm => can (match_term tm) body) clauses andalso
	 all (fn eq =>
	      let val {lhs,rhs} = dest_eq eq
	      in is_var lhs andalso is_var rhs end)
	 (strip_conj eqs)
     end handle HOL_ERR _ => false)
  | is_uniqueness_for _ _ = false

    

fun is_induction_for (HolDbData.StoredThm {theorem=(_,init_thm),...})
                     (HolDbData.StoredThm {theorem=(_,ind_thm),...}) =
    (let val {constructors, etys} =
	 dest_existential (get_existential init_thm)
	 val (Uvars,Body) = strip_forall (concl ind_thm)
	 val {ant=ind_hyps,conseq=ind_concl} = dest_imp Body
     in
	 set_eq (map type_of Uvars)
	        (map (fn ty => mk_type{Tyop="fun",Args=[ty,bool]}) etys)
	 andalso
	 all (fn tm =>
	      let val {Bvar, Body} = dest_forall tm
		  val {Rator,Rand} = dest_comb Body
	      in Bvar = Rand andalso Lib.mem Rator Uvars
	      end)
	 (strip_conj ind_concl)
	 andalso
	 all (fn tm =>
	      let val {Rator,Rand} =
		  dest_comb(#2(strip_imp(#2(strip_forall tm))))
		  val {hd,args} = dest_curried_app Rand
	      in Lib.mem Rator Uvars andalso Lib.mem hd constructors
	      end)
	 (strip_conj ind_hyps)

     end handle  _ => false)
  | is_induction_for _ _ = false


fun is_cases_for (HolDbData.StoredThm {theorem=(_,ex_thm),...})
                 (HolDbData.StoredThm {theorem=(_,c_thm),...}) =
    (let val {constructors, etys} = dest_existential (get_existential ex_thm)
	 val clauses = map dest_forall (strip_conj(concl c_thm))
     in
	 all (fn {Bvar,Body} =>
	      let val evars_eqs = map strip_exists (strip_disj Body)
	      in all (fn (evars,eq) =>
		      let val {lhs=l,rhs=r} = dest_eq eq
			  val {hd,args} = dest_curried_app r
		      in l = Bvar andalso Lib.mem hd constructors
			  andalso Lib.set_eq args evars
		      end)
		  evars_eqs
	      end)
	 clauses
     end handle HOL_ERR _ => false)
  | is_cases_for _ _ = false


fun is_distinct_constr_for (HolDbData.StoredThm {theorem=(_,ex_thm),...})
                           (HolDbData.StoredThm {theorem=(_,d_thm),...}) =
    (let val {constructors, etys} = dest_existential (get_existential ex_thm)
	 val clauses = map strip_forall (strip_conj(concl d_thm))
     in
	 all (fn (Bvars,Body) =>
	      let val {lhs=l,rhs=r} = dest_eq(dest_neg Body)
		  val {hd=lconst,args=largs} = dest_curried_app l
		  val {hd=rconst,args=rargs} = dest_curried_app r
	      in Lib.mem lconst constructors andalso
		  Lib.mem rconst constructors andalso
		  all (fn x => Lib.mem x Bvars) largs andalso
		  all (fn x => Lib.mem x Bvars) rargs
	      end)
	 clauses
     end handle HOL_ERR _ => false)
  | is_distinct_constr_for _ _ = false


(* Now for more purely database stuff *)

val all_theories_db = Hol_queries.mk_all_theories_db ();

fun is_initial_co_for ty = Orsml.apply_test (is_initial_theorem_for ty)

fun is_existential_co_for ty = Orsml.apply_test (is_existential_for ty)

fun is_uniqueness_co_for thm_co =
    Orsml.apply_test (is_uniqueness_for (Orsml.DEST.co_to_base thm_co))

fun mk_initial_co_for ty =
    Orsml.comp ((Orsml.smap (fn thm => Orsml.mkprodco(thm,Orsml.empty))),
          Set.select (is_initial_co_for ty))

fun mk_exist_uniq_co_for ty thy_db =
    Orsml.smap (fn exists_co =>
		Orsml.mkprodco(exists_co,
			       Set.select
			       (is_uniqueness_co_for exists_co)
			       thy_db))
    (Set.select (is_existential_co_for ty) thy_db)

fun mk_initiality_options ty =
    set_to_or (Orsml.union (mk_initial_co_for ty all_theories_db,
			    mk_exist_uniq_co_for ty all_theories_db))


fun gather_ind_and_cases init_thms_co =
    let val initial_thm = Orsml.DEST.co_to_base (Orsml.p1 init_thms_co)
        val induct_co =
            Set.select
	    (Orsml.apply_test (is_induction_for initial_thm))
	    all_theories_db
        val cases_co =
            Set.select
	    (Orsml.apply_test (is_cases_for initial_thm))
	    all_theories_db
        val distinct_co =
            Set.select
	    (Orsml.apply_test (is_distinct_constr_for initial_thm))
	    all_theories_db
        val info = Orsml.mkprodco (induct_co,
				   Orsml.union(cases_co, distinct_co))
    in Orsml.mkprodco (init_thms_co, info)
    end

fun mk_full_induction_options ty =
    Orsml.orsmap gather_ind_and_cases (mk_initiality_options ty)

fun fold_induction_options [] = Orsml.bang Orsml.empty
  | fold_induction_options (hd_ty :: tl_tys) =
    let val new_options = mk_full_induction_options hd_ty
    in Orsml.cond(Orsml.eq(new_options, Orsml.orempty),
            (fn rem_co => Orsml.mkprodco(Orsml.bang Orsml.empty,rem_co)),
            (fn rem_co => Orsml.mkprodco(new_options,rem_co)))
           (fold_induction_options tl_tys)
    end

fun goal_induction_options goal =
    Orsml.normal (fold_induction_options (universal_types goal));

val poss_ind = goal_induction_options
    (--`!(n:num) l. ((Nd (CONS (Lf n) l)) = Nd (APPEND l [(Lf n)])) =
              (EVERY (\x. x = Lf n) l)`--);

