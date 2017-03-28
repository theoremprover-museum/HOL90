(* File: <HOLdir>/contrib/orsml/examples/ex1.sml *)

val _ = load_library_in_place (find_library "orsml");

val _ = use (!HOLdir^"contrib/orsml/src/sr.lib");

fun proper_disjoint_subterms tm =
    if is_var tm orelse is_const tm then Orsml.orsng(Orsml.empty)
    else if is_abs tm then disjoint_subterms (#Body(dest_abs tm))
	else Orsml.orsmap
	    Orsml.flat
	    (Orsml.alpha (Orsml.union
			  (Orsml.sng (disjoint_subterms (rator tm)),
			   Orsml.sng (disjoint_subterms (rand tm)))))
and disjoint_subterms tm =
    Orsml.orunion (Orsml.orsng(Orsml.sng(Orsml.mkbaseco(HolDbData.Term tm))),
		   proper_disjoint_subterms tm)


fun exists test [] = false
  | exists test (x::xs) = test x orelse exists test xs

fun is_rewr {term, eq} =
    if is_eq eq then can (fn tm => match_term (lhs eq) tm) term
    else if is_forall eq
	     then is_rewr {term = term, eq = #2 (strip_forall eq)}
	 else if is_conj eq
		  then exists (fn eq => is_rewr {term = term, eq =eq})
		              (strip_conj eq)
	      else false

fun is_cond_rewr {term, cond_eq} =
    if is_eq cond_eq then can (fn tm => match_term (lhs cond_eq) tm) term
    else if is_forall cond_eq
	     then is_cond_rewr {term = term,
				cond_eq = #2 (strip_forall cond_eq)}
	 else if is_conj cond_eq
		  then exists (fn cond_eq => is_cond_rewr {term = term,
							   cond_eq =cond_eq})
		              (strip_conj cond_eq)
	      else if is_imp cond_eq
		       then is_cond_rewr {term = term,
					  cond_eq = #conseq(dest_imp cond_eq)}
		   else false;


fun is_rewrite {term, theorem} = is_rewr{term = term, eq = concl theorem}

fun is_cond_rewrite {term, theorem} =
    is_cond_rewr{term = term, cond_eq = concl theorem}


fun Is_rewrite term_co thm =
    (case Orsml.DEST.co_to_base term_co
       of HolDbData.Term tm => is_rewrite {term = tm, theorem = thm}
        | _ => false)

fun Is_cond_rewrite term_co thm =
    (case Orsml.DEST.co_to_base term_co
       of HolDbData.Term tm => is_cond_rewrite {term = tm, theorem = thm}
        | _ => false)

(* Build a database for all ancestor theories. May take a little while. *)
val all_theories_db = Hol_queries.mk_all_theories_db ();

fun maximal_antichain orset =
    Set.orselect
    (fn set => (Orsml.eq(Orsml.orsng set,
			 Set.orselect
			 (fn sbset => Set.subset(sbset,set))
			 orset)))
    orset


fun find_rewrites tm =
    let val disj_subtms = disjoint_subterms tm
    in
	maximal_antichain
	(Orsml.normal
	 (Orsml.orsmap (fn partition => 
		  Orsml.smap (fn term_co =>
			Orsml.mkprodco(term_co,
				       set_to_or
				       (Set.select
					(Orsml.apply_test
					 (Hol_queries.thm_test
					  (Is_rewrite term_co)))
					all_theories_db)))
		  partition)
	  disj_subtms))
    end

(* Find all theorems that could be used for rewriting all subterms of the
 * given term.
 *************************************************************************)
val test = find_rewrites (--`SUC x + 1`--);



(* Find all theorems having a subterm matching the given pattern. *)
Hol_queries.seek_all (--`a + b < c`--);
