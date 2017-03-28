(* =====================================================================*)
(* FILE          : hol_queries.sml                                      *)
(* DESCRIPTION   : test functions and queries specifically useful in    *)
(*                 hol90.                                               *)
(*                                                                      *)
(* AUTHOR        : Elsa Gunter                                          *)
(*                                                                      *)
(* DATE          : 94.10.11                                             *)
(*                                                                      *)
(* =====================================================================*)

(* Copyright 1994 by AT&T Bell Laboratories *)
(* Share and Enjoy *)

signature Hol_queries_sig =
  sig
    val mk_theory_db : string -> Orsml.co
    val mk_all_theories_db : unit -> Orsml.co
    val type_test : (hol_type -> bool) -> HolDbData.hol_theory_data -> bool
    val term_test : (term -> bool) -> HolDbData.hol_theory_data -> bool
    val thm_test : (thm -> bool) -> HolDbData.hol_theory_data -> bool
    val db_find_thms : {test:thm -> bool, theory:string} -> Orsml.co
    val db_find_all_thms : (thm -> bool) -> Orsml.co
    val find_match : {pattern:term, term:term} -> term subst * hol_type subst
    val seek : {pattern:term, theory:string} -> HolDbData.hol_theory_data list
    val seek_all : term -> HolDbData.hol_theory_data list
  end

structure Hol_queries:Hol_queries_sig =
struct
open Rsyntax; (* use records *)
(*
   Turning theories into complex objects (ie databases) is moderately
   expensive.  Therefore for ancestor theories, we will cache to result
   and use the cache version on all subsequent calls.
*)

val theory_db_cache = ref([]:(string * Orsml.co)list)

(*
   We don't cache the current theory, but look it up each time.  If we could
   tell somehow whether the current theory had been altered, then we could 
   cache the current theory as well, and only recompute it when it has been
   change.  Aslo, there are no duplicates in a theory.  Therefore, we don't
   need duplicate elimination.  This will speed up the initial construction.
*) 
fun mk_theory_db thy =

    if thy = current_theory ()
	then Orsml.mksetco(map Orsml.mkbaseco
			       (HolDbData.theory_to_data thy))
    else
	(#2(Lib.first (fn (name,db) => name = thy) (!theory_db_cache))
	 handle HOL_ERR _ =>
	     let val hold = !Orsml.Dup_elim
		 val thy_db =
		 Orsml.mksetco(map Orsml.mkbaseco
				   (HolDbData.theory_to_data thy))
		 val _ = theory_db_cache := (thy,thy_db) :: (!theory_db_cache)
		 val _ = Orsml.Dup_elim := hold
	     in
		 thy_db
	     end)

(*
   We don't know if the current_theory has been changed, so we need to remake
   the union every time.  We do know there are no duplicates among theories,
   provided there are not duplicated theories, so again we don't need
   duplicate elimination.
*)

fun mk_all_theories_db () =
    let val hold = !Orsml.Dup_elim
	val db = 
	    fold (fn (thy,db)=> Orsml.union (mk_theory_db thy,db))
	         (Lib.mk_set ((Theory.current_theory())::
			      Theory.ancestry (Theory.current_theory())))
		 Orsml.empty
	val _ = Orsml.Dup_elim := hold
    in
	db
    end

fun type_test test (HolDbData.Type ty) = test ty
  | type_test test _ = false

fun term_test test (HolDbData.Term tm) = test tm
  | term_test test (HolDbData.Constant {constant,...}) = test constant
  | term_test test (HolDbData.Infix {constant,...}) = test constant
  | term_test test (HolDbData.Binder {constant,...}) = test constant
  | term_test test _ = false

fun thm_test test (HolDbData.Thm thm) = test thm
  | thm_test test (HolDbData.Axiom {theorem = (_,thm),...}) = test thm
  | thm_test test (HolDbData.Definition {theorem = (_,thm),...}) = test thm
  | thm_test test (HolDbData.StoredThm {theorem = (_,thm),...}) = test thm
  | thm_test test _ = false

fun db_find_thms {test, theory} =
    Set.select (Orsml.apply_test (thm_test test)) (mk_theory_db theory);

fun db_find_all_thms test =
    fold (fn (theory,co) => Orsml.union 
	  (db_find_thms {test = test, theory = theory},co))
    ((Theory.current_theory())::Theory.ancestry (Theory.current_theory()))
    Orsml.empty


(* find_match was in the original system *)

(* try to match PATTERN against a subterm of TERM, return the term
   & hol_type substitutions that make PATTERN match the subterm *)

fun find_match {pattern, term} =
    let 
	fun find_match_aux term =
	    match_term pattern term
	    handle HOL_ERR _ =>
		find_match_aux (#Body(dest_abs term))
		handle HOL_ERR _ =>
		    find_match_aux (rator term)
		    handle HOL_ERR _ =>
			find_match_aux (rand term)
			handle HOL_ERR _ =>
			    raise HOL_ERR
                                    {origin_structure = "Hol_queries",
				     origin_function = "find_match",
				     message = "no match"}
    in
	find_match_aux term
    end

fun seek {pattern, theory} =
    map Orsml.DEST.co_to_base (Orsml.DEST.co_to_list
    (db_find_thms {test = (fn thm =>
			  (Lib.can find_match {pattern = pattern,
					       term = concl thm})),
		  theory = theory}))
fun seek_all pattern =
    map Orsml.DEST.co_to_base (Orsml.DEST.co_to_list
    (db_find_all_thms (fn thm =>
		      (Lib.can find_match {pattern = pattern,
					   term = concl thm}))))

end;

