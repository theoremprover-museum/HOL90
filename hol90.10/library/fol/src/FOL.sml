(* ========================================================================= 
 * FOL
 * ========================================================================= *)

structure FOL : FOL_sig = 
struct

open liteLib;
open LiteLib;

val offinc = 100000;; (* NB: should be bigger than all variable codes.       *)

    
(* ------------------------------------------------------------------------- *)
(* Shadow syntax for FOL terms in NNF. Functions and predicates have         *)
(* numeric codes, and negation is done by negating the predicate code.       *)
(* ------------------------------------------------------------------------- *)

datatype fol_term = Var of int
                  | Fnapp of int * fol_term list;;

type fol_atom = (int * fol_term list)
datatype fol_form = Atom of (int * fol_term list)
                  | Conj of fol_form * fol_form
                  | Disj of fol_form * fol_form
                  | Forall of int * fol_form;;

(* ------------------------------------------------------------------------- *)
(* A few handy functions on the shadow syntax.                               *)
(* ------------------------------------------------------------------------- *)

fun fol_free_in v tm =
  case tm of
    Var x => x = v
  | Fnapp(_,lis) => Lib.exists (fol_free_in v) lis;;

val fol_frees =
  let fun fol_frees tm acc =
      case tm of
	  Var x => insert x acc
	| Fnapp(_,lis) => Lib.itlist fol_frees lis acc 
  in fn tm => fol_frees tm []
  end;;

fun raw_fol_subst theta tm =
  case tm of
    Var v => (rev_assoc v theta handle Subscript => raise UNCHANGED)
  | Fnapp(f,args) => Fnapp(f,qmap (raw_fol_subst theta) args);;

fun fol_subst theta = qfun_to_fun (raw_fol_subst theta);
    
fun fol_substl theta =
    qfun_to_fun (qmap (raw_fol_subst theta));
    

fun fol_inst theta (at as (p,args)) =
  (p,qmap (raw_fol_subst theta) args)
  handle UNCHANGED => at;;

(* ------------------------------------------------------------------------- *)
(* Stick another instantiation into a list.                                  *)
(* ------------------------------------------------------------------------- *)

val raw_augment_insts =
  let fun augment1 theta (s,x) =
    let val s' = raw_fol_subst theta s 
    in if fol_free_in x s andalso not(s = Var(x)) then
	failwith "augment1: Occurs check"
       else (s',x) 
    end
  in
    fn p => fn insts => p::(qfun_to_fun (qmap (augment1 [p])) insts)
  end;;

fun augment_insts (t,v) insts =
    let val t' = fol_subst insts t
	val p = (t',v)
    in case t' of
	Var(w) => 
	    if w <= v then
		if w = v then insts
                else raw_augment_insts p insts
	    else raw_augment_insts (Var(v),w) insts
      | _ => if fol_free_in v t' then failwith "augment_insts: Occurs check"
	     else raw_augment_insts p insts
    end;;

(* ------------------------------------------------------------------------- 
 * Unification.                                                              
 *
 * fol_unify (Var 1) (Var 2) [];
 *
 * ------------------------------------------------------------------------- *)

fun fol_unify tm1 tm2 sofar =
    case tm1 of
	Var(x) =>
	    (let val tm1' = rev_assoc x sofar 
	     in fol_unify tm1' tm2 sofar
	     end 
		 handle Subscript =>
		     augment_insts (tm2,x) sofar)
  | Fnapp(f1,args1) =>
      case tm2 of
	  Var(y) =>
	      (let val tm2' = rev_assoc y sofar 
	       in fol_unify tm1 tm2' sofar
	       end
		   handle Subscript =>
		       augment_insts (tm1,y) sofar)
	| Fnapp(f2,args2) =>
	      if f1 = f2 then rev_itlist2 fol_unify args1 args2 sofar
	      else failwith "fol_unify: No match";;

(* ------------------------------------------------------------------------- *)
(* Perform instantiation of a formula.                                       *)
(* ------------------------------------------------------------------------- *)

fun form_inst i f =
  case f of
    Conj(f1,f2) => Conj(form_inst i f1,form_inst i f2)
  | Disj(f1,f2) => Disj(form_inst i f1,form_inst i f2)
  | Forall(v,f1) => let val i' = filter (fn x => not (v = Lib.snd x)) i 
		    in Forall(v,form_inst i' f1)
		    end
  | Atom a => Atom(fol_inst i a);;


(* ------------------------------------------------------------------------- *)
(* Test for equality under the pending instantiations.                       *)
(* ------------------------------------------------------------------------- *)

fun fol_eq insts tm1 tm2 =
  case tm1 of
    Var(x) =>
        (let val tm1' = rev_assoc x insts
	 in fol_eq insts tm1' tm2
	 end
	 handle Subscript =>
	     (case tm2 of
		  Var(y) =>
		      (if x = y then true 
		       else (let val tm2' = rev_assoc y insts
			     in tm1 = tm2'
			     end
			     handle Subscript => tm1 = tm2))
		| _ => false))
  | Fnapp(f1,args1) =>
	case tm2 of
	    Var(y) =>
		(let val tm2' = rev_assoc y insts 
		 in fol_eq insts tm1 tm2'
		 end
		 handle Subscript => false)
	  | Fnapp(f2,args2) =>
		if f1 = f2 then all2 (fol_eq insts) args1 args2
		else false;;

fun fol_atom_eq insts (p1,args1) (p2,args2) =
  p1 = p2 andalso all2 (fol_eq insts) args1 args2;;

(* ------------------------------------------------------------------------- 
 * Versions of shadow syntax operations with variable bumping.               
 * ------------------------------------------------------------------------- *)

fun raw_fol_subst_bump offset theta tm =
  case tm of
    Var v => if v < offinc then
               let val v' = v + offset 
	       in rev_assoc v' theta handle Subscript => Var(v')
	       end
             else
               (rev_assoc v theta handle Subscript => raise UNCHANGED)
  | Fnapp(f,args) => Fnapp(f,qmap (raw_fol_subst_bump offset theta) args);;

fun fol_subst_bump offset theta = qfun_to_fun(raw_fol_subst_bump offset theta);

fun fol_inst_bump offset theta (at as (p,args)) =
  (p,qmap (raw_fol_subst_bump offset theta) args)
  handle UNCHANGED => at;;

(* ------------------------------------------------------------------------- 
 * Versions of "augment_insts" and "fol_unify" with variable offsets.        
 *
 * Bumping can be explained as follows: Every time we use a new rule in
 * a search, we allocate a new section of the variable space for the
 * variables that are local to that rule.  "offset" is the current index
 * into that space.  In fol_unify_bump, both the terms may contain
 * variables with index < offinc.  These indicate general variables 
 * not yet bumped up into offset..offset+offinc.
 *
 * After unifying, the local instantiations may be determined by
 * looking for those with index > offset.
 *      val (locin,globin) = qpartition (fn (_,v) => offset <= v) insts allins
 * ------------------------------------------------------------------------- *)

fun augment_insts_bump offset (t,v) insts =
  let val t' = fol_subst_bump offset insts t
      val p = (t',v)
  in case t' of
      Var(w) => 
	  if w <= v then
	      if w = v then insts
	      else raw_augment_insts p insts
	  else raw_augment_insts (Var(v),w) insts
    | _ => 
	  if fol_free_in v t' then failwith "augment_insts_bump: Occurs check"
	  else raw_augment_insts p insts
  end;;

fun fol_unify_bump offset tm1 tm2 sofar =
  case tm1 of
    Var(x) =>
      let val x' = if x < offinc then x + offset else x 
      in let val tm1' = rev_assoc x' sofar in
	      fol_unify_bump offset tm1' tm2 sofar
	 end
         handle Subscript => augment_insts_bump offset (tm2,x') sofar
      end
  | Fnapp(f1,args1) =>
	(case tm2 of
	    Var(y) =>
		let val y' = if y < offinc then y + offset else y 
		in let val tm2' = rev_assoc y' sofar 
		   in fol_unify_bump offset tm1 tm2' sofar
		   end
 	           handle Subscript =>
		       augment_insts_bump offset (tm1,y') sofar
		end
	  | Fnapp(f2,args2) =>
		if f1 = f2 then 
		    rev_itlist2 (fol_unify_bump offset) args1 args2 sofar
		else failwith "fol_unify_bump: No match");



end (* struct *)


