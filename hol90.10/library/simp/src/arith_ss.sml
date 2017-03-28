(* ---------------------------------------------------------------------
 * A symbolic calculator for the HOL "num" arithmetic.  Does no proof - it
 * relies on some other tool to do the proof.  See arith_ss.sml.
 *
 * When using this with natural arithmetic, note that
 * the fact that m-n=0 for n>m is not taken into account.  It assumes that
 * subtraction is always being used in a "well behaved" way.
 * --------------------------------------------------------------------*)
structure arith_ss : arith_ss_sig =
struct

type conv = Abbrev.conv;

open liteLib arithLib reduceLib;
open Lib Exception CoreHol;
open Term Dsyntax Thm Drule Conv Parse Psyntax
open LiteLib Arith_cons Arith Simplifier Equal Traverse Cache Trace;

val _ = say "Loading arithmetic simplification tools...";

(* ---------------------------------------------------------------------
 * LIN: Linear arithmetic expressions
 * --------------------------------------------------------------------*)

val mk_numeral = term_of_int;
val dest_numeral = int_of_term;

datatype lin = LIN of ((term * int) list * int);

fun string_ord (s1:string,s2) = if s1 < s2 then LESS
                                else if s1 > s2 then GREATER
                                                else EQUAL;

fun term_ord (t1,t2) =
    if is_var t1 then
	if is_var t2 then (string_ord (fst(dest_var t1),fst(dest_var t2)))
	else LESS
    else if is_const t1
         then if is_var t2 then GREATER
	      else if is_const t2
                   then (string_ord (fst(dest_const t1),fst(dest_const t2)))
	           else LESS
    else if is_comb t1 then
        if is_var t2 orelse is_const t2 then GREATER
        else if is_comb t2 then
           case term_ord (rator t1,rator t2) of
	       EQUAL => term_ord (rand t1,rand t2)
	     | x => x
	else LESS
    else if is_abs t1 then
        if is_var t2 orelse is_const t2 orelse is_comb t2 then GREATER
        else if is_comb t2 then
           case term_ord (bvar t1,bvar t2) of
	       EQUAL => term_ord (body t1,body t2)
	     | x => x
	else LESS
    else failwith "term_ord";

val zero_tm = (--`0`--);
fun dest_SUC tm =
    if (fst(dest_const(rator tm)) = "SUC") then rand tm else fail();
val num_ty = (==`:num`==);

val mk_lin =
  let fun tmord ((term1,n1:int),(term2,n2)) =
      case term_ord (term1,term2) of
        EQUAL => if n1 < n2 then LESS else if n2 > n1 then GREATER else EQUAL
      | x => x;
      val tmlt = lt_of_ord tmord;
      fun shrink_likes ((tm1,k1)::(tm2,k2)::rest) =
        if (tm1 = tm2) then
          if (k1+k2 = 0) then shrink_likes rest
          else shrink_likes ((tm1,k1+k2)::rest)
        else (tm1,k1)::shrink_likes((tm2,k2)::rest)
        | shrink_likes x = x
      val canon_tms = shrink_likes o sort (curry tmlt)
      fun mk_tm (tm,0) = failwith "mk_tm: zero term"
        | mk_tm (tm,k) = (tm,k)
  in fn (k,x) => LIN (canon_tms (mapfilter mk_tm k),x)
  end;

fun dest_lin (LIN p) = p;

(* ---------------------------------------------------------------------
 * LIN <--> HOL
 * --------------------------------------------------------------------*)

fun is_pos_tm (tm,n) = n > 0
fun is_neg_tm (tm,n) = n < 0

fun term_of_tm (tm,n) =
   if (abs n = 1) then tm
   else mk_mult (mk_numeral (abs n),tm);


val list_mk_plus = end_foldr mk_plus;
val list_mk_mult = end_foldr mk_mult;

fun term_of_lin (LIN (tms,k)) =
  let val pos_terms = map term_of_tm (filter is_pos_tm tms)
      val neg_terms =
        (map term_of_tm (filter is_neg_tm tms))@
        (if k < 0 then [mk_numeral (~k)] else [])
      val const_term = if k > 0 then SOME (mk_numeral k) else NONE
  in
      case const_term of
	  SOME x =>
	      if (null pos_terms) then
		  if (null neg_terms) then x
		  else mk_minus(x,list_mk_plus neg_terms)
	      else if (null neg_terms) then list_mk_plus(pos_terms@[x])
		   else mk_minus(list_mk_plus (pos_terms@[x]),
                                 list_mk_plus neg_terms)
	| NONE =>
	      if (null pos_terms) then
		  if (null neg_terms) then zero_tm
		  else failwith "no positive terms"
	      else if (null neg_terms) then list_mk_plus pos_terms
		   else mk_minus(list_mk_plus pos_terms,list_mk_plus neg_terms)
  end;

fun negate (x,y:int) = (x,~y);

fun lin_of_term tm =
  let val (t1,t2) = dest_plus tm
      val (l1,k1) = dest_lin(lin_of_term t1)
      val (l2,k2) = dest_lin(lin_of_term t2)
  in mk_lin(l1@l2,k1+k2)
  end
  handle HOL_ERR _ =>
  let val (t1,t2) = dest_minus tm
      val (l1,k1) = dest_lin(lin_of_term t1)
      val (l2,k2) = dest_lin(lin_of_term t2)
  in mk_lin(l1@map negate l2,k1 - k2)
  end
  handle HOL_ERR _ =>
  let val (l1,k1) = dest_lin(lin_of_term (dest_SUC tm))
  in LIN(l1,k1+1)
  end
  handle HOL_ERR _ =>
  mk_lin([],dest_numeral tm)
  handle HOL_ERR _ =>
  mk_lin([(tm,1)],0);


val linear_reduction = term_of_lin o lin_of_term;

(* ---------------------------------------------------------------------
 * is_arith
 *
 * Decide whether something looks like something which may be
 * either decideable by ARITH_CONV or useful for ARITH_CONV.
 *
 * EXAMPLES
 * is_arith (--`~(1 = 2)`--);                      (* true *)
 * is_arith (--`~(LENGTH [1] = 0)`--);             (* true *)
 * is_arith (--`~(x:'a = y)`--);                   (* false *)
 * is_arith (--`!z:num. ~(x:'a = y)`--);           (* false *)
 * is_arith (--`!z:num. ~(z = y)`--);              (* true *)
 * is_arith (--`!P. !z:num. ~(z = y) /\ P`--);     (* true *)
* is_arith (-+`(!i. i < 1 + n' ==> (f i = f' i)) ==> 1 + n > 0`+-);

 * --------------------------------------------------------------------*)
(* there might still be bugs in this.... DRS 5 Aug 96 *)

fun is_arith tm =
   if (is_forall tm) then
       (type_of (bvar (rand tm)) = num_ty andalso is_presburger(body(rand tm)))
   else if is_exists tm then
	(type_of (bvar (rand tm)) = num_ty andalso is_arith (body (rand tm)))
   else if (is_abs tm) then false
   else if (is_geq tm) orelse (is_less tm) orelse
           (is_leq tm) orelse (is_great tm) then  true
   else if (is_conj tm) orelse (is_disj tm) orelse (is_imp tm)
     orelse (is_eq tm andalso type_of (rhs tm) = bool_ty) then
     is_arith (lhand tm) andalso is_arith (rand tm)
   else if (is_neg tm) then is_arith (dest_neg tm)
   else if (is_eq tm) then (type_of (rhs tm) = num_ty)
   else false;


fun is_arith_thm thm = (not (null (hyp thm)) andalso is_arith (concl thm));

(* ---------------------------------------------------------------------
prim_load_library interpret {lib=arith_lib,theory="-"};
 * --------------------------------------------------------------------*)

type ctxt = thm list;
val facts = [`1 < 2`,`1 + x = x + 1`,`x < x + 1`];

val ARITH = EQT_ELIM o ARITH_CONV;

fun CTXT_ARITH thms tm =
  if (type_of tm = bool_ty) andalso (is_arith tm) then
     let val context = map concl thms
         fun try gl =
           let val gl' = list_mk_imp(context,gl)
	   in rev_itlist (C MP) thms (ARITH gl')
           end
	 val thm = EQT_INTRO (try tm)
	     handle HOL_ERR _ => EQF_INTRO (try(mk_neg tm))
     in trace(1,PRODUCE(tm,"ARITH",thm)); thm
     end
   else if (type_of tm = num_ty) then
     let val reduction = linear_reduction tm
     in if (reduction = tm)
        then failwith "CTXT_ARITH: no reduction possible"
        else
          let val context = map concl thms
              val gl = list_mk_imp(context,mk_eq(tm,reduction))
	      val thm = rev_itlist (C MP) thms (ARITH gl)
          in trace(1,PRODUCE(tm,"ARITH",thm)); thm
          end
     end
   else failwith "CTXT_ARITH: not applicable";

val (CACHED_ARITH,arith_cache) =
  let fun check tm =
      let val ty = type_of tm
      in (ty = num_ty orelse (ty=bool_ty andalso is_arith tm))
      end;
  in  CACHE (check,CTXT_ARITH)
  end;


(* ---------------------------------------------------------------------
 * --------------------------------------------------------------------*)

val ARITH_REDUCER =
  let exception CTXT of thm list;
      fun get_ctxt e = (raise e) handle CTXT c => c;
  in REDUCER {addcontext= fn (ctxt, newthms) =>
              CTXT ((filter is_arith_thm
                     (flatten (map CONJUNCTS newthms)))@get_ctxt ctxt),
              apply=fn args => CACHED_ARITH (get_ctxt (#context args)),
              initial=CTXT []}
  end;

fun mk_redconv pat = {name = "REDUCE_CONV (arithmetic reduction)",
                      trace = 2,
                      key = SOME([], pat),
                      conv = K (K (CHANGED_CONV Redconv.REDUCE_CONV))}

val ARITH_ss = Simplifier.SIMPSET
    {convs = [mk_redconv (--`a * b`--),
              mk_redconv (--`a EXP b`--),
	      mk_redconv (--`a DIV b`--),
	      mk_redconv (--`a MOD b`--)],
     rewrs = [ARITH (--`!x y. (x + 1 = y + 1) = (x = y)`--)],
     congs = [],
     filter = NONE,
     ac = [],
     dprocs = [ARITH_REDUCER]};

fun clear_arith_caches() = clear_cache arith_cache;

open Simpsets;

val HOL_ss = merge_ss [BOOL_ss, CONG_ss, LIST_ss, COMBIN_ss, SATISFY_ss,
                       NOT_ss, UNWIND_ss, ARITH_ss, PAIR_ss, SUM_ss];

val hol_ss = mk_simpset [HOL_ss];;

val _ = say "done!\n";



end (* struct *)



