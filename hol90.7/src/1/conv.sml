(* ===================================================================== *)
(* FILE          : conv.sml                                              *)
(* DESCRIPTION   : Many conversions. A conversion is an ML function of   *)
(*                 type :term -> thm. The theorem is an equality whose   *)
(*                 lhs is the argument term. Translated from hol88.      *)
(*                                                                       *)
(* AUTHORS       : (c) Many people at Cambridge:                         *)
(*                        Larry Paulson                                  *)
(*                        Mike Gordon                                    *)
(*                        Richard Boulton and                            *)
(*                        Tom Melham, University of Cambridge plus       *)
(*                     Paul Loewenstein, for hol88                       *)
(* TRANSLATOR    : Konrad Slind, University of Calgary                   *)
(* DATE          : September 11, 1991                                    *)
(* Many micro-optimizations added, February 24, 1992, KLS                *)
(* ===================================================================== *)

structure Conv : Conv_sig =
struct
structure Thm = Base_logic.Thm;
open Base_logic;
open Term_io.Parse;
open Thm;
open Term; 
open Dsyntax;
open Drule;

fun CONV_ERR{function,message} = HOL_ERR{origin_structure = "Conv",
					 origin_function = function,
					 message = message}

(* For term decomposition failure. Not exported. *)
exception BAD_STRUCT;


(* Instantiate terms and types of a theorem				*)
fun INST_TY_TERM(tm_subst,type_subst) th = 
    INST tm_subst (INST_TYPE type_subst th);


(* |- !x y z. w   --->  |- w[g1/x][g2/y][g3/z]   *)
fun GSPEC th =
   let val (_,w) = dest_thm th 
   in if (is_forall w)
      then GSPEC (SPEC (genvar (type_of (#Bvar (dest_forall w)))) th)
      else th
   end;

(* Match a given part of "th" to a term, instantiating "th".
   The part should be free in the theorem, except for outer bound variables.
   (? KLS)
*)
fun PART_MATCH partfn th =
   let val pth = GSPEC (GEN_ALL th)
       val pat = partfn(concl pth)
       val matchfn = Match.match_term pat 
   in
   fn tm => INST_TY_TERM (matchfn tm) pth
   end;

(* ---------------------------------------------------------------------*)
(* Conversion for rewrite rules of the form |- !x1 ... xn. t == u   	*)
(* Matches x1 ... xn : 	 t'  ---->  |- t' == u'   			*)
(* Matches all types in conclusion except those mentioned in hypotheses.*)
(*									*)
(* Rewritten such that the lhs of |- t' = u' is syntactically equal to 	*)
(* the input term, not just alpha-equivalent. 	         [TFM 90.07.11] *)
(*									*)
(* OLD CODE:								*)
(*									*)
(*   let REWRITE_CONV =							*)
(*       set_fail_prefix `REWRITE_CONV`					*)
(*         (PART_MATCH (fst o dest_eq));;				*)
(* ---------------------------------------------------------------------*)
fun REWR_CONV th =
   let val instth = PART_MATCH lhs th 
            handle (HOL_ERR _) => raise CONV_ERR{function = "REWR_CONV",
                            message = "bad theorem argument (not an equation)"}
   in
   fn tm => 
     let val eqn = instth tm
         val l = lhs(concl eqn)
     in if (l = tm) 
        then eqn 
        else TRANS (ALPHA tm l) eqn
     end 
     handle (HOL_ERR _) => raise CONV_ERR{function = "REWR_CONV",
                                 message = "lhs of theorem doesn't match term"}
   end;



(* ---------------------------------------------------------------------*)
(* MATCH_MP: Matching Modus Ponens for implications.			*)
(*									*)
(*    |- !x1 ... xn. P ==> Q     |- P' 					*)
(* ---------------------------------------				*)
(*                |- Q'  						*)
(*									*)
(* Matches all types in conclusion except those mentioned in hypotheses.*)
(*									*)
(* Reimplemented with bug fix [TFM 91.06.17]. 				*)
(* OLD CODE:								*)
(*									*)
(* let MATCH_MP impth =							*)
(*  let match = PART_MATCH (fst o dest_imp) impth ? failwith `MATCH_MP` *)
(*     in								*)
(*     \th. MP (match (concl th)) th;;					*)
(*									*)
(* ---------------------------------------------------------------------*)


(* Pre - JRH version
 * fun MATCH_MP impth =
 *    let val (hy,c) = dest_thm impth
 *        val (vs,imp) = strip_forall c
 *        val pat = #ant(dest_imp imp)
 *                  handle _ => raise CONV_ERR{function = "MATCH_MP",
 *                                             message = "not an implication"}
 *        val fvs = set_diff (free_vars pat) (free_varsl hy)
 *        val gth = GSPEC (GENL fvs (SPECL vs impth))
 *        val matchfn = Match.match_term (#ant(dest_imp(concl gth)))
 *    in
 *    fn th => MP (INST_TY_TERM (matchfn (concl th)) gth) th
 *             handle _ => raise CONV_ERR{function = "MATCH_MP",
 * 				       message = "does not match"}
 *    end;
 *****************************************************************************)
local
val mk_rsubst2 = Lib.map2 (fn r1 => fn r2 => {redex = r2, residue = r1})
fun variants (_,[]) = []
  | variants (av, h::rst) =
      let val vh = variant av h
      in vh::variants (vh::av, rst)
      end
fun rassoc_total x =
   let fun rassc [] = x
         | rassc ({redex,residue}::rst) = 
             if (x=redex) then residue else rassc rst
   in rassc
   end 
fun rassoc_option x =
   let fun rassc [] = NONE
         | rassc ({redex,residue}::rst) = 
             if (x=redex) then (SOME residue) else rassc rst
   in rassc
   end
fun req{redex,residue} = (redex=residue);
in
fun MATCH_MP ith =
    let val bod = #ant(Dsyntax.dest_imp(snd(strip_forall(concl ith))))
    in
    fn th =>
      let val mfn = C Match.match_term (concl th)
          val tth = INST_TYPE (snd(mfn bod)) ith
          val tbod = #ant(dest_imp(snd(strip_forall(concl tth))))
          val tmin = fst(mfn tbod)
          val hy1 = free_varsl(hyp tth) 
          and hy2 = free_varsl(hyp th)
          val (avs,{ant,conseq}) = (I ## dest_imp) (strip_forall (concl tth))
          val (rvs,fvs) = partition (C free_in ant) (free_vars conseq)
          val afvs = Lib.set_diff fvs (Lib.set_diff hy1 avs)
          val cvs = free_varsl (map (C rassoc_total tmin) rvs)
          val vfvs = mk_rsubst2 (variants (cvs@hy1@hy2, afvs)) afvs
          val atmin = (filter (op not o op req) vfvs)@tmin
          val (spl,ill) = partition (C mem avs o #redex) atmin
          val fspl = map (C rassoc_total spl) avs
          val mth = MP (SPECL fspl (INST ill tth)) th
          fun loop [] = []
            | loop (tm::rst) = 
                (case (rassoc_option tm vfvs)
                   of NONE => loop rst
                    | (SOME x) => x::(loop rst))
      in
      GENL (loop avs) mth 
      end 
    end
end;


(* ---------------------------------------------------------------------*)
(* RAND_CONV conv "t1 t2" applies conv to t2				*)
(* 									*)
(* Added TFM 88.03.31							*)
(* Revised TFM 91.03.08							*)
(* Revised RJB 91.04.17							*)
(* ---------------------------------------------------------------------*)
fun RAND_CONV conv tm =
   let val {Rator,Rand} = dest_comb tm handle (HOL_ERR _) 
                          => raise CONV_ERR{function = "RAND_CONV",
				            message = "not a comb"}
   in AP_TERM Rator (conv Rand)
      handle (HOL_ERR _) => raise CONV_ERR{function = "RAND_CONV", message=""}
   end


(* ---------------------------------------------------------------------*)
(* RATOR_CONV conv "t1 t2" applies conv to t1				*)
(* 									*)
(* Added TFM 88.03.31							*)
(* Revised TFM 91.03.08							*)
(* Revised RJB 91.04.17							*)
(* ---------------------------------------------------------------------*)
fun RATOR_CONV conv tm =
   let val {Rator,Rand} = dest_comb tm handle (HOL_ERR _) 
                          => raise CONV_ERR{function = "RATOR_CONV",
				            message = "not a comb"}
   in AP_THM (conv Rator) Rand 
   handle (HOL_ERR _) => raise CONV_ERR{function = "RATOR_CONV", message = ""}
   end
   

(* ---------------------------------------------------------------------*)
(* ABS_CONV conv "\x. t[x]" applies conv to t[x]			*)
(* 									*)
(* Added TFM 88.03.31							*)
(* Revised RJB 91.04.17							*)
(* ---------------------------------------------------------------------*)
fun ABS_CONV conv tm =
   let val {Bvar,Body} = dest_abs tm handle (HOL_ERR _) 
                         => raise CONV_ERR{function = "ABS_CONV",
				           message = "not an abs"}
   in ABS Bvar (conv Body)
      handle (HOL_ERR _) => raise CONV_ERR{function = "ABS_CONV", message=""}
   end;

(*Conversion that always fails;  identity element for ORELSEC *)
fun NO_CONV _ = raise CONV_ERR{function = "NO_CONV", message = ""};

(* Conversion that always succeeds, using reflexive law:   t --->  |- t==t
   Identity element for THENC 
*)
val ALL_CONV  =  REFL;


infix THENC;
infix ORELSEC;

(* Apply two conversions in succession;  fail if either does*)
fun conv1 THENC conv2: conv = fn t => 
   let val th1 = conv1 t
   in
   TRANS th1 (conv2 (rhs (concl th1)))
   end;

(* Apply conv1;  if it fails then apply conv2 *)
fun conv1 ORELSEC conv2 =
    fn t =>  (conv1 t handle (HOL_ERR _) => conv2 t);


(*Perform the first successful conversion of those in the list*)
fun FIRST_CONV [] tm = NO_CONV tm 
  | FIRST_CONV (c::rst) tm = c tm handle (HOL_ERR _) => FIRST_CONV rst tm;

(* Perform every conversion in the list *)
fun EVERY_CONV convl tm = 
   itlist (curry (op THENC)) convl ALL_CONV tm 
   handle _ => raise CONV_ERR{function = "EVERY_CONV", message = ""};


(*Apply a conversion zero or more times*)
fun REPEATC conv t = ((conv THENC (REPEATC conv)) ORELSEC ALL_CONV) t;

(*Cause the conversion to fail if it does not change its input*)
fun CHANGED_CONV conv tm =
   let val th = conv tm 
       val {lhs, rhs} = dest_eq (concl th) 
   in
   if (aconv lhs rhs)
   then raise CONV_ERR{function = "CHANGED_CONV", message = ""}
   else th 
   end;


fun TRY_CONV conv = conv ORELSEC ALL_CONV;

(* Apply conv to all top-level subterms of a term.
  Old version with over-subtle treatment of bound variables:

fun SUB_CONV conv tm =
    if is_comb tm then
       let val (rator,rand) = dest_comb tm in
          MK_COMB (conv rator, conv rand)) 
       end
    else if is_abs tm then
       let val (bv,body) = dest_abs t 
	   val gv = genvar(type_of bv) 
           val bodyth = conv (subst [gv,bv] body) 
           val bv' = variant (thm_free_vars bodyth) bv in
	MK_ABS (GEN bv' (INST [bv',gv] bodyth)))
       end
    else (ALL_CONV tm);
*)

fun SUB_CONV conv tm =
   if (is_comb tm)
   then let val {Rator,Rand} = dest_comb tm
        in MK_COMB(conv Rator, conv Rand)
        end
   else if (is_abs tm)
        then let val {Bvar,Body} = dest_abs tm
             in MK_ABS (GEN Bvar (conv Body))
             end
        else ALL_CONV tm;

(* ===================================================================== *)
(* Section for defining depth conversions                 [RJB 91.04.17] *)
(* ===================================================================== *)
(* ===================================================================== *)
(* Conversions that use failure to indicate that they have not changed	*)
(* their input term, and hence save the term from being rebuilt		*)
(* unnecessarily.							*)
(*									*)
(* Based on ideas of Roger Fleming. Implemented by Richard Boulton.	*)
(* =====================================================================*)

(* ---------------------------------------------------------------------*)
(* Failure string indicating that a term has not been changed by the	*)
(* conversion applied to it.						*)
(* ---------------------------------------------------------------------*)

exception UNCHANGED;

(* ---------------------------------------------------------------------*)
(* QCONV : conv -> conv							*)
(*									*)
(* Takes a conversion that uses failure to indicate that it has not	*)
(* changed its argument term, and produces an ordinary conversion.	*)
(* ---------------------------------------------------------------------*)

fun QCONV conv tm = conv tm
                    handle UNCHANGED => REFL tm;

(* ---------------------------------------------------------------------*)
(* ALL_QCONV : conv							*)
(*									*)
(* Identity conversion for conversions using failure.			*)
(* ---------------------------------------------------------------------*)

val ALL_QCONV:conv = fn _ => raise UNCHANGED;

(* ---------------------------------------------------------------------*)
(* THENQC : conv -> conv -> conv					*)
(*									*)
(* Takes two conversions that use failure and produces a conversion that*)
(* applies them in succession. The new conversion also uses failure. It	*)
(* fails if neither of the two argument conversions cause a change.	*)
(* ---------------------------------------------------------------------*)

fun THENQC conv1 conv2 tm =
   let val th1 = conv1 tm
   in  
   TRANS th1 (conv2 (rhs (concl th1)))
   handle UNCHANGED => th1
   end
   handle UNCHANGED => conv2 tm;

(* ---------------------------------------------------------------------*)
(* ORELSEQC : conv -> conv -> conv					*)
(*									*)
(* Takes two conversions that use failure and produces a conversion that*)
(* tries the first one, and if this fails for a reason other than that	*)
(* the term is unchanged, it tries the second one. A dummy theorem	*)
(* (TRUTH) is used to allow the `qconv' failure to propagate, but not	*)
(* other kinds of failure.						*)
(* ---------------------------------------------------------------------*)

fun ORELSEQC conv1 conv2 (tm:term) =
   let val (th,real_thm) = 
          (conv1 tm,true) 
          handle UNCHANGED => (TRUTH,false) | _ => (conv2 tm,true)
               
(*               | (HOL_ERR _) => (conv2 tm,true) *)
   in if real_thm 
      then th 
      else raise UNCHANGED
   end;

(* ---------------------------------------------------------------------*)
(* REPEATQC : conv -> conv						*)
(*									*)
(* Applies a conversion zero or more times.				*)
(* ---------------------------------------------------------------------*)

fun REPEATQC conv tm = ORELSEQC (THENQC conv (REPEATQC conv)) ALL_QCONV tm;

(* ---------------------------------------------------------------------*)
(* CHANGED_QCONV : conv -> conv						*)
(*									*)
(* Causes the conversion given to fail if it does not change its input.	*)
(* Alpha convertibility is only tested for if the term is changed in	*)
(* some way.								*)
(* ---------------------------------------------------------------------*)
val CHANGED_QCONV_ERR = CONV_ERR{function="CHANGED_QCONV",message = ""}
fun CHANGED_QCONV conv (tm:term) =
   let val th = conv tm 
                handle UNCHANGED => raise CHANGED_QCONV_ERR
       val {lhs,rhs} = dest_eq (concl th)
   in
   if (aconv lhs rhs)
   then raise CHANGED_QCONV_ERR
   else th
   end;

(* ---------------------------------------------------------------------*)
(* TRY_QCONV : conv -> conv						*)
(*									*)
(* Applies a conversion, and if it fails, raises a `qconv' failure	*)
(* indicating that the term is unchanged.				*)
(* ---------------------------------------------------------------------*)

fun TRY_QCONV conv = ORELSEQC conv ALL_QCONV;

(* ---------------------------------------------------------------------*)
(* SUB_QCONV : conv -> conv						*)
(*									*)
(* Applies conv to all top-level subterms of a term. Set up to detect	*)
(* `qconv' failures when dealing with a combination. If neither the 	*)
(* rator nor the rand are modified the `qconv' failure is propagated.	*)
(* Otherwise, the failure information is used to avoid unnecessary	*)
(* processing.								*)
(* ---------------------------------------------------------------------*)

fun SUB_QCONV conv tm =
  case (Term.dest_term tm)
  of (COMB{Rator,Rand}) =>
        (let val th = conv Rator
         in  MK_COMB (th, conv Rand)
             handle UNCHANGED => AP_THM th Rand
         end
         handle UNCHANGED => AP_TERM Rator (conv Rand))
   | (LAMB{Bvar,Body}) =>
         let val Bth = conv Body
         in ABS Bvar Bth
            handle _
            => let val v = genvar (type_of Bvar)
                   val th1 = ALPHA_CONV v tm
                   val {rhs,...} = dest_eq(Thm.concl th1)
                   val {Body=Body',...} = dest_abs rhs (* v = Bvar *)
                   val eq_thm' = ABS v (conv Body')
                   val th2 = ALPHA_CONV Bvar(#rhs(dest_eq(concl eq_thm')))
               in TRANS (TRANS th1 eq_thm') th2
               end
         end
   | _ => ALL_QCONV tm;

(*  Pre-August 1993 
 * fun SUB_QCONV conv tm =
 *    if (is_comb tm) 
 *    then let val {Rator,Rand} = dest_comb tm
 *         in
 *            let val th = conv Rator
 *            in  
 *            MK_COMB (th, conv Rand)
 *            handle UNCHANGED => AP_THM th Rand
 *            end
 *            handle UNCHANGED => AP_TERM Rator (conv Rand)
 *         end
 *    else if (is_abs tm) 
 *         then let val {Bvar,Body} = dest_abs tm
 *              in ABS Bvar (conv Body)
 *              end
 * (*               val bodyth = conv Body
 *  *           in 
 *  *           MK_ABS (GEN Bvar bodyth)
 *  *           end
 *  ***)
 *         else ALL_QCONV tm;
 * *)

(* ---------------------------------------------------------------------*)
(* Apply a conversion recursively to a term and its parts.		*)
(* The abstraction around "t" avoids infinite recursion.		*)
(*									*)
(* Old version:								*)
(*									*)
(* letrec DEPTH_CONV conv t =						*)
(*    (SUB_CONV (DEPTH_CONV conv) THENC (REPEATC conv))			*)
(*    t;;								*)
(* ---------------------------------------------------------------------*)

fun DEPTH_QCONV conv tm =
 THENQC (SUB_QCONV (DEPTH_QCONV conv)) (REPEATQC conv) tm;

val DEPTH_CONV = QCONV o DEPTH_QCONV;;

(* ---------------------------------------------------------------------*)
(* Like DEPTH_CONV, but re-traverses term after each conversion		*)
(* Loops if the conversion function never fails				*)
(*									*)
(* Old version:								*)
(*									*)
(* letrec REDEPTH_CONV conv t =						*)
(*    (SUB_CONV (REDEPTH_CONV conv) THENC				*)
(*     ((conv THENC (REDEPTH_CONV conv)) ORELSEC ALL_CONV))		*)
(*    t;;								*)
(* ---------------------------------------------------------------------*)

fun REDEPTH_QCONV conv tm =
 THENQC
 (SUB_QCONV (REDEPTH_QCONV conv))
 (ORELSEQC (THENQC conv (REDEPTH_QCONV conv)) ALL_QCONV)
 tm;

val REDEPTH_CONV = QCONV o REDEPTH_QCONV;;

(* ---------------------------------------------------------------------*)
(* Rewrite the term t trying conversions at top level before descending	*)
(* Not true Normal Order evaluation, but may terminate where		*)
(* REDEPTH_CONV would loop.  More efficient than REDEPTH_CONV for	*)
(* rewrites that throw away many of their pattern variables.		*)
(*									*)
(* Old version:								*)
(*									*)
(* letrec TOP_DEPTH_CONV conv t =					*)
(*    (REPEATC conv  THENC						*)
(*     (TRY_CONV							*)
(*         (CHANGED_CONV (SUB_CONV (TOP_DEPTH_CONV conv)) THENC		*)
(*          TRY_CONV(conv THENC TOP_DEPTH_CONV conv))))			*)
(*    t;;								*)
(*									*)
(* Slower, simpler version (tries conv even if SUB_CONV does nothing)	*)
(*									*)
(* letrec TOP_DEPTH_CONV conv t =					*)
(*    (REPEATC conv  THENC						*)
(*     SUB_CONV (TOP_DEPTH_CONV conv) THENC				*)
(*     ((conv THENC TOP_DEPTH_CONV conv)  ORELSEC ALL_CONV))		*)
(*    t;;								*)
(* ---------------------------------------------------------------------*)

fun TOP_DEPTH_QCONV conv tm =
 THENQC
 (REPEATQC conv)
 (TRY_QCONV
     (THENQC (CHANGED_QCONV (SUB_QCONV (TOP_DEPTH_QCONV conv)))
             (TRY_QCONV (THENQC conv (TOP_DEPTH_QCONV conv)))))
 tm;

val TOP_DEPTH_CONV = QCONV o TOP_DEPTH_QCONV;

(* ---------------------------------------------------------------------*)
(* ONCE_DEPTH_CONV conv tm: applies conv ONCE to the first suitable	*)
(* sub-term(s) encountered in top-down order.				*)
(*									*)
(* Old Version:								*)
(*									*)
(* letrec ONCE_DEPTH_CONV conv tm =					*)
(*        (conv ORELSEC (SUB_CONV (ONCE_DEPTH_CONV conv))) tm;;		*)
(*									*)
(*									*)
(* Reimplemented: TFM 90.07.04 (optimised for speed)			*)
(*									*)
(* This version uses failure to avoid rebuilding unchanged subterms	*)
(* (now superseded by more general use of failure for optimisation).	*)
(*									*)
(* let ONCE_DEPTH_CONV =						*)
(*     letrec ODC conv tm =						*)
(*        conv tm ?							*)
(*        (let l,r = dest_comb tm in					*)
(*             (let lth = ODC conv l in					*)
(* 	         (MK_COMB(lth,ODC conv r)) ? AP_THM lth r) ?		*)
(*             AP_TERM l (ODC conv r)) ?				*)
(*        let v,body = dest_abs tm in					*)
(*        let bodyth = ODC conv body in					*)
(*            MK_ABS (GEN v bodyth) in					*)
(*        \conv tm. ODC conv tm ? REFL tm;;				*)
(* ---------------------------------------------------------------------*)

fun ONCE_DEPTH_QCONV conv tm =
 TRY_QCONV (ORELSEQC conv (SUB_QCONV (ONCE_DEPTH_QCONV conv))) tm;

val ONCE_DEPTH_CONV = QCONV o ONCE_DEPTH_QCONV;;


(* Convert a conversion to a rule *)

fun CONV_RULE conv th = EQ_MP (conv(concl th)) th;


(* Convert a conversion to a tactic *)

local 
val t = --`T`--
in
fun CONV_TAC (conv:conv) :tactic = fn (asl,w) =>
   let val th = conv w
       val {rhs,...} = dest_eq(concl th)
   in
   if (rhs = t)
   then ([], (fn [] => EQ_MP (SYM th) TRUTH))
   else ([(asl,rhs)], fn [th'] => EQ_MP (SYM th) th')
   end
end;

(* Rule and tactic for beta-reducing on all beta-redexes *)

val BETA_RULE = CONV_RULE(DEPTH_CONV BETA_CONV)
and BETA_TAC  = CONV_TAC (DEPTH_CONV BETA_CONV);


(* =====================================================================*)
(* What follows is a complete set of conversions for moving ! and ? into*)
(* and out of the basic logical connectives ~, /\, \/, ==>, and =.	*)
(*									*)
(* Naming scheme:							*)
(*									*)
(*   1: for moving quantifiers inwards:  <quant>_<conn>_CONV		*)
(*									*)
(*   2: for moving quantifiers outwards: [dir]_<conn>_<quant>_CONV      *)
(*									*)
(* where								*)
(*									*)
(*   <quant> := FORALL | EXISTS						*)
(*   <conn>  := NOT | AND | OR | IMP | EQ				*)
(*   [dir]   := LEFT | RIGHT			(optional)		*)
(*									*)
(*									*)
(* [TFM 90.11.09]							*)
(* =====================================================================*)

(* ---------------------------------------------------------------------*)
(* NOT_FORALL_CONV, implements the following axiom scheme:		*)
(*									*)
(*      |- (~!x.tm) = (?x.~tm)						*)
(*									*)
(* ---------------------------------------------------------------------*)
fun NOT_FORALL_CONV tm =
   let val all = dest_neg tm
       val {Bvar,Body} = dest_forall all
       val exists = mk_exists{Bvar = Bvar, Body = mk_neg Body} 
       val nott = ASSUME (mk_neg Body) 
       val not_all = mk_neg all
       val th1 = DISCH all (MP nott (SPEC Bvar (ASSUME all))) 
       val imp1 = DISCH exists (CHOOSE (Bvar, ASSUME exists) (NOT_INTRO th1)) 
       val th2 = CCONTR Body (MP (ASSUME(mk_neg exists))
                              (EXISTS(exists,Bvar) nott)) 
       val th3 = CCONTR exists (MP (ASSUME not_all) (GEN Bvar th2)) 
   in
   IMP_ANTISYM_RULE (DISCH not_all th3) imp1 
   end
   handle _ => raise CONV_ERR{function = "NOT_FORALL_CONV", message = ""};

(* ---------------------------------------------------------------------*)
(* NOT_EXISTS_CONV, implements the following axiom scheme.		*)
(*									*)
(*	|- (~?x.tm) = (!x.~tm)						*)
(*									*)
(* ---------------------------------------------------------------------*)
fun NOT_EXISTS_CONV tm =
   let val {Bvar,Body} = dest_exists (dest_neg tm) 
       val all = mk_forall{Bvar = Bvar, Body = mk_neg Body}
       val rand_tm = rand tm
       val asm1 = ASSUME Body 
       val thm1 = MP (ASSUME tm) (EXISTS (rand_tm, Bvar) asm1) 
       val imp1 = DISCH tm (GEN Bvar (NOT_INTRO (DISCH Body thm1))) 
       val asm2 = ASSUME  all 
       and asm3 = ASSUME rand_tm
       val thm2 = DISCH rand_tm (CHOOSE (Bvar,asm3) (MP (SPEC Bvar asm2) asm1))
       val imp2 = DISCH all (NOT_INTRO thm2) 
   in
   IMP_ANTISYM_RULE imp1 imp2
   end
   handle _ => raise CONV_ERR{function = "NOT_EXISTS_CONV", message = ""};

(* ---------------------------------------------------------------------*)
(* EXISTS_NOT_CONV, implements the following axiom scheme.		*)
(*									*)
(*	|- (?x.~tm) = (~!x.tm)						*)
(*									*)
(* ---------------------------------------------------------------------*)
fun EXISTS_NOT_CONV tm = 
   let val {Bvar,Body} = dest_exists tm
   in
   SYM(NOT_FORALL_CONV (mk_neg (mk_forall{Bvar = Bvar, Body = dest_neg Body})))
   end
   handle _ => raise CONV_ERR{function = "EXISTS_NOT_CONV", message = ""};

(* ---------------------------------------------------------------------*)
(* FORALL_NOT_CONV, implements the following axiom scheme.		*)
(*									*)
(*	|- (!x.~tm) = (~?x.tm)						*)
(*									*)
(* ---------------------------------------------------------------------*)
fun FORALL_NOT_CONV tm = 
   let val {Bvar,Body} = dest_forall tm
   in
   SYM(NOT_EXISTS_CONV (mk_neg (mk_exists{Bvar = Bvar,Body = dest_neg Body})))
   end
   handle _ => raise CONV_ERR{function = "FORALL_NOT_CONV", message = ""};

(* ---------------------------------------------------------------------*)
(* FORALL_AND_CONV : move universal quantifiers into conjunction.	*)
(*									*)
(* A call to FORALL_AND_CONV "!x. P /\ Q"  returns:			*)
(*									*)
(*   |- (!x. P /\ Q) = (!x.P) /\ (!x.Q)					*)
(* ---------------------------------------------------------------------*)
fun FORALL_AND_CONV tm = 
    let val {Bvar,Body} = dest_forall tm
        val {...} = dest_conj Body
        val (Pth,Qth) = CONJ_PAIR (SPEC Bvar (ASSUME tm)) 
        val imp1 = DISCH tm (CONJ (GEN Bvar Pth) (GEN Bvar Qth)) 
        val xtm = rand(concl imp1) 
        val spec_bv = SPEC Bvar
        val (t1,t2) = (spec_bv##spec_bv) (CONJ_PAIR (ASSUME xtm)) 
    in
    IMP_ANTISYM_RULE imp1 (DISCH xtm (GEN Bvar (CONJ t1 t2)))
    end
    handle _ => raise CONV_ERR{function = "FORALL_AND_CONV", message = ""};

(* ---------------------------------------------------------------------*)
(* EXISTS_OR_CONV : move existential quantifiers into disjunction.	*)
(*									*)
(* A call to EXISTS_OR_CONV "?x. P \/ Q"  returns:			*)
(*									*)
(*   |- (?x. P \/ Q) = (?x.P) \/ (?x.Q)					*)
(* ---------------------------------------------------------------------*)
fun EXISTS_OR_CONV tm = 
   let val {Bvar,Body} = dest_exists tm
       val {disj1,disj2} = dest_disj Body
       val ep = mk_exists{Bvar = Bvar, Body = disj1} 
       and eq = mk_exists{Bvar = Bvar, Body = disj2}
       val ep_or_eq = mk_disj{disj1 = ep, disj2 = eq}
       val aP = ASSUME disj1
       val aQ = ASSUME disj2
       val Pth = EXISTS(ep,Bvar) aP
       and Qth = EXISTS(eq,Bvar) aQ 
       val thm1 = DISJ_CASES_UNION (ASSUME Body) Pth Qth 
       val imp1 = DISCH tm (CHOOSE (Bvar,ASSUME tm) thm1) 
       val t1 = DISJ1 aP disj2 
       and t2 = DISJ2 disj1 aQ 
       val th1 = EXISTS(tm,Bvar) t1 
       and th2 = EXISTS(tm,Bvar) t2 
       val e1 = CHOOSE (Bvar,ASSUME ep) th1 
       and e2 = CHOOSE (Bvar,ASSUME eq) th2 
   in
   IMP_ANTISYM_RULE imp1 (DISCH ep_or_eq (DISJ_CASES (ASSUME ep_or_eq) e1 e2))
   end
   handle _ => raise CONV_ERR{function = "EXISTS_OR_CONV", message = ""};

(* ---------------------------------------------------------------------*)
(* AND_FORALL_CONV : move universal quantifiers out of conjunction.	*)
(*									*)
(* A call to AND_FORALL_CONV "(!x. P) /\ (!x. Q)"  returns:		*)
(*									*)
(*   |- (!x.P) /\ (!x.Q) = (!x. P /\ Q) 				*)
(* ---------------------------------------------------------------------*)

fun AND_FORALL_CONV tm = 
   let val {conj1,conj2} = dest_conj tm
       val {Bvar = x, Body = P} = dest_forall conj1
                                  handle _ => raise BAD_STRUCT
       val {Bvar = y, Body = Q} = dest_forall conj2
                                  handle _ => raise BAD_STRUCT
   in
   if (not (x=y))
   then raise CONV_ERR{function = "AND_FORALL_CONV",
		       message = "forall'ed variables not the same"}
   else let val specx = SPEC x
            val (t1,t2) = (specx##specx) (CONJ_PAIR (ASSUME tm)) 
            val imp1 = DISCH tm (GEN x (CONJ t1 t2)) 
            val rtm = rand(concl imp1) 
            val (Pth,Qth) = CONJ_PAIR (SPEC x (ASSUME rtm)) 
        in
        IMP_ANTISYM_RULE imp1 (DISCH rtm (CONJ (GEN x Pth) (GEN x Qth)))
        end
   end
   handle BAD_STRUCT => raise CONV_ERR{function = "AND_FORALL_CONV",
                                       message = "argument not well-formed"}
        | (e as HOL_ERR{origin_structure = "Conv",
			origin_function = "AND_FORALL_CONV",...}) => raise e
        | e => raise CONV_ERR{function = "AND_FORALL_CONV", message = ""};


(* ---------------------------------------------------------------------*)
(* LEFT_AND_FORALL_CONV : move universal quantifier out of conjunction.	*)
(*									*)
(* A call to LEFT_AND_FORALL_CONV "(!x.P) /\  Q"  returns:		*)
(*									*)
(*   |- (!x.P) /\ Q = (!x'. P[x'/x] /\ Q) 				*)
(* 									*)
(* Where x' is a primed variant of x not free in the input term		*)
(* ---------------------------------------------------------------------*)
fun LEFT_AND_FORALL_CONV tm = 
   let val {conj1,...} = dest_conj tm
       val {Bvar,...} = dest_forall conj1
       val x' = variant (free_vars tm) Bvar 
       val specx' = SPEC x'
       and genx' = GEN x'
       val (t1,t2) = (specx' ## I) (CONJ_PAIR (ASSUME tm)) 
       val imp1 = DISCH tm (genx' (CONJ t1 t2)) 
       val rtm = rand(concl imp1) 
       val (Pth,Qth) = CONJ_PAIR (specx' (ASSUME rtm)) 
   in
   IMP_ANTISYM_RULE imp1 (DISCH rtm (CONJ (genx' Pth)  Qth))
   end
   handle _ => raise CONV_ERR{function = "LEFT_AND_FORALL_CONV", message = ""};

(* ---------------------------------------------------------------------*)
(* RIGHT_AND_FORALL_CONV : move universal quantifier out of conjunction.*)
(*									*)
(* A call to RIGHT_AND_FORALL_CONV "P /\ (!x.Q)"  returns:		*)
(*									*)
(*   |-  P /\ (!x.Q) = (!x'. P /\ Q[x'/x]) 				*)
(* 									*)
(* where x' is a primed variant of x not free in the input term		*)
(* ---------------------------------------------------------------------*)
fun RIGHT_AND_FORALL_CONV tm = 
   let val {conj2, ...} = dest_conj tm
       val {Bvar,...} = dest_forall conj2
       val x' = variant (free_vars tm) Bvar
       val specx' = SPEC x'
       val genx' = GEN x'
       val (t1,t2) = (I ## specx') (CONJ_PAIR (ASSUME tm)) 
       val imp1 = DISCH tm (genx' (CONJ t1 t2)) 
       val rtm = rand(concl imp1) 
       val (Pth,Qth) = CONJ_PAIR (specx' (ASSUME rtm)) 
   in
   IMP_ANTISYM_RULE imp1 (DISCH rtm (CONJ Pth (genx' Qth)))
   end
   handle _ => raise CONV_ERR{function = "RIGHT_AND_FORALL_CONV",
			      message = ""};

(* ---------------------------------------------------------------------*)
(* OR_EXISTS_CONV : move existential quantifiers out of disjunction.	*)
(*									*)
(* A call to OR_EXISTS_CONV "(?x. P) \/ (?x. Q)"  returns:		*)
(*									*)
(*   |- (?x.P) \/ (?x.Q) = (?x. P \/ Q) 				*)
(* ---------------------------------------------------------------------*)
fun OR_EXISTS_CONV tm = 
   let val {disj1,disj2} = dest_disj tm
       val {Bvar = x, Body = P} = dest_exists disj1
       val {Bvar = y, Body = Q} = dest_exists disj2
   in
   if (not (x=y)) 
   then raise CONV_ERR{function = "OR_EXISTS_CONV",
                   message = "existentially quantified variables not the same"}
   else let val aP = ASSUME P
            and aQ = ASSUME Q
            and P_or_Q = mk_disj{disj1 = P, disj2 = Q}
            val otm = mk_exists {Bvar = x, Body = P_or_Q}
            val t1 = DISJ1 aP Q 
            and t2 = DISJ2 P aQ
            val eotm = EXISTS(otm,x)   
            val e1 = CHOOSE (x,ASSUME disj1) (eotm t1)
            and e2 = CHOOSE (x,ASSUME disj2) (eotm t2)
            val thm1 = DISJ_CASES (ASSUME tm) e1 e2 
            val imp1 = DISCH tm thm1 
            val Pth = EXISTS(disj1,x) aP 
            and Qth = EXISTS(disj2,x) aQ 
            val thm2 = DISJ_CASES_UNION (ASSUME P_or_Q) Pth Qth 
        in
        IMP_ANTISYM_RULE imp1 (DISCH otm (CHOOSE (x,ASSUME otm) thm2))
        end
   end
   handle (e as (HOL_ERR{origin_structure = "Conv",
			 origin_function = "OR_EXISTS_CONV",...})) => raise e
        | _ => raise CONV_ERR{function = "OR_EXISTS_CONV", message = ""};

(* ---------------------------------------------------------------------*)
(* LEFT_OR_EXISTS_CONV : move existential quantifier out of disjunction.*)
(*									*)
(* A call to LEFT_OR_EXISTS_CONV "(?x.P) \/  Q"  returns:		*)
(*									*)
(*   |- (?x.P) \/ Q = (?x'. P[x'/x] \/ Q) 				*)
(* 									*)
(* Where x' is a primed variant of x not free in the input term		*)
(* ---------------------------------------------------------------------*)
fun LEFT_OR_EXISTS_CONV tm = 
   let val {disj1,disj2} = dest_disj tm
       val {Bvar,Body} = dest_exists disj1
       val x' = variant (free_vars tm) Bvar 
       val newp = subst[{redex = Bvar, residue = x'}] Body
       val newp_thm = ASSUME newp
       val new_disj = mk_disj {disj1 = newp, disj2 = disj2}
       val otm = mk_exists {Bvar = x', Body = new_disj}
       and Qth = ASSUME disj2
       val t1 = DISJ1 newp_thm disj2 
       and t2 = DISJ2 newp (ASSUME disj2) 
       val th1 = EXISTS(otm,x') t1 
       and th2 = EXISTS(otm,x') t2 
       val thm1 = DISJ_CASES (ASSUME tm) (CHOOSE(x',ASSUME disj1)th1) th2 
       val imp1 = DISCH tm thm1 
       val Pth = EXISTS(disj1,x') newp_thm
       val thm2 = DISJ_CASES_UNION (ASSUME new_disj) Pth Qth 
   in
   IMP_ANTISYM_RULE imp1 (DISCH otm (CHOOSE (x',ASSUME otm) thm2))
   end
   handle _ => raise CONV_ERR{function = "LEFT_OR_EXISTS_CONV", message = ""};

(* ---------------------------------------------------------------------*)
(* RIGHT_OR_EXISTS_CONV: move existential quantifier out of disjunction.*)
(*									*)
(* A call to RIGHT_OR_EXISTS_CONV "P \/ (?x.Q)"  returns:		*)
(*									*)
(*   |-  P \/ (?x.Q) = (?x'. P \/ Q[x'/x]) 				*)
(* 									*)
(* where x' is a primed variant of x not free in the input term		*)
(* ---------------------------------------------------------------------*)
fun RIGHT_OR_EXISTS_CONV tm = 
   let val {disj1,disj2} = dest_disj tm
       val {Bvar,Body} = dest_exists disj2
       val x' = variant (free_vars tm) Bvar 
       val newq = subst[{redex = Bvar, residue = x'}] Body
       val newq_thm = ASSUME newq
       and Pth = ASSUME disj1
       val P_or_newq = mk_disj{disj1 = disj1, disj2 = newq}
       val otm = mk_exists{Bvar = x',Body = P_or_newq}
       val eotm' = EXISTS(otm,x')
       val th1 = eotm' (DISJ2 disj1 newq_thm)
       and th2 = eotm' (DISJ1 Pth newq)
       val thm1 = DISJ_CASES (ASSUME tm) th2 (CHOOSE(x',ASSUME disj2) th1)
       val imp1 = DISCH tm thm1 
       val Qth = EXISTS(disj2,x') newq_thm
       val thm2 = DISJ_CASES_UNION (ASSUME P_or_newq) Pth Qth 
   in
   IMP_ANTISYM_RULE imp1 (DISCH otm (CHOOSE (x',ASSUME otm) thm2))
   end
   handle _ => raise CONV_ERR{function = "RIGHT_OR_EXISTS_CONV", message = ""};

(* ---------------------------------------------------------------------*)
(* EXISTS_AND_CONV : move existential quantifier into conjunction.	*)
(*									*)
(* A call to EXISTS_AND_CONV "?x. P /\ Q"  returns:			*)
(*									*)
(*    |- (?x. P /\ Q) = (?x.P) /\ Q        [x not free in Q]		*)
(*    |- (?x. P /\ Q) = P /\ (?x.Q)        [x not free in P]		*)
(*    |- (?x. P /\ Q) = (?x.P) /\ (?x.Q)   [x not free in P /\ Q]	*)
(* ---------------------------------------------------------------------*)
fun EXISTS_AND_CONV tm =
   let val {Bvar, Body} = dest_exists tm
                          handle _ =>
			      raise CONV_ERR{function = "EXISTS_AND_CONV",
					     message =
					       "expecting `?x. P /\\ Q`"}
       val {conj1,conj2} = dest_conj Body
                           handle _ =>
			       raise CONV_ERR{function = "EXISTS_AND_CONV",
					      message =
					        "expecting `?x. P /\\ Q`"}
       val fP = free_in Bvar conj1 
       and fQ =  free_in Bvar conj2
   in
   if (fP andalso fQ) 
   then raise CONV_ERR{function = "EXISTS_AND_CONV",
                       message = ("`"^(#Name(dest_var Bvar))^
				  "` free in both conjuncts")}
   else let val (t1,t2) = CONJ_PAIR(ASSUME Body) 
            val econj1 = mk_exists{Bvar = Bvar, Body = conj1}
            val econj2 = mk_exists{Bvar = Bvar, Body = conj2}
            val eP = if fQ 
                     then t1
                     else EXISTS (econj1,Bvar) t1
            and eQ = if fP 
                     then t2 
                     else EXISTS (econj2,Bvar) t2
            val imp1 = DISCH tm (CHOOSE(Bvar,ASSUME tm) (CONJ eP eQ)) 
            val th = EXISTS (tm,Bvar) (CONJ(ASSUME conj1) (ASSUME conj2))
            val th1 = if (fP orelse (not fQ))
                      then CHOOSE(Bvar,ASSUME econj1)th 
                      else th
            val thm1 = if (fQ orelse (not fP))
                       then CHOOSE(Bvar,ASSUME econj2)th1
                       else th1
            val otm = rand(concl imp1) 
            val (t1,t2) = CONJ_PAIR(ASSUME otm) 
            val thm2 = PROVE_HYP t1 (PROVE_HYP t2 thm1) 
        in
        IMP_ANTISYM_RULE imp1 (DISCH otm thm2)
        end
   end
   handle (e as HOL_ERR{origin_structure = "Conv",
			origin_function = "EXISTS_AND_CONV",...}) => raise e
        | _ => raise CONV_ERR{function = "EXISTS_AND_CONV", message = ""};

(* ---------------------------------------------------------------------*)
(* AND_EXISTS_CONV : move existential quantifier out of conjunction.	*)
(*									*)
(*   |- (?x.P) /\ (?x.Q) = (?x. P /\ Q) 				*)
(* 									*)
(* provided x is free in neither P nor Q.				*)
(* ---------------------------------------------------------------------*)
local
val AE_ERR = CONV_ERR{function = "AND_EXISTS_CONV",
		      message = "expecting `(?x.P) /\\ (?x.Q)`"}
in
fun AND_EXISTS_CONV tm = 
   let val {conj1,conj2} = dest_conj tm
                           handle _ => raise AE_ERR
       val {Bvar = x, Body = P} = dest_exists conj1
                                  handle _ => raise AE_ERR
       val {Bvar = y, Body = Q} = dest_exists conj2
                                  handle _ => raise AE_ERR
   in
   if (not(x=y)) 
   then raise AE_ERR
   else if (free_in x P orelse free_in x Q) 
        then raise CONV_ERR{function = "AND_EXISTS_CONV",
			    message = ("`"^(#Name(dest_var x))^
				       "` free in conjunct(s)")}
        else SYM (EXISTS_AND_CONV
                    (mk_exists{Bvar = x,
                               Body = mk_conj{conj1 = P, conj2 = Q}}))
   end
   handle (e as HOL_ERR{origin_structure = "Conv",
			origin_function = "AND_EXISTS_CONV",...}) => raise e
        | _ => raise CONV_ERR{function = "AND_EXISTS_CONV", message = ""}
end;

(* ---------------------------------------------------------------------*)
(* LEFT_AND_EXISTS_CONV: move existential quantifier out of conjunction	*)
(*									*)
(* A call to LEFT_AND_EXISTS_CONV "(?x.P) /\  Q"  returns:		*)
(*									*)
(*   |- (?x.P) /\ Q = (?x'. P[x'/x] /\ Q) 				*)
(* 									*)
(* Where x' is a primed variant of x not free in the input term		*)
(* ---------------------------------------------------------------------*)
fun LEFT_AND_EXISTS_CONV tm = 
   let val {conj1,conj2} = dest_conj tm 
       val {Bvar,Body} = dest_exists conj1 
       val x' = variant (free_vars tm) Bvar 
       val newp = subst[{redex = Bvar, residue = x'}] Body
       val new_conj = mk_conj {conj1 = newp, conj2 = conj2} 
       val otm = mk_exists{Bvar = x', Body = new_conj}
       val (EP,Qth) = CONJ_PAIR(ASSUME tm) 
       val thm1 = EXISTS(otm,x')(CONJ(ASSUME newp)(ASSUME conj2)) 
       val imp1 = DISCH tm (MP (DISCH conj2 (CHOOSE(x',EP)thm1)) Qth) 
       val (t1,t2) = CONJ_PAIR (ASSUME new_conj) 
       val thm2 = CHOOSE (x',ASSUME otm) (CONJ (EXISTS (conj1,x') t1) t2) 
   in
   IMP_ANTISYM_RULE imp1 (DISCH otm thm2)
   end
   handle _ => raise CONV_ERR{function = "LEFT_AND_EXISTS_CONV", message = ""};

(* ---------------------------------------------------------------------*)
(* RIGHT_AND_EXISTS_CONV: move existential quantifier out of conjunction*)
(*									*)
(* A call to RIGHT_AND_EXISTS_CONV "P /\ (?x.Q)"  returns:		*)
(*									*)
(*   |- P /\ (?x.Q) = (?x'. P /\ (Q[x'/x]) 				*)
(* 									*)
(* where x' is a primed variant of x not free in the input term		*)
(* ---------------------------------------------------------------------*)
fun RIGHT_AND_EXISTS_CONV tm = 
   let val {conj1,conj2} = dest_conj tm 
       val {Bvar,Body} = dest_exists conj2
       val x' = variant (free_vars tm) Bvar 
       val newq = subst[{redex = Bvar, residue = x'}]Body 
       val new_conj = mk_conj{conj1 = conj1,conj2 = newq}
       val otm = mk_exists{Bvar = x',Body = new_conj}
       val (Pth,EQ) = CONJ_PAIR(ASSUME tm) 
       val thm1 = EXISTS(otm,x')(CONJ(ASSUME conj1)(ASSUME newq)) 
       val imp1 = DISCH tm (MP (DISCH conj1 (CHOOSE(x',EQ)thm1)) Pth) 
       val (t1,t2) = CONJ_PAIR (ASSUME new_conj) 
       val thm2 = CHOOSE (x',ASSUME otm) (CONJ t1 (EXISTS (conj2,x') t2)) 
   in
   IMP_ANTISYM_RULE imp1 (DISCH otm thm2)
   end
   handle _ => raise CONV_ERR{function = "RIGHT_AND_EXISTS_CONV",
			      message = ""};


(* ---------------------------------------------------------------------*)
(* FORALL_OR_CONV : move universal quantifier into disjunction.		*)
(*									*)
(* A call to FORALL_OR_CONV "!x. P \/ Q"  returns:			*)
(*									*)
(*   |- (!x. P \/ Q) = (!x.P) \/ Q	 [if x not free in Q]		*)
(*   |- (!x. P \/ Q) = P \/ (!x.Q)	 [if x not free in P]		*)
(*   |- (!x. P \/ Q) = (!x.P) \/ (!x.Q)	 [if x free in neither P nor Q]	*)
(* ---------------------------------------------------------------------*)
local
val FO_ERR = CONV_ERR{function = "FORALL_OR_CONV",
		      message = "expecting `!x. P \\/ Q`"}
in
fun FORALL_OR_CONV tm =
   let val {Bvar,Body} = dest_forall tm
                         handle _ => raise FO_ERR
       val {disj1,disj2} = dest_disj Body
                           handle _ => raise FO_ERR
       val fdisj1 = free_in Bvar disj1
       and fdisj2 =  free_in Bvar disj2 
   in
   if (fdisj1 andalso fdisj2) 
   then raise CONV_ERR{function = "FORALL_OR_CONV",
                       message = ("`"^(#Name(dest_var Bvar))^
				       "` free in both disjuncts")}
   else let val disj1_thm = ASSUME disj1
            val disj2_thm = ASSUME disj2
            val thm1 = SPEC Bvar (ASSUME tm) 
            val imp1 = 
               if fdisj1 
               then let val thm2 = CONTR disj1 (MP (ASSUME (mk_neg disj2)) 
                                                   disj2_thm)
                        val thm3 = DISJ1(GEN Bvar
                                             (DISJ_CASES thm1 disj1_thm thm2))
                                        disj2 
                        val thm4 = DISJ2 (mk_forall{Bvar = Bvar, Body = disj1})
                                         (ASSUME disj2) 
                    in
                    DISCH tm (DISJ_CASES(SPEC disj2 EXCLUDED_MIDDLE) thm4 thm3)
                    end
               else if fdisj2 
                    then let val thm2 = CONTR disj2(MP (ASSUME (mk_neg disj1)) 
                                                    (ASSUME disj1))
                             val thm3 = DISJ2 disj1(GEN Bvar(DISJ_CASES thm1 
                                                                        thm2
                                                                    disj2_thm))
                             val thm4 = DISJ1(ASSUME disj1) 
                                             (mk_forall{Bvar=Bvar, Body=disj2})
                         in
                         DISCH tm (DISJ_CASES (SPEC disj1 EXCLUDED_MIDDLE) 
                                              thm4 thm3)
                         end
                    else let val (t1,t2) = (GEN Bvar(ASSUME disj1), 
                                            GEN Bvar(ASSUME disj2)) 
                         in
                         DISCH tm (DISJ_CASES_UNION thm1 t1 t2)
                         end
            val otm = rand(concl imp1) 
            val {disj1,disj2} = dest_disj otm
            val thm5 = (if (fdisj1 orelse (not fdisj2)) then SPEC Bvar else I) 
                       (ASSUME disj1) 
            val thm6 = (if (fdisj2 orelse (not fdisj1)) then SPEC Bvar else I)
                       (ASSUME disj2)
            val imp2 = GEN Bvar (DISJ_CASES_UNION (ASSUME otm) thm5 thm6) 
        in
        IMP_ANTISYM_RULE imp1 (DISCH otm imp2)
        end
   end
   handle (e as HOL_ERR{origin_structure = "Conv",
			origin_function = "FORALL_OR_CONV",...}) => raise e
        | _ => raise CONV_ERR{function = "FORALL_OR_CONV", message = ""}
end;

(* ---------------------------------------------------------------------*)
(* OR_FORALL_CONV : move existential quantifier out of conjunction.	*)
(*									*)
(*   |- (!x.P) \/ (!x.Q) = (!x. P \/ Q) 				*)
(* 									*)
(* provided x is free in neither P nor Q.				*)
(* ---------------------------------------------------------------------*)
local
val OF_ERR = CONV_ERR{function = "OR_FORALL_CONV",
		      message = "expecting `(!x.P) \\/ (!x.Q)`"}
in
fun OR_FORALL_CONV tm = 
   let val {disj1,disj2} = dest_disj tm
                           handle _ => raise OF_ERR
       val {Bvar = x, Body = P} = dest_forall disj1
                           handle _ => raise OF_ERR
       val {Bvar = y, Body = Q} = dest_forall disj2
                           handle _ => raise OF_ERR
   in
   if (not(x=y)) 
   then raise OF_ERR
   else if (free_in x P orelse free_in x Q) 
        then raise CONV_ERR{function = "OR_FORALL_CONV",
                            message = ("`"^(#Name(dest_var x))^
				       "` free in disjuncts(s)")}
        else SYM (FORALL_OR_CONV
                   (mk_forall{Bvar = x, Body = mk_disj{disj1 = P, disj2 = Q}}))
   end
   handle (e as HOL_ERR{origin_structure = "Conv",
			origin_function = "OR_FORALL_CONV",...}) => raise e
        | _ => raise CONV_ERR{function = "OR_FORALL_CONV", message = ""}
end;

(* ---------------------------------------------------------------------*)
(* LEFT_OR_FORALL_CONV : move universal quantifier out of conjunction.	*)
(*									*)
(* A call to LEFT_OR_FORALL_CONV "(!x.P) \/  Q"  returns:		*)
(*									*)
(*   |- (!x.P) \/ Q = (!x'. P[x'/x] \/ Q) 				*)
(* 									*)
(* Where x' is a primed variant of x not free in the input term		*)
(* ---------------------------------------------------------------------*)
fun LEFT_OR_FORALL_CONV tm = 
   let val {disj1,disj2} = dest_disj tm
       val {Bvar,Body} = dest_forall disj1
       val x' = variant (free_vars tm) Bvar
       val newp = subst[{redex = Bvar, residue = x'}] Body
       val aQ = ASSUME disj2
       val Pth = DISJ1 (SPEC x' (ASSUME disj1)) disj2
       val Qth = DISJ2 newp aQ 
       val imp1 = DISCH tm (GEN x' (DISJ_CASES (ASSUME tm) Pth Qth)) 
       val otm = rand(concl imp1) 
       val thm1 = SPEC x' (ASSUME otm) 
       val thm2 = CONTR newp (MP(ASSUME(mk_neg disj2)) aQ) 
       val thm3 = DISJ1 (GEN x' (DISJ_CASES thm1 (ASSUME newp) thm2)) disj2 
       val thm4 = DISJ2 disj1 aQ 
       val imp2 = DISCH otm(DISJ_CASES(SPEC disj2 EXCLUDED_MIDDLE)thm4 thm3) 
   in
   IMP_ANTISYM_RULE imp1 imp2
   end
   handle _ => raise CONV_ERR{function = "LEFT_OR_FORALL_CONV", message = ""};

(* ---------------------------------------------------------------------*)
(* RIGHT_OR_FORALL_CONV : move universal quantifier out of conjunction.	*)
(*									*)
(* A call to RIGHT_OR_FORALL_CONV "P \/ (!x.Q)"  returns:		*)
(*									*)
(*   |- P \/ (!x.Q) = (!x'. P \/ (Q[x'/x]) 				*)
(* 									*)
(* where x' is a primed variant of x not free in the input term		*)
(* ---------------------------------------------------------------------*)
fun RIGHT_OR_FORALL_CONV tm = 
   let val {disj1,disj2} = dest_disj tm
       val {Bvar,Body} = dest_forall disj2
       val x' = variant (free_vars tm) Bvar
       val newq = subst[{redex = Bvar, residue = x'}] Body
       val Qth = DISJ2 disj1 (SPEC x' (ASSUME disj2))
       val Pthm = ASSUME disj1
       val Pth = DISJ1 Pthm newq 
       val imp1 = DISCH tm (GEN x' (DISJ_CASES (ASSUME tm) Pth Qth)) 
       val otm = rand(concl imp1) 
       val thm1 = SPEC x' (ASSUME otm) 
       val thm2 = CONTR newq (MP(ASSUME(mk_neg disj1)) Pthm) 
       val thm3 = DISJ2 disj1 (GEN x' (DISJ_CASES thm1 thm2 (ASSUME newq))) 
       val thm4 = DISJ1 Pthm disj2 
       val imp2 = DISCH otm(DISJ_CASES(SPEC disj1 EXCLUDED_MIDDLE)thm4 thm3) 
   in
   IMP_ANTISYM_RULE imp1 imp2
   end
   handle _ => raise CONV_ERR{function = "RIGHT_OR_FORALL_CONV", message = ""};

(* ---------------------------------------------------------------------*)
(* FORALL_IMP_CONV, implements the following axiom schemes.		*)
(*									*)
(*	|- (!x. P==>Q[x]) = (P ==> (!x.Q[x]))	  [x not free in P]	*)
(*									*)
(*	|- (!x. P[x]==>Q) = ((?x.P[x]) ==> Q)	  [x not free in Q]	*)
(*									*)
(*	|- (!x. P==>Q) = ((?x.P) ==> (!x.Q))	  [x not free in P==>Q]	*)
(* ---------------------------------------------------------------------*)
local
val FI_ERR = CONV_ERR{function = "FORALL_IMP_CONV",
		      message = "expecting `!x. P ==> Q`"}
in
fun FORALL_IMP_CONV tm = 
   let val {Bvar,Body} = dest_forall tm
                         handle _ => raise FI_ERR
       val {ant,conseq} = dest_imp Body
                          handle _ => raise FI_ERR
       val fant = free_in Bvar ant 
       and fconseq =  free_in Bvar conseq
       val ant_thm = ASSUME ant
       val tm_thm = ASSUME tm
   in
   if (fant andalso fconseq) 
   then raise CONV_ERR{function = "FORALL_IMP_CONV",
		       message = ("`"^(#Name(dest_var Bvar))^
				  "` free on both sides of `==>`")}
   else if fant 
        then let val asm = mk_exists{Bvar = Bvar, Body = ant} 
                 val th1 = CHOOSE(Bvar,ASSUME asm)
                                 (UNDISCH(SPEC Bvar tm_thm))
                 val imp1 = DISCH tm (DISCH asm th1) 
                 val cncl = rand(concl imp1) 
                 val th2 = MP (ASSUME cncl) (EXISTS (asm,Bvar) ant_thm) 
                 val imp2 = DISCH cncl (GEN Bvar (DISCH ant th2)) 
             in
             IMP_ANTISYM_RULE imp1 imp2 
             end
       else if fconseq 
            then let val imp1 = DISCH ant(GEN Bvar(UNDISCH(SPEC Bvar tm_thm))) 
                     val cncl = concl imp1 
                     val imp2 = GEN Bvar(DISCH ant
                                          (SPEC Bvar(UNDISCH (ASSUME cncl))))
                 in
                 IMP_ANTISYM_RULE (DISCH tm imp1) (DISCH cncl imp2)
                 end
            else let val asm = mk_exists{Bvar = Bvar, Body = ant} 
                     val th1 = GEN Bvar (CHOOSE(Bvar,ASSUME asm)
                                            (UNDISCH(SPEC Bvar tm_thm))) 
                     val imp1 = DISCH tm (DISCH asm th1) 
                     val cncl = rand(concl imp1) 
                     val th2 = SPEC Bvar (MP (ASSUME cncl) 
                                          (EXISTS (asm,Bvar) ant_thm)) 
                     val imp2 = DISCH cncl (GEN Bvar (DISCH ant th2)) 
                 in
                 IMP_ANTISYM_RULE imp1 imp2
                 end
   end
   handle (e as HOL_ERR{origin_structure = "Conv",
			origin_function = "FORALL_IMP_CONV",...}) => raise e
        | _ => raise CONV_ERR{function = "FORALL_IMP_CONV", message = ""}
end;

(* ---------------------------------------------------------------------*)
(* LEFT_IMP_EXISTS_CONV, implements the following theorem-scheme:	*)
(*									*)
(*    |- (?x. t1[x]) ==> t2  =  !x'. t1[x'] ==> t2			*)
(*									*)
(* where x' is a variant of x chosen not to be free in (?x.t1[x])==>t2  *)
(*									*)
(* Author: Tom Melham                                                   *)
(* Revised: [TFM 90.07.01]						*)
(*----------------------------------------------------------------------*)
fun LEFT_IMP_EXISTS_CONV tm = 
   let val {ant, ...} = dest_imp tm 
       val {Bvar,Body} = dest_exists ant 
       val x' = variant (free_vars tm) Bvar 
       val t' = subst [{redex = Bvar, residue = x'}] Body 
       val th1 = GEN x' (DISCH t'(MP(ASSUME tm)(EXISTS(ant,x')(ASSUME t')))) 
       val rtm = concl th1 
       val th2 = CHOOSE (x',ASSUME ant) (UNDISCH(SPEC x'(ASSUME rtm))) 
   in
   IMP_ANTISYM_RULE (DISCH tm th1) (DISCH rtm (DISCH ant th2))
   end
   handle _ => raise CONV_ERR{function = "LEFT_IMP_EXISTS_CONV", message = ""};

(* ---------------------------------------------------------------------*)
(* RIGHT_IMP_FORALL_CONV, implements the following theorem-scheme:	*)
(*									*)
(*    |- (t1 ==> !x. t2)  =  !x'. t1 ==> t2[x'/x]			*)
(*									*)
(* where x' is a variant of x chosen not to be free in the input term.	*)
(*----------------------------------------------------------------------*)
fun RIGHT_IMP_FORALL_CONV tm = 
   let val {ant,conseq} = dest_imp tm
       val {Bvar,Body} = dest_forall conseq
       val x' = variant (free_vars tm) Bvar 
       val t' = subst [{redex = Bvar, residue = x'}] Body 
       val imp1 = DISCH tm (GEN x' (DISCH ant(SPEC x'(UNDISCH(ASSUME tm))))) 
       val ctm = rand(concl imp1) 
       val alph = GEN_ALPHA_CONV Bvar (mk_forall{Bvar = x', Body = t'}) 
       val thm1 = EQ_MP alph (GEN x'(UNDISCH (SPEC x' (ASSUME ctm)))) 
       val imp2 = DISCH ctm (DISCH ant thm1) 
   in
   IMP_ANTISYM_RULE imp1 imp2
   end
   handle _ => raise CONV_ERR{function = "RIGHT_IMP_FORALL_CONV",
			      message = ""};


(* ---------------------------------------------------------------------*)
(* EXISTS_IMP_CONV, implements the following axiom schemes.		*)
(*									*)
(*	|- (?x. P==>Q[x]) = (P ==> (?x.Q[x]))	  [x not free in P]	*)
(*									*)
(*	|- (?x. P[x]==>Q) = ((!x.P[x]) ==> Q)	  [x not free in Q]	*)
(*									*)
(*	|- (?x. P==>Q) = ((!x.P) ==> (?x.Q))	  [x not free in P==>Q]	*)
(* ---------------------------------------------------------------------*)
local
val EI_ERR = CONV_ERR{function = "EXISTS_IMP_CONV",
		      message = "expecting `?x. P ==> Q`"}
in
fun EXISTS_IMP_CONV tm = 
   let val {Bvar,Body} = dest_exists tm
                         handle _ => raise EI_ERR
       val {ant = P,conseq = Q} = dest_imp Body
                                  handle _ => raise EI_ERR
       val fP = free_in Bvar P
       and fQ =  free_in Bvar Q 
   in
   if (fP andalso fQ)
   then raise CONV_ERR{function = "EXISTS_IMP_CONV",
		       message = ("`"^(#Name(dest_var Bvar))^
				  "` free on both sides of `==>`")}
   else if fP 
        then let val allp = mk_forall{Bvar = Bvar, Body = P} 
                 val th1 = SPEC Bvar (ASSUME allp) 
                 val thm1 = MP (ASSUME Body) th1 
                 val imp1 = DISCH tm (CHOOSE(Bvar,ASSUME tm)(DISCH allp thm1)) 
                 val otm = rand(concl imp1) 
                 val thm2 = EXISTS(tm,Bvar)(DISCH P (UNDISCH(ASSUME otm))) 
                 val notP = mk_neg P
                 val notP_thm = ASSUME notP
                 val nex =  mk_exists{Bvar = Bvar, Body = notP}
                 val asm1 = EXISTS (nex, Bvar) notP_thm
                 val th2 = CCONTR P (MP (ASSUME (mk_neg nex)) asm1) 
                 val th3 = CCONTR nex (MP (ASSUME (mk_neg allp))
                                          (GEN Bvar th2)) 
                 val thm4 = DISCH P (CONTR Q (UNDISCH notP_thm))
                 val thm5 = CHOOSE(Bvar,th3)(EXISTS(tm,Bvar)thm4) 
                 val thm6 = DISJ_CASES (SPEC allp EXCLUDED_MIDDLE) thm2 thm5 
             in
             IMP_ANTISYM_RULE imp1 (DISCH otm thm6) 
             end
        else if fQ 
             then let val thm1 = EXISTS (mk_exists{Bvar = Bvar, Body = Q},Bvar)
                                        (UNDISCH(ASSUME Body)) 
                      val imp1 = DISCH tm (CHOOSE(Bvar,ASSUME tm)
                                                 (DISCH P thm1)) 
                      val thm2 = UNDISCH (ASSUME (rand(concl imp1))) 
                      val thm3 = CHOOSE (Bvar,thm2) (EXISTS (tm,Bvar) 
                                                         (DISCH P (ASSUME Q))) 
                      val thm4 = EXISTS(tm,Bvar)
                                       (DISCH P
                                         (CONTR Q(UNDISCH(ASSUME(mk_neg P)))))
                      val thm5 = DISJ_CASES (SPEC P EXCLUDED_MIDDLE) thm3 thm4 
                  in
                  IMP_ANTISYM_RULE imp1 (DISCH(rand(concl imp1)) thm5) 
                  end
            else let val eQ = mk_exists{Bvar = Bvar, Body = Q}
                     and aP = mk_forall{Bvar = Bvar, Body = P}
                     val thm1 = EXISTS(eQ,Bvar)(UNDISCH(ASSUME Body)) 
                     val thm2 = DISCH aP (PROVE_HYP (SPEC Bvar (ASSUME aP))
                                                    thm1)
                     val imp1 = DISCH tm (CHOOSE(Bvar,ASSUME tm) thm2) 
                     val thm2 = CHOOSE(Bvar,UNDISCH (ASSUME(rand(concl imp1))))
                                      (ASSUME Q) 
                     val thm3 = DISCH P (PROVE_HYP (GEN Bvar (ASSUME P)) thm2) 
                     val imp2 = DISCH (rand(concl imp1)) (EXISTS(tm,Bvar) thm3)
                 in
                 IMP_ANTISYM_RULE imp1 imp2
                 end
   end
   handle (e as HOL_ERR{origin_structure = "Conv",
			origin_function = "EXISTS_IMP_CONV",...}) => raise e
        | _ => raise CONV_ERR{function = "EXISTS_IMP_CONV", message = ""}
end;

(* ---------------------------------------------------------------------*)
(* LEFT_IMP_FORALL_CONV, implements the following theorem-scheme:	*)
(*									*)
(*    |- (!x. t1[x]) ==> t2  =  ?x'. t1[x'] ==> t2			*)
(*									*)
(* where x' is a variant of x chosen not to be free in the input term	*)
(*----------------------------------------------------------------------*)
fun LEFT_IMP_FORALL_CONV tm = 
   let val {ant,conseq} = dest_imp tm 
       val {Bvar,Body} = dest_forall ant 
       val x' = variant (free_vars tm) Bvar 
       val t1' = subst [{redex = Bvar, residue = x'}] Body 
       val not_t1'_thm = ASSUME (mk_neg t1')
       val th1 = SPEC x' (ASSUME ant) 
       val new_imp = mk_imp{ant = t1', conseq = conseq}
       val thm1 = MP (ASSUME new_imp) th1 
       val otm = mk_exists{Bvar = x', Body = new_imp}
       val imp1 = DISCH otm (CHOOSE(x',ASSUME otm)(DISCH ant thm1)) 
       val thm2 = EXISTS(otm,x') (DISCH t1' (UNDISCH(ASSUME tm))) 
       val nex =  mk_exists{Bvar = x', Body = mk_neg t1'}
       val asm1 = EXISTS (nex, x') not_t1'_thm 
       val th2 = CCONTR t1' (MP (ASSUME (mk_neg nex)) asm1) 
       val th3 = CCONTR nex (MP(ASSUME(mk_neg ant)) (GEN x' th2)) 
       val thm4 = DISCH t1' (CONTR conseq (UNDISCH not_t1'_thm)) 
       val thm5 = CHOOSE(x',th3)
                        (EXISTS(mk_exists{Bvar = x',Body = concl thm4},x')thm4)
       val thm6 = DISJ_CASES (SPEC ant EXCLUDED_MIDDLE) thm2 thm5 
   in
   IMP_ANTISYM_RULE (DISCH tm thm6) imp1
   end
   handle _ => raise CONV_ERR{function = "LEFT_IMP_FORALL_CONV", message = ""};

(* ---------------------------------------------------------------------*)
(* RIGHT_IMP_EXISTS_CONV, implements the following theorem-scheme:	*)
(*									*)
(*    |- (t1 ==> ?x. t2)  =  ?x'. t1 ==> t2[x'/x]			*)
(*									*)
(* where x' is a variant of x chosen not to be free in the input term.	*)
(*----------------------------------------------------------------------*)
fun RIGHT_IMP_EXISTS_CONV tm = 
   let val {ant,conseq} = dest_imp tm
       val {Bvar,Body} = dest_exists conseq
       val x' = variant (free_vars tm) Bvar 
       val t2' = subst [{redex = Bvar, residue = x'}] Body
       val new_imp = mk_imp{ant = ant, conseq = t2'}
       val otm = mk_exists{Bvar = x', Body = new_imp}
       val thm1 = EXISTS(conseq,x')(UNDISCH(ASSUME new_imp)) 
       val imp1 = DISCH otm (CHOOSE(x',ASSUME otm) (DISCH ant thm1)) 
       val thm2 = UNDISCH (ASSUME tm) 
       val thm3 = CHOOSE (x',thm2) (EXISTS (otm,x') (DISCH ant (ASSUME t2'))) 
       val thm4 = DISCH ant (CONTR t2'(UNDISCH(ASSUME(mk_neg ant)))) 
       val thm5 = EXISTS(otm,x') thm4 
       val thm6 = DISJ_CASES (SPEC ant EXCLUDED_MIDDLE) thm3 thm5 
   in
   IMP_ANTISYM_RULE (DISCH tm thm6) imp1
   end
   handle _ => raise CONV_ERR{function = "RIGHT_IMP_EXISTS_CONV",
			      message = ""};

(* ---------------------------------------------------------------------*)
(* X_SKOLEM_CONV : introduce a skolem function.				*)
(*									*)
(*   |- (!x1...xn. ?y. tm[x1,...,xn,y])					*)
(*        =								*)
(*      (?f. !x1...xn. tm[x1,..,xn,f x1 ... xn]				*)
(*									*)
(* The first argument is the function f.				*)
(* ---------------------------------------------------------------------*)
fun X_SKOLEM_CONV v = 
   if (not(is_var v)) 
   then raise CONV_ERR{function = "X_SKOLEM_CONV",
                       message = "first argument not a variable"}
   else 
fn tm =>
  let val (xs,ex) = strip_forall tm
      val (ab as {Bvar,Body}) = dest_exists ex
                                handle _ =>  
                                raise CONV_ERR{function = "X_SKOLEM_CONV",
                                               message = 
					         "expecting `!x1...xn. ?y.tm`"}
      val fx = Term.list_mk_comb(v,xs) 
               handle _ => 
               raise CONV_ERR{function = "X_SKOLEM_CONV",
                              message = "function variable has the wrong type"}
  in 
  if (free_in v tm) 
  then raise CONV_ERR{function = "X_SKOLEM_CONV",
                      message = ("`"^(#Name(dest_var v))^
				 "` free in the input term")}
  else let val pat_bod = list_mk_forall(xs,subst[{redex=Bvar,residue=fx}]Body)
           val pat = mk_exists{Bvar = v, Body = pat_bod}
           val fnn = list_mk_abs(xs,mk_select ab) 
           val bth = SYM(LIST_BETA_CONV (Term.list_mk_comb(fnn,xs))) 
           val thm1 = SUBST [{var = Bvar, thm = bth}] Body 
                            (SELECT_RULE (SPECL xs (ASSUME tm)))
           val imp1 = DISCH tm (EXISTS (pat,fnn) (GENL xs thm1)) 
           val thm2 = SPECL xs (ASSUME pat_bod)
           val thm3 = GENL xs (EXISTS (ex,fx) thm2) 
           val imp2 = DISCH pat (CHOOSE (v,ASSUME pat) thm3) 
       in
       IMP_ANTISYM_RULE imp1 imp2
       end
  end
  handle (e as HOL_ERR{origin_structure = "Conv",
		       origin_function = "X_SKOLEM_CONV",...}) => raise e
       | _ => raise CONV_ERR{function = "X_SKOLEM_CONV", message = ""};

(* ---------------------------------------------------------------------*)
(* SKOLEM_CONV : introduce a skolem function.				*)
(*									*)
(*   |- (!x1...xn. ?y. tm[x1,...,xn,y])					*)
(*        =								*)
(*      (?y'. !x1...xn. tm[x1,..,xn,y' x1 ... xn]			*)
(*									*)
(* Where y' is a primed variant of y not free in the input term.	*)
(* ---------------------------------------------------------------------*)
local
fun mkfty tm ty = Type.mk_type{Tyop = "fun", Args = [type_of tm,ty]}
in
fun SKOLEM_CONV tm =
   let val (xs,ex) = strip_forall tm
       val {Bvar, ...} = dest_exists ex
       val {Name,Ty} = dest_var Bvar
       val fv = mk_var{Name = Name, Ty = itlist mkfty xs Ty}
   in
   X_SKOLEM_CONV (variant (free_vars tm) fv) tm
   end
   handle _ => raise CONV_ERR{function = "SKOLEM_CONV", message = ""}
end;



(*----------------------------------------------------------------------*)
(* SYM_CONV : a conversion for symmetry of equality.			*)
(*									*)
(* e.g. SYM_CONV "x=y"   ---->   (x=y) = (y=x).				*)
(*----------------------------------------------------------------------*)
local val alpha = ==`:'a`==
in
fun SYM_CONV tm = 
   let val {lhs,rhs} = dest_eq tm
       val th = INST_TYPE [alpha |-> type_of lhs] EQ_SYM_EQ
   in
   SPECL [lhs,rhs] th
   end
   handle _ => raise CONV_ERR{function = "SYM_CONV", message = ""}
end;

(* First a function for converting a conversion to a rule *)

(*
    A |- t1 = t2
   --------------   (t2' got from t2 using a conversion)
    A |- t1 = t2'
*)

fun RIGHT_CONV_RULE conv th = TRANS th (conv(rhs(concl th)));

(* ---------------------------------------------------------------------*)
(* FUN_EQ_CONV "f = g"  returns:  |- (f = g) = !x. (f x = g x).  	*)
(*									*)
(* Notes: f and g must be functions. The conversion choses an "x" not	*)
(* free in f or g. This conversion just states that functions are equal	*)
(* IFF the results of applying them to an arbitrary value are equal.	*)
(*									*)
(* New version: TFM 88.03.31						*)
(* ---------------------------------------------------------------------*)
fun FUN_EQ_CONV tm = 
   let val vars = free_vars tm 
       val {Tyop = "fun", Args = [ty1,_]} = Type.dest_type(type_of (lhs tm)) 
       val varnm = if (Type.is_vartype ty1) 
                   then "x"
                   else hd(explode(#Tyop(Type.dest_type ty1)))
(*       val x = variant vars (mk_primed_var{Name = varnm, Ty = ty1}) *)
         val x = variant vars (mk_var{Name = varnm, Ty = ty1})
       val imp1 = DISCH_ALL (GEN x (AP_THM (ASSUME tm) x))
       val asm = ASSUME (concl (GEN x (AP_THM (ASSUME tm) x)))
   in
   IMP_ANTISYM_RULE imp1 (DISCH_ALL (EXT asm))
   end
   handle _ => raise CONV_ERR{function = "FUN_EQ_CONV", message = ""};

(* --------------------------------------------------------------------- *)
(* X_FUN_EQ_CONV "x" "f = g"                                             *)
(*                                                                       *)
(* yields |- (f = g) = !x. f x = g x                                     *)
(*                                                                       *)
(* fails if x free in f or g, or x not of the right type.                *)
(* --------------------------------------------------------------------- *)
fun X_FUN_EQ_CONV x tm = 
   if (not(is_var x))
   then raise CONV_ERR{function = "X_FUN_EQ_CONV",
		       message =  "first arg is not a variable"}
   else if (mem x (free_vars tm)) 
        then raise CONV_ERR{function = "X_FUN_EQ_CONV",
                            message = (#Name(dest_var x) ^
				       " is a free variable")}
        else let val l = lhs tm 
                         handle _ => 
                         raise CONV_ERR{function = "X_FUN_EQ_CONV",
					message =  "not an equation"}
                 val ty1 = case (Type.dest_type (type_of l))
                             of {Tyop = "fun", Args = [ty1,_]} => ty1
                              | _ => raise CONV_ERR{function = "X_FUN_EQ_CONV",
						    message = 
						  "lhs and rhs not functions"}
             in
             if (not (ty1 = type_of x))
             then raise CONV_ERR{function = "X_FUN_EQ_CONV",
                                 message = (#Name(dest_var x) ^
					    " has the wrong type")}
             else let val imp1 = DISCH_ALL (GEN x (AP_THM (ASSUME tm) x))
                      val asm = ASSUME (concl (GEN x (AP_THM (ASSUME tm) x))) 
                  in
                  IMP_ANTISYM_RULE imp1 (DISCH_ALL (EXT asm))
                  end
             end
             handle (e as HOL_ERR{origin_structure = "Conv",
				  origin_function = "X_FUN_EQ_CONV",...}) =>
	            raise e
                  | _ => raise CONV_ERR{function = "X_FUN_EQ_CONV",
					message = ""};

(* ---------------------------------------------------------------------*)
(* SELECT_CONV: a conversion for introducing "?" when P [@x.P[x]].	*)
(*									*)
(* SELECT_CONV "P [@x.P [x]]" ---> |- P [@x.P [x]] = ?x. P[x]		*)
(*									*)
(* Added: TFM 88.03.31							*)
(* ---------------------------------------------------------------------*)
(* fun SELECT_CONV tm =                                                 
**   let val epsl = find_terms is_select tm                             
**       fun findfn t = (tm = subst [{redex = #Bvar (dest_select t),
**                                    residue = t}]
**                                  (#Body (dest_select t)))
**       val sel = first findfn epsl
**       val ex  = mk_exists(dest_select sel)
**       val imp1 = DISCH_ALL (SELECT_RULE (ASSUME ex)) 
**       and imp2 = DISCH_ALL (EXISTS (ex,sel) (ASSUME tm)) 
**   in
**   IMP_ANTISYM_RULE imp2 imp1
**   end
**   handle _ => raise CONV_ERR{function = "SELECT_CONV", message = ""};
*)

local
val f = mk_var{Name="f",Ty= ==`:'a->bool`==} 
val th1 = AP_THM Exists.EXISTS_DEF f 
val th2 = CONV_RULE (RAND_CONV BETA_CONV) th1 
val tyv = Type.mk_vartype "'a" 
fun EXISTS_CONV{Bvar,Body} = 
   let val ty = type_of Bvar
       val ins = INST_TYPE [{redex=tyv, residue=ty}] th2
       val th = INST[{redex=inst[{redex=tyv,residue=ty}] f,
                      residue=mk_abs{Bvar=Bvar,Body=Body}}] ins
   in CONV_RULE (RAND_CONV BETA_CONV) th
   end
fun find_first p tm =
   if (p tm)
   then tm 
   else if (is_abs tm)
        then find_first p (body tm) 
        else if is_comb tm 
             then let val {Rator,Rand} = dest_comb tm 
                  in (find_first p Rator) handle _ => (find_first p Rand)
                  end
             else raise CONV_ERR{function="SELECT_CONV.find_first",message=""}
in
fun SELECT_CONV tm =
   let fun right t = 
          let val {Bvar,Body} = dest_select t
          in Term.aconv (subst[{redex=Bvar,residue=t}] Body) tm
          end handle _ => false
       val epi = find_first right tm 
   in
   SYM (EXISTS_CONV (dest_select epi))
   end
   handle _ => raise CONV_ERR{function="SELECT_CONV",message=""}
end;

(* ---------------------------------------------------------------------*)
(* CONTRAPOS_CONV: convert an implication to its contrapositive.	*)
(*									*)
(* CONTRAPOS_CONV "a ==> b" --> |- (a ==> b) = (~b ==> ~a)		*)
(*									*)
(* Added: TFM 88.03.31							*)
(* Revised: TFM 90.07.13						*)
(* ---------------------------------------------------------------------*)
fun CONTRAPOS_CONV tm =
   let val {ant,conseq} = dest_imp tm
       val negc = mk_neg conseq
       and contra = mk_imp{ant = mk_neg conseq, conseq = mk_neg ant}
       val imp1 = DISCH negc (NOT_INTRO(IMP_TRANS(ASSUME tm)(ASSUME negc))) 
       and imp2 = DISCH ant (CCONTR conseq (UNDISCH (UNDISCH (ASSUME contra))))
   in
   IMP_ANTISYM_RULE (DISCH tm imp1) (DISCH contra imp2)
   end
   handle _ => raise CONV_ERR{function = "CONTRAPOS_CONV", message = ""};

(* ---------------------------------------------------------------------*)
(* ANTE_CONJ_CONV: convert an implication with conjuncts in its 	*)
(*		  antecedant to a series of implications.		*)
(*									*)
(* ANTE_CONJ_CONV "a1 /\ a2 ==> c" 					*)
(*	----> |- a1 /\ a2 ==> c = (a1 ==> (a2 ==> c))			*)
(*									*)
(* Added: TFM 88.03.31							*)
(* ---------------------------------------------------------------------*)
fun ANTE_CONJ_CONV tm =
   let val {ant,conseq} = dest_imp tm
       val {conj1,conj2} = dest_conj ant
       val ant_thm = ASSUME ant
       val imp1 = MP (ASSUME tm) (CONJ (ASSUME conj1) (ASSUME conj2)) 
       and imp2 = LIST_MP [CONJUNCT1 ant_thm,CONJUNCT2 ant_thm]
		          (ASSUME (mk_imp{ant = conj1,
                                          conseq = mk_imp{ant = conj2,
                                                          conseq = conseq}}))
   in
   IMP_ANTISYM_RULE (DISCH_ALL (DISCH conj1 (DISCH conj2 imp1)))
                    (DISCH_ALL (DISCH ant imp2))
   end
   handle _ => raise CONV_ERR{function = "ANTE_CONJ_CONV", message = ""};


(* ---------------------------------------------------------------------*)
(* SWAP_EXISTS_CONV: swap the order of existentially quantified vars.	*)
(*									*)
(* SWAP_EXISTS_CONV "?x y.t[x,y]" ---> |- ?x y.t[x,y] = ?y x.t[x,y]	*)
(*									*)
(* AUTHOR: Paul Loewenstein 3 May 1988                             	*)
(* ---------------------------------------------------------------------*)
fun SWAP_EXISTS_CONV xyt =
   let val {Bvar = x,Body = yt} = dest_exists xyt
       val {Bvar = y, Body = t} = dest_exists yt
       val xt = mk_exists {Bvar = x, Body = t}
       val yxt = mk_exists{Bvar = y, Body = xt}
       val t_thm = ASSUME t
   in
   IMP_ANTISYM_RULE
         (DISCH xyt (CHOOSE (x,ASSUME xyt) (CHOOSE (y, (ASSUME yt))
          (EXISTS (yxt,y) (EXISTS (xt,x) t_thm)))))
         (DISCH yxt (CHOOSE (y,ASSUME yxt) (CHOOSE (x, (ASSUME xt))
 	 (EXISTS (xyt,x) (EXISTS (yt,y) t_thm)))))
   end
   handle _ => raise CONV_ERR{function = "SWAP_EXISTS_CONV", message = ""};


(* ---------------------------------------------------------------------*)
(* bool_EQ_CONV: conversion for boolean equality.			*)
(*									*)
(* bool_EQ_CONV "b1 = b2" returns:					*)
(*									*)
(*    |- (b1 = b2) = T	   if b1 and b2 are identical boolean terms	*)
(*    |- (b1 = b2)  = b2	   if b1 = "T"				*)
(*    |- (b1 = b2)  = b1	   if b2 = "T"				*)
(* 									*)
(* Added TFM 88.03.31							*)
(* Revised TFM 90.07.24							*)
(* ---------------------------------------------------------------------*)
local
val boolty = ==`:bool`==
val (Tb::bT::_) = map (GEN (--`b:bool`--))
                      (CONJUNCTS(SPEC (--`b:bool`--) EQ_CLAUSES))
val T = --`T`--
and F = --`F`--
in
fun bool_EQ_CONV tm = 
   let val {lhs,rhs} = (dest_eq tm)
       val _ = if (type_of rhs = boolty) 
               then () 
               else raise CONV_ERR{function = "bool_EQ_CONV",
				   message = "does not have boolean type"}
   in
   if (lhs=rhs) 
   then EQT_INTRO (REFL lhs) 
   else if (lhs=T)
        then SPEC rhs Tb 
        else if (rhs=T) 
             then SPEC lhs bT
             else raise CONV_ERR{function = "bool_EQ_CONV",
				 message = "inapplicable"}
   end
   handle (e as HOL_ERR{origin_structure = "Conv",
			origin_function = "bool_EQ_CONV",...}) => raise e
        | _ => raise CONV_ERR{function = "bool_EQ_CONV", message = ""}
end;

(* ---------------------------------------------------------------------*)
(* EXISTS_UNIQUE_CONV: expands with the definition of unique existence.	*)
(*									*)
(* 									*)
(* EXISTS_UNIQUE_CONV "?!x.P[x]" yields the theorem: 			*)
(* 									*)
(*     |- ?!x.P[x] = ?x.P[x] /\ !x y. P[x] /\ P[y] ==> (x=y)		*)
(* 									*)
(* ADDED: TFM 90.05.06							*)
(*									*)
(* REVISED: now uses a variant of x for y in 2nd conjunct [TFM 90.06.11]*)
(* ---------------------------------------------------------------------*)
local
val v = genvar (==`:bool`==)
val AND = --`/\`--
val IMP = --`==>`--
val alpha = ==`:'a`==
fun alpha_subst ty = [{redex = alpha, residue = ty}]
val check = assert (fn c => (#Name(dest_const c) = "?!"))
fun MK_BIN f (e1,e2) = MK_COMB((AP_TERM f e1),e2) 
val rule = CONV_RULE o RAND_CONV o GEN_ALPHA_CONV
fun MK_ALL x y tm = rule y (FORALL_EQ x tm) 
fun handle_ant{conj1, conj2} = (BETA_CONV conj1, BETA_CONV conj2)
fun conv (nx,ny) t = 
   let val ([ox,oy],imp) = strip_forall t
       val {ant,conseq} = dest_imp imp
       val ant' = MK_BIN AND (handle_ant (dest_conj ant))
   in
   MK_ALL ox nx (MK_ALL oy ny (MK_BIN IMP (ant',REFL conseq))) 
   end
in
fun EXISTS_UNIQUE_CONV tm =
   let val {Rator,Rand} = dest_comb tm
       val _ = check Rator
       val (ab as {Bvar,Body}) = dest_abs Rand
       val def = INST_TYPE (alpha_subst (type_of Bvar)) Bool.EXISTS_UNIQUE_DEF
       val exp = RIGHT_BETA(AP_THM def Rand) 
       and y = variant (all_vars Body) Bvar
   in
   SUBST [{var = v, thm = conv (Bvar,y) (rand(rand(concl exp)))}] 
         (mk_eq{lhs = tm,rhs = mk_conj{conj1 = mk_exists ab, 
                                       conj2 = v}})
         exp
   end
   handle _ => raise CONV_ERR{function = "EXISTS_UNIQUE_CONV", message = ""}
end;

(* Compiling COND_CONV breaks v.88 *)
(* ---------------------------------------------------------------------*)
(* COND_CONV: conversion for simplifying conditionals:			*)
(*									*)
(*   --------------------------- COND_CONV "T => u | v"			*)
(*     |- (T => u | v) = u 						*)
(*                                                                      *)
(*									*)
(*   --------------------------- COND_CONV "F => u | v"			*)
(*     |- (F => u | v) = v 						*)
(*									*)
(*									*)
(*   --------------------------- COND_CONV "b => u | u"			*)
(*     |- (b => u | u) = u 						*)
(*									*)
(*   --------------------------- COND_CONV "b => u | v"	(u =alpha v)	*)
(*     |- (b => u | v) = u 						*)
(*									*)
(* COND_CONV "P=>u|v" fails if P is neither "T" nor "F" and u =/= v.	*)
(* ---------------------------------------------------------------------*)
local
val T = --`T`--
and F = --`F`--
and vt = genvar (==`:'a`==) 
and vf =  genvar (==`:'a`==) 
val gen = GENL [vt,vf] 
val (CT,CF) = (gen ## gen) (CONJ_PAIR (SPECL [vt,vf] COND_CLAUSES))
val alpha = ==`:'a`==
in
fun COND_CONV tm =
   let val {cond,larm,rarm} = dest_cond tm 
                              handle _ => raise BAD_STRUCT
       val INST_TYPE' = INST_TYPE [{redex = alpha, residue = type_of larm}]
   in
   if (cond=T) 
   then SPEC rarm (SPEC larm (INST_TYPE' CT)) 
   else if (cond=F) 
        then SPEC rarm (SPEC larm (INST_TYPE' CF)) 
        else if (larm=rarm) 
             then SPEC larm (SPEC cond (INST_TYPE' COND_ID)) 
             else if (aconv larm rarm) 
                  then let val cnd = AP_TERM (rator tm) (ALPHA rarm larm)
                           val th = SPEC larm (SPEC cond (INST_TYPE' COND_ID)) 
                       in
                       TRANS cnd th 
                       end
                  else raise CONV_ERR{function = "COND_CONV", message = ""}
   end
   handle BAD_STRUCT => raise CONV_ERR{function = "COND_CONV",
				       message = "not a cond"}
        | (e as HOL_ERR{origin_structure = "Conv",
			origin_function = "COND_CONV",...}) =>
	      raise e
        | _ => raise CONV_ERR{function = "COND_CONV", message = ""}
end;


(* ===================================================================== *)
(* A rule defined using conversions.                                     *)
(* ===================================================================== *)


(* ---------------------------------------------------------------------*)
(* EXISTENCE: derives existence from unique existence:		        *)
(* 									*)
(*    |- ?!x. P[x]							*)
(* --------------------							*)
(*    |- ?x. P[x]							*)
(* 									*)
(* ---------------------------------------------------------------------*)
local
val EXISTS_UNIQUE_DEF = Theory.definition "bool" "EXISTS_UNIQUE_DEF"
val P = --`P:'a -> bool`--
val th1 = SPEC P (CONV_RULE (X_FUN_EQ_CONV P) EXISTS_UNIQUE_DEF)
val th2 = CONJUNCT1(UNDISCH(fst(EQ_IMP_RULE(RIGHT_BETA th1))))
val imp = GEN P (DISCH (--`$?! ^P`--) th2)
val check = assert (fn c => (#Name(dest_const c) = "?!"))
val alpha = ==`:'a`==
in
fun EXISTENCE th =
   let val {Rator,Rand} = dest_comb(concl th)
       val _ = check Rator
       val {Bvar,...} = dest_abs Rand
   in
   MP (SPEC Rand (INST_TYPE [{redex = alpha, residue = type_of Bvar}] imp))
      th
   end
   handle _ => raise CONV_ERR{function = " EXISTENCE", message = ""}
end;


(*-----------------------------------------------------------------------*)
(* AC_CONV - Prove equality using associative + commutative laws         *)
(*                                                                       *)
(* The conversion is given an associative and commutative law (it deduces*)
(* the relevant operator and type from these) in the form of the inbuilt *)
(* ones, and an equation to prove. It will try to prove this. Example:   *)
(*                                                                       *)
(*  AC_CONV(ADD_ASSOC,ADD_SYM) "(1 + 3) + (2 + 4) = 4 + (3 + (2 + 1))"   *)
(* [JRH 91.07.17]                                                        *)
(*-----------------------------------------------------------------------*)

fun AC_CONV(associative,commutative) tm =
   let val opr = (rator o rator o lhs o snd o strip_forall o concl) commutative
       val ty = (hd o #Args o Type.dest_type o type_of) opr
       val x = mk_var{Name="x",Ty=ty}
       and y = mk_var{Name="y",Ty=ty}
       and z = mk_var{Name="z",Ty=ty}
       val xy = mk_comb{Rator=mk_comb{Rator=opr,Rand=x},Rand=y} 
       and yz = mk_comb{Rator=mk_comb{Rator=opr,Rand=y},Rand=z}
       and yx = mk_comb{Rator=mk_comb{Rator=opr,Rand=y},Rand=x}
       val comm = PART_MATCH I commutative (mk_eq{lhs=xy,rhs=yx})
       and ass = PART_MATCH I (SYM (SPEC_ALL associative))
              (mk_eq{lhs=mk_comb{Rator=mk_comb{Rator=opr,Rand=xy},Rand=z},
                     rhs=mk_comb{Rator=mk_comb{Rator=opr,Rand=x},Rand=yz}})
       val asc = TRANS (SUBS [comm] (SYM ass)) (INST[{redex=y,residue=x},
                                                     {redex=x,residue=y}] ass)
       val init = TOP_DEPTH_CONV (REWR_CONV ass) tm
       val gl = rhs (concl init)

       fun bubble head expr =
          let val {Rator,Rand=r} = dest_comb expr
              val {Rator=xopr, Rand = l} = dest_comb Rator
          in
          if (xopr = opr)
          then if (l = head) 
               then REFL expr 
               else if (r = head)
                    then INST [{redex=x,residue=l}, {redex=y,residue=r}] comm
                    else let val subb = bubble head r
                             val eqv = AP_TERM (mk_comb{Rator=xopr,Rand=l})subb
                             val {Rator,Rand=r'} = 
                                        dest_comb(#rhs(dest_eq(concl subb)))
                             val {Rator=yopr,Rand=l'} = dest_comb Rator
                         in
                         TRANS eqv (INST[{redex=x,residue=l},
                                         {redex=y,residue=l'},
                                         {redex=z,residue=r'}] asc)
                         end
          else raise CONV_ERR{function="AC_CONV.bubble",message=""}
          end

       fun asce {lhs,rhs} =
          if (lhs = rhs)
          then REFL lhs
          else let val {Rator,Rand=r'} = dest_comb lhs
                   val {Rator=zopr,Rand=l'} = dest_comb Rator
               in
               if (zopr = opr) 
               then let val beq = bubble l' rhs
                        val rt = Dsyntax.rhs (concl beq)
                    in TRANS (AP_TERM (mk_comb{Rator=opr,Rand=l'})
                                      (asce{lhs=rand lhs, rhs=rand rt}))
                             (SYM beq)
                    end
               else raise CONV_ERR{function="AC_CONV.asce",message=""}
               end
   in
   EQT_INTRO (EQ_MP (SYM init) (asce (dest_eq gl)))
   end
   handle _ => raise CONV_ERR{function="AC_CONV",message =""};

(*-----------------------------------------------------------------------*)
(* GSYM - General symmetry rule                                          *)
(*                                                                       *)
(* Reverses the first equation(s) encountered in a top-down search.      *)
(*                                                                       *)
(* [JRH 92.03.28]                                                        *)
(*-----------------------------------------------------------------------*)

val GSYM = CONV_RULE(ONCE_DEPTH_CONV SYM_CONV);

end; (* Conv *)
