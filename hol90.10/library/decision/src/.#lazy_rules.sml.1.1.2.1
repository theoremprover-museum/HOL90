(****************************************************************************)
(*                                                                          *)
(*               Copyright 1995, 1996 University of Cambridge               *)
(*                                                                          *)
(*                           All rights reserved.                           *)
(*                                                                          *)
(****************************************************************************)

(****************************************************************************)
(* FILE          : lazy_rules.sml                                           *)
(* DESCRIPTION   : Inference rules over lazy theorems.                      *)
(*                                                                          *)
(* AUTHOR        : R.J.Boulton                                              *)
(* DATE          : 6th June 1995                                            *)
(*                                                                          *)
(* LAST MODIFIED : R.J.Boulton                                              *)
(* DATE          : 19th August 1996                                         *)
(****************************************************************************)

structure LazyRules =
struct

local

open Exception Lib CoreHol.Term CoreHol.Dsyntax Psyntax LazyThm;

fun failwith function = raise HOL_ERR{origin_structure = "LazyRules",
                                      origin_function = function,
                                      message = ""}
and failwith_message function message =
   raise HOL_ERR{origin_structure = "LazyRules",
                 origin_function = function,
                 message = message};


fun assume tm =
   if (type_of tm = bool)
   then ([tm],tm)
   else failwith "ASSUME";

fun refl tm = ([],mk_eq (tm,tm));

fun disch w (hyps,conc) =
   (filter (not o aconv w) hyps,mk_imp (w,conc))
   handle HOL_ERR _ => failwith "DISCH";

fun mp (hypsi,conci) (hyps,conc) =
   let val (t1,t2) = dest_imp conci
   in  if (aconv t1 conc)
       then (union hypsi hyps,t2)
       else failwith ""
   end
   handle HOL_ERR _ => failwith "MP";

fun sym (hyps,conc) =
   let val (t1,t2) = dest_eq conc
   in  (hyps,mk_eq (t2,t1))
   end
   handle HOL_ERR _ => failwith "SYM";

fun trans (hyps1,conc1) (hyps2,conc2) =
   let val (l1,r1) = dest_eq conc1
       and (l2,r2) = dest_eq conc2
   in  if (aconv r1 l2)
       then (union hyps1 hyps2,mk_eq (l1,r2))
       else failwith ""
   end
   handle HOL_ERR _ => failwith "TRANS";

fun ap_term tm (hyps,conc) =
   let val (l,r) = dest_eq conc
   in  (hyps,mk_eq (mk_comb (tm,l),mk_comb (tm,r)))
   end
   handle HOL_ERR _ => failwith "AP_TERM";

fun eq_mp (hypse,conce) (hyps,conc) =
   let val (t1,t2) = dest_eq conce
   in  if (aconv t1 conc)
       then (union hypse hyps,t2)
       else failwith ""
   end
   handle HOL_ERR _ => failwith "EQ_MP";

fun spec tm (hyps,conc) =
   let val (Rator,Rand) = dest_comb conc
   in  if (#Name (Rsyntax.dest_const Rator) = "!")
       then (hyps,beta_conv (mk_comb (Rand,tm)))
       else failwith ""
   end
   handle HOL_ERR _ => failwith "SPEC";

fun specl L b = rev_itlist spec L b;

fun spec_all (gl as (hyps,conc)) =
   let fun f v (vs,l) =
          let val v' = variant vs v
          in  (v' :: vs,v' :: l)
          end
       val hvs = free_varsl hyps
       and fvs = free_vars conc
       and vars = fst (strip_forall conc)
   in  specl (snd (itlist f vars (hvs @ fvs,[]))) gl
   end;

local val T = mk_const ("T",bool)
in
fun eqt_intro (hyps,conc) = ((hyps,mk_eq (conc,T))
                              handle HOL_ERR _ => failwith "EQT_INTRO")
end;

local val F = mk_const ("F",bool)
in
fun eqf_intro (hyps,conc) =
          ((hyps,mk_eq (dest_neg conc,F))
           handle HOL_ERR _ => failwith "EQF_INTRO")
end;

fun conj (hyps1,conc1) (hyps2,conc2) =
   (union hyps1 hyps2,mk_conj (conc1,conc2))
   handle HOL_ERR _ => failwith "CONJ";

fun prove_hyp (agl as (_,ac)) bgl = mp (disch ac bgl) agl;

fun conjuncts (hyps,conc) = map (fn conj => (hyps,conj)) (strip_conj conc);

fun mk_comb' (hypsf,concf) (hypsx,concx) =
   let val (f1,f2) = dest_eq concf
       and (x1,x2) = dest_eq concx
   in  (union hypsf hypsx,
        mk_eq (mk_comb (f1,x1),mk_comb (f2,x2)))
   end
   handle _ => failwith "MK_COMB";

fun disj_cases (hypsd,concd) (hypsa,conca) (hypsb,concb) =
   if (is_disj concd) andalso (aconv conca concb)
   then let val (disj1,disj2) = dest_disj concd
        in  (union hypsd (union (Drule.disch (disj1,hypsa))
                                (Drule.disch (disj2,hypsb))),
             conca)
        end
   else failwith "DISJ_CASES";

in

fun ASSUME tm = mk_pre_thm (assume tm,fn () => CoreHol.Thm.ASSUME tm);

fun REFL tm = mk_pre_thm (refl tm,fn () => CoreHol.Thm.REFL tm);

fun DISCH w = apply_rule1 (disch w,CoreHol.Thm.DISCH w);

fun MP th1 th2 = apply_rule2 (mp,CoreHol.Thm.MP) th1 th2;

fun SYM th = apply_rule1 (sym,Drule.SYM) th;

fun TRANS th1 th2 = apply_rule2 (trans,Drule.TRANS) th1 th2;

fun AP_TERM tm = apply_rule1 (ap_term tm,Drule.AP_TERM tm);

fun EQ_MP th1 th2 = apply_rule2 (eq_mp,Drule.EQ_MP) th1 th2;

fun SPEC tm = apply_rule1 (spec tm,Drule.SPEC tm);

fun SPECL tms = apply_rule1 (specl tms,Drule.SPECL tms);

fun SPEC_ALL th = apply_rule1 (spec_all,Drule.SPEC_ALL) th;

fun EQT_INTRO th = apply_rule1 (eqt_intro,Drule.EQT_INTRO) th;

fun EQF_INTRO th = apply_rule1 (eqf_intro,Drule.EQF_INTRO) th;

fun CONJ th1 th2 = apply_rule2 (conj,Drule.CONJ) th1 th2;

fun PROVE_HYP th1 th2 = apply_rule2 (prove_hyp,Drule.PROVE_HYP) th1 th2;

fun CONJUNCTS th = apply_rule1_multi_result (conjuncts,Drule.CONJUNCTS) th;

fun MK_COMB p = 
            uncurry (apply_rule2 (mk_comb',curry Drule.MK_COMB)) p;

fun DISJ_CASES th1 th2 th3 = 
               apply_rule3 (disj_cases,Drule.DISJ_CASES) th1 th2 th3;

fun CONV_RULE conv th = EQ_MP (conv (concl th)) th;

end;

end; (* LazyRules *)
