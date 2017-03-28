(* ===================================================================== *)
(* FILE          : drule.sml                                             *)
(* DESCRIPTION   : Derived theorems and rules. (Proper derivations are 	 *)
(*		   given as comments.) Combines both hol-drule.ml and    *)
(*                 drul.ml from hol88. This file really should be a      *)
(*                 single structure, but NJSML runs out of memory after  *)
(*                 building a 33Meg heap. I have split it up into 4      *)
(*                 structures. Translated from hol88.                    *)
(*                                                                       *)
(* AUTHORS       : (c) Mike Gordon and                                   *)
(*                     Tom Melham, University of Cambridge, for hol88    *)
(* TRANSLATOR    : Konrad Slind, University of Calgary                   *)
(* DATE          : September 11, 1991                                    *)
(* ===================================================================== *)


structure Drule1 :Drule1_sig =
struct
open CoreHol;
open Exception
open Lib;
open Thm;
open Dsyntax;
open Term;
open Parse;

infix 5 |->;

structure Thm = Thm;

val alpha = Type.mk_vartype"'a";

fun DRULE_ERR{function,message} = HOL_ERR{origin_structure = "Drule",
					  origin_function = function,
					  message = message}

(*---------------------------------------------------------------------------
 *  Add an assumption
 *
 *      A |- t'
 *   -----------
 *    A,t |- t'
 *
 *fun ADD_ASSUM t th = MP (DISCH t th) (ASSUME t);
 *---------------------------------------------------------------------------*)
fun ADD_ASSUM t th = 
  let val th' = mk_drule_thm(union [t] (hyp th), concl th)
  in Thm.note(STEP{Name="ADDASSUM", Just=[JA_TERM t, JA_THM th], Thm=th'}, th')
  end;


(*---------------------------------------------------------------------------
 *  Undischarging
 *
 *   A |- t1 ==> t2
 *   -------------
 *    A, t1 |- t2
 *---------------------------------------------------------------------------*)
fun UNDISCH th = MP th (ASSUME(#ant(dest_imp(concl th))))
                 handle _ => raise DRULE_ERR{function = "UNDISCH",
					     message = ""};

(*---------------------------------------------------------------------------
 *  Symmetry of =
 *
 *       A |- t1 = t2
 *     ----------------
 *       A |- t2 = t1
 *
 *fun SYM th =
 *   let val (t1,t2) = dest_eq(concl th)
 *       val v = genvar(type_of t1)
 *   in
 *   SUBST [(th,v)] (mk_eq(v,t1)) (REFL t1)
 *   end
 *   handle _ => raise DRULE_ERR{function = "SYM",message = ""};
 *---------------------------------------------------------------------------*)
fun SYM th =
   let val (hyps,conc) = dest_thm th
       val {lhs,rhs} = dest_eq conc
       val th' = mk_drule_thm (hyps, mk_eq {lhs = rhs, rhs = lhs})
   in
     Thm.note (STEP{Name="SYM", Just=[JA_THM th], Thm=th'}, th')
   end 
   handle _ => raise DRULE_ERR{function = "SYM",message = ""};

(*---------------------------------------------------------------------------
 * Transitivity of =
 *
 *   A1 |- t1 = t2  ,  A2 |- t2 = t3
 *  ---------------------------------
 *        A1 u A2 |- t1=t3
 *
 *fun TRANS th1 th2 =
 *   let val (t1,t2) = dest_eq(concl th1)
 *       and (t2',t3) = dest_eq(concl th2)
 *       val v = genvar(type_of t1)
 *   in
 *   SUBST [(th2,v)] (mk_eq(t1,v)) th1
 *   end
 *   handle _ => raise DRULE_ERR{function = "TRANS",message = ""};
 *
 *ml_curried_infix `TRANS`;
 *
 *Note: for hol90 I made TRANS prefix  -- KLS
 *---------------------------------------------------------------------------*)
fun TRANS th1 th2 =
   let val (h1,c1) = dest_thm th1
       and (h2,c2) = dest_thm th2
       val {lhs = lhs1, rhs = rhs1} = dest_eq c1
       and {lhs = lhs2, rhs = rhs2} = dest_eq c2
       and hyps = union h1 h2
   in
   if (aconv rhs1 lhs2)
   then let val th' = mk_drule_thm(hyps,mk_eq{lhs = lhs1, rhs = rhs2})
        in Thm.note (STEP{Name="TRANS", Just=[JA_THM th1, JA_THM th2],
                          Thm=th'}, th')
        end
   else raise DRULE_ERR{function = "TRANS",message = ""}
   end
   handle _ => raise DRULE_ERR{function = "TRANS",message = ""};


(*---------------------------------------------------------------------------
 * Transitivity of ==>
 *
 *   A1 |- t1 ==> t2            A2 |- t2 ==> t3
 * ---------------------------------------------
 *           A1 u A2 |- t1 ==> t3
 *
 *fun IMP_TRANS th1 th2 =
 *   let val (t1,t2) = dest_imp(concl th1)
 *   in
 *   DISCH t1 (MP th2 (MP th1 (ASSUME t1)))
 *   end
 *   handle _ => raise DRULE_ERR("IMP_TRANS","");
 *---------------------------------------------------------------------------*)

(*---------------------------------------------------------------------------
 *  Modified: TFM 88.10.08 to use "union A1 A1" instead of A1 @ A2 
 *---------------------------------------------------------------------------*)
fun IMP_TRANS th1 th2 =
 let val (A1, c1) = dest_thm th1
     val {ant, conseq} = dest_imp c1
     val (A2,c2) = dest_thm th2
     val {ant = ant', conseq = conseq'} = dest_imp c2
 in
 if (aconv conseq ant')
 then let val th' = mk_drule_thm(union A1 A2, mk_imp{ant=ant, conseq=conseq'})
      in Thm.note(STEP{Name="IMPTRANS", Just=[JA_THM th1, JA_THM th2],
                       Thm=th'}, th')
      end
 else raise DRULE_ERR{function = "IMP_TRANS",message = ""}
 end
 handle _ => raise DRULE_ERR{function = "IMP_TRANS",message = ""};


(*---------------------------------------------------------------------------
 * Application of a term to a theorem
 *
 *    A |- t1 = t2
 * ------------------
 *  A |- t t1 = t t2
 *
 *fun AP_TERM tm th = 
 *   let val (t1,_) = dest_eq(concl th)
 *       val th1 = REFL (--`^tm ^t1`--)
 *       (* th1 = |- t t1 = t t1 *)
 *       and v  = genvar(type_of t1)
 *   in
 *   SUBST [(th,v)] (--`^tm ^t1 = ^tm ^v`--) th1
 *   end
 *   handle _ => raise DRULE_ERR{function = "AP_TERM",message = ""};
 *---------------------------------------------------------------------------*)
fun AP_TERM tm th =
 let val {lhs,rhs} = dest_eq(concl th)
     val th' = mk_drule_thm(hyp th, 
                   mk_eq{lhs = mk_comb{Rator=tm, Rand=lhs},
                         rhs = mk_comb{Rator = tm, Rand = rhs}})
 in Thm.note (STEP{Name="APTERM", Just=[JA_TERM tm, JA_THM th], Thm=th'}, th')
 end
 handle _ => raise DRULE_ERR{function="AP_TERM", message=""};


(*---------------------------------------------------------------------------
 * Application of a theorem to a term
 *
 *    A |- t1 = t2
 *   ----------------
 *   A |- t1 t = t2 t
 *
 *fun AP_THM th tm =
 *   let val (t1,_) = dest_eq(concl th)
 *       val th1 = REFL (--`^t1 ^tm`--)
 *       (* th1 = |- t1 t = t1 t *)
 *       and v   = genvar(type_of t1)
 *   in
 *   SUBST [(th,v)] (--`^t1 ^tm = ^v ^tm`--) th1
 *   end
 *   handle _ => raise DRULE_ERR{function = "AP_THM",message = ""};
 *---------------------------------------------------------------------------*)
fun AP_THM th tm =
   let val {lhs,rhs} = dest_eq(concl th)
       val th' = mk_drule_thm(hyp th, 
                    mk_eq{lhs = mk_comb{Rator = lhs, Rand = tm},
                          rhs = mk_comb{Rator = rhs, Rand = tm}})
   in Thm.note (STEP{Name="APTHM", Just=[JA_THM th, JA_TERM tm],Thm=th'}, th')
   end
   handle _ => raise DRULE_ERR{function = "AP_THM",message = ""};

(*---------------------------------------------------------------------------
 *  Modus Ponens for =
 *
 *
 *   A1 |- t1 = t2  ,  A2 |- t1
 *  ----------------------------
 *        A1 u A2 |- t2
 *
 *fun EQ_MP th1 th2 =
 *   let val (t1,t2) = dest_eq(concl th1)
 *       val v = genvar(type_of t1)
 *   in
 *   SUBST [(th1,v)] v th2
 *   end
 *   handle _ => raise DRULE_ERR{function = "EQ_MP",message = ""};
 *---------------------------------------------------------------------------*)
fun EQ_MP th1 th2 =
 let val {lhs,rhs} = dest_eq(concl th1)
     and t1'       = concl th2
 in
 if (aconv lhs t1')
 then let val th' = mk_drule_thm(union(hyp th1)(hyp th2), rhs)
     in Thm.note(STEP{Name="EQMP", Just=[JA_THM th1, JA_THM th2], Thm=th'},th')
    end
 else raise DRULE_ERR{function = "EQ_MP",message = ""}
 end
 handle _ => raise DRULE_ERR{function = "EQ_MP",message = ""};


(*---------------------------------------------------------------------------
 *              A |- t1 = t2
 *    ------------------------------------
 *     A |- t1 ==> t2      A |- t2 ==> t1
 *
 *fun EQ_IMP_RULE th =
 *   let val (t1,t2) = dest_eq(concl th)
 *   in
 *   (DISCH t1 (EQ_MP th (ASSUME t1)), DISCH t2 (EQ_MP(SYM th)(ASSUME t2)))
 *   end
 *   handle _ => raise DRULE_ERR{function = "EQ_IMP_RULE",message = ""};
 *---------------------------------------------------------------------------*)
fun EQ_IMP_RULE th =
  let val {lhs,rhs} = dest_eq(concl th)
      and A = hyp th
      val thl = mk_drule_thm(A,mk_imp{ant=lhs, conseq=rhs})
      val thr = mk_drule_thm(A,mk_imp{ant=rhs, conseq=lhs})
  in
    (Thm.note(STEP{Name="EQIMPRULEL", Just=[JA_THM th], Thm=thl},thl),
     Thm.note(STEP{Name="EQIMPRULER", Just=[JA_THM th], Thm=thr},thr))
  end
   handle _ => raise DRULE_ERR{function = "EQ_IMP_RULE",message = ""};

(*---------------------------------------------------------------------------
 *  |- T (type of "x" set to ":bool" for HOL88) 
 *---------------------------------------------------------------------------*)
val TRUTH = EQ_MP (SYM boolThry.T_DEF) (REFL (--`\x:bool. x`--));


(*---------------------------------------------------------------------------
 * =T elimination
 *
 *   A |- t = T
 *  ------------
 *    A |- t
 *---------------------------------------------------------------------------*)
fun EQT_ELIM th = EQ_MP (SYM th) TRUTH
                  handle _ => raise DRULE_ERR{function = "EQT_ELIM",
					      message = ""};

(*---------------------------------------------------------------------------
 * Specialization
 *
 *    A |- !(\x.u)
 *  --------------------   (where t is free for x in u)
 *    A |- u[t/x]
 *
 *fun SPEC t th =
 *   let val {Rator=F,Rand=body} = dest_comb(concl th)
 *   in
 *   if (not(#Name(dest_const F)="!"))
 *   then raise DRULE_ERR{function = "SPEC",message = ""}
 *   else let val {Bvar=x,Body=u} = dest_abs body
 *        and v1 = genvar(type_of F)
 *        and v2 = genvar(type_of body)
 *        val th1 = SUBST[{var = v1,
 *                         thm = INST_TYPE[{redex   = (==`:'a`==),
 *                                          residue = type_of x}] FORALL_DEF}]
 *                       (--`^v1 ^body`--) th
 *        (* th1 = |- (\P. P = (\x. T))(\x. t1 x) *)
 *        val th2 = BETA_CONV(concl th1)
 *        (* th2 = |- (\P. P = (\x. T))(\x. t1 x) = ((\x. t1 x) = (\x. T)) *)
 *        val th3 = EQ_MP th2 th1
 *        (* th3 = |- (\x. t1 x) = (\x. T) *)
 *        val th4 = SUBST [{var= v2, thm=th3}] (--`^body ^t = ^v2 ^t`--) 
 *                        (REFL (--`^body ^t`--))
 *        (* th4 = |- (\x. t1 x)t = (\x. T)t *)
 *        val {lhs=ls,rhs=rs} = dest_eq(concl th4)
 *        val th5 = TRANS(TRANS(SYM(BETA_CONV ls))th4)(BETA_CONV rs)
 *        (* th5 = |- t1 t = T *)
 *        in
 *        EQT_ELIM th5
 *        end
 *   end
 *   handle _ => raise DRULE_ERR{function = "SPEC",message = ""};
 *
 *
 *pre-dB manner:
 *fun SPEC t th =  
 *   let val {Bvar,Body} = dest_forall(concl th) 
 *   in
 *   mk_drule_thm(hyp th, subst[{redex = Bvar, residue = t}] Body)
 *   end
 *   handle _ => raise DRULE_ERR{function = "SPEC",message = ""};
 *---------------------------------------------------------------------------*)
fun SPEC t th =  
   let val {Rator,Rand} = dest_comb(concl th)
       val {Name="!",...} = dest_const Rator
       val th' = mk_drule_thm(hyp th, beta_conv(mk_comb{Rator=Rand, Rand=t}))
   in 
     Thm.note (STEP{Name="SPEC", Just=[JA_TERM t, JA_THM th], Thm=th'}, th')
   end
   handle _ => raise DRULE_ERR{function = "SPEC",message = ""};



(*---------------------------------------------------------------------------
 *
 *      |- !x1 ... xn. t[xi]
 *    --------------------------	SPECL [t1; ...; tn]
 *          |-  t[ti]
 *---------------------------------------------------------------------------*)
fun SPECL tm_list th = rev_itlist SPEC tm_list th handle _ 
                       => raise DRULE_ERR{function = "SPECL",message = ""};


(*---------------------------------------------------------------------------
 * Introduce  =T
 *
 *     A |- t
 *   ------------
 *     A |- t=T
 *
 *fun EQT_INTRO th =
 *   let val t = concl th
 *   in
 *   MP (MP(SPEC (--`T`--) (SPEC t IMP_ANTISYM_AX))
 *         (DISCH t TRUTH))
 *      (DISCH (--`T`--) th)
 *   end;
 *---------------------------------------------------------------------------*)
local val T = --`T`--
in
fun EQT_INTRO th = 
  let val th' = mk_drule_thm(hyp th, mk_eq{lhs = concl th, rhs = T})
  in Thm.note (STEP{Name="EQTINTRO", Just=[JA_THM th], Thm=th'}, th')
  end handle _ => raise DRULE_ERR{function = "EQT_INTRO", message = ""}
end;

(*---------------------------------------------------------------------------
 * Generalization  - This does not work in HOL88
 *
 *         A |- t
 *   -------------------   (where x not free in A)
 *       A |- !(\x.t)
 *
 *fun GEN x th =
 *   let val th1 = ABS x (EQT_INTRO th)
 *     (* th1 = |- (\x. t1 x) = (\x. T)  --ABS does not behave this way --KLS*)
 *      val abs = `\^x. ^(concl th)`
 *      and v1 = genvar `:(^(type_of x) -> bool) -> bool`
 *      and v2 = genvar `:bool`
 *      val th2 = SUBST [(INST_TYPE[(type_of x, `:'a`)]FORALL_DEF,v1)]
 *                      `($! ^abs) = (^v1 ^abs)`
 *                      (REFL `$! ^abs`)
 *      (* th2 = |- (!x. t1 x) = (\P. P = (\x. T))(\x. t1 x) *)
 *      val th3 = TRANS th2 (BETA_CONV(snd(dest_eq(concl th2))))
 *      (* th3 = |- (!x. t1 x) = ((\x. t1 x) = (\x. T)) *)
 *      in
 *      SUBST [(SYM th3, v2)] v2 th1
 *      end
 *      handle _ => raise DRULE_ERR{function = "GEN",message = ""};
 *---------------------------------------------------------------------------*)
fun GEN x th = 
  if (Portable.List.exists (free_in x) (hyp th))
   then raise DRULE_ERR{function = "GEN",message = ""}
   else let val th' = mk_drule_thm(hyp th, mk_forall{Bvar=x, Body=concl th})
        in Thm.note(STEP{Name="GEN",Just=[JA_TERM x, JA_THM th],Thm=th'},th')
        end handle _ => raise DRULE_ERR{function = "GEN",message = ""};

val GENL = itlist GEN;

(*---------------------------------------------------------------------------
 * Simple version of alpha-conversion (needed for deriving ETA_CONV)
 *
 *       "\x1. t x1"   "\x2. t x2"   --->   |- "(\x1.t x1)=(\x2.t x2)"
 *
 *fun SIMPLE_ALPHA(t1,t2) =
 *   let val (x1,body1) = dest_abs t1
 *       and (x2,body2) = dest_abs t2
 *       val th1 = BETA_CONV `^t1 (x:^(type_of x1))`
 *       (* th1 = |- (\x1. t x1)x = t x *)
 *       and th2 = BETA_CONV `^t2 (x:^(type_of x2))`
 *       (* th2 = |- (\x2. t x2)x = t x *)
 *       and th3 = SPEC t1 (INST_TYPE [(type_of x1, `:'a`),
 *                                     (type_of body1, `:'b`)] ETA_AX)
 *       (* th3 = |- (\x. (\x1. t x1)x) = (\x1. t x1) *)
 *       and th4 = SPEC t2 (INST_TYPE [(type_of x2, `:'a`),
 *                                     (type_of body2, `:'b`)] ETA_AX)
 *       (* th4 = |- (\x. (\x2. t x2)x) = (\x2. t x2) *)
 *   in
 *   TRANS (TRANS (SYM th3) 
 *                (ABS `x:^(type_of x1)` (TRANS th1 (SYM th2))))
 *         th4
 *   end
 *   handle _ => raise DRULE_ERR{function = "SIMPLE_ALPHA",message = ""};
 *---------------------------------------------------------------------------*)

(*---------------------------------------------------------------------------
 * Eta-conversion
 *
 * 	"(\x.t x)"   --->    |- (\x.t x) = t  (if x not free in t)
 *
 *fun ETA_CONV (tm as Abs(Var(vty,_), cmb as Comb(t,_))) =
 *      (let val body_ty = type_of cmb
 *           val th = SPEC t (INST_TYPE [(vty,`:'a`), (body_ty, `:'b`)] ETA_AX)
 *           (* th = |- (\x. t x) = t *)
 *       in
 *       TRANS (SIMPLE_ALPHA(tm,lhs(concl th))) th
 *       end
 *       handle _ => raise DRULE_ERR{function = "ETA_CONV",message = ""})
 *  | ETA_CONV _ = raise DRULE_ERR{function = "ETA_CONV",message = ""};
 *
 *---------------------------------------------------------------------------*)
fun ETA_CONV tm =
   let val {Bvar,Body} = dest_abs tm
       val {Rator, Rand} = dest_comb Body
   in
   if ((Bvar = Rand) andalso (not(mem Bvar (free_vars Rator))))
   then let val th' = mk_drule_thm([], mk_eq{lhs = tm, rhs = Rator})
        in Thm.note (STEP{Name="ETACONV", Just=[JA_TERM tm], Thm=th'},th')
        end
   else raise DRULE_ERR{function = "ETA_CONV",message = ""}
   end
   handle _ => raise DRULE_ERR{function = "ETA_CONV",message = ""};

(*---------------------------------------------------------------------------
 * Extensionality
 *
 *     A |- !x. t1 x = t2 x
 *    ----------------------     (x not free in A, t1 or t2)
 *        A |- t1 = t2
 *
 *fun EXT th =
 *   let val (x,_) = dest_forall(concl th)
 *       val th1 = SPEC x th
 *       (* th1 = |- t1 x = t2 x *)
 *       val (t1x,t2x) = dest_eq(concl th1)
 *       val x = snd(dest_comb t1x)
 *       val th2 = ABS x th1
 *       (* th2 = |- (\x. t1 x) = (\x. t2 x) *)
 *   in
 *   TRANS (TRANS(SYM(ETA_CONV `\(^x). ^t1x`))th2)
 *         (ETA_CONV `\(^x). ^t2x`)
 *   end
 *   handle _ => raise DRULE_ERR{function = "EXT",message = ""};
 *---------------------------------------------------------------------------*)
fun EXT th =
   let val {Bvar,Body} = dest_forall(concl th)
       val {lhs,rhs} = dest_eq Body
       val {Rator = Rator1, Rand = v1} = dest_comb lhs
       val {Rator = Rator2, Rand = v2} = dest_comb rhs
       val fv = union (free_vars Rator1) (free_vars Rator2)
   in
   if (not(mem Bvar fv) andalso (Bvar = v1) andalso (Bvar = v2))
   then let val th' = mk_drule_thm(hyp th, mk_eq{lhs = Rator1, rhs = Rator2})
        in Thm.note (STEP{Name="EXT", Just=[JA_THM th], Thm=th'},th')
        end
   else raise DRULE_ERR{function = "EXT",message = ""}
   end
   handle _ => raise DRULE_ERR{function = "EXT",message = ""};

(*---------------------------------------------------------------------------
 * SELECT introduction
 *
 *    A |- P t
 *  -----------------
 *   A |- P($@ P)
 *---------------------------------------------------------------------------*)
local fun alpha_subst ty = [alpha |-> ty]
in
fun SELECT_INTRO th =
 let val {Rator, Rand} = dest_comb(concl th)
     val SELECT_AX' = INST_TYPE (alpha_subst (type_of Rand)) boolThry.SELECT_AX
 in
   MP (SPEC Rand (SPEC Rator SELECT_AX')) th end
   handle _ => raise DRULE_ERR{function = "SELECT_INTRO",message = ""}
end;


(*---------------------------------------------------------------------------
 * SELECT elimination (cases)
 *
 *   A1 |- P($? P)    ,    A2, "P v" |- t
 *  ------------------------------------------ (v occurs nowhere)
 *              A1 u A2 |- t
 *---------------------------------------------------------------------------*)
fun SELECT_ELIM th1 (v,th2) =
  let val {Rator, Rand} = dest_comb(concl th1)
      val th3 = DISCH (mk_comb{Rator = Rator, Rand = v}) th2
      (* th3 = |- P v ==> t *)
  in
  MP (SPEC Rand (GEN v th3)) th1
  end
  handle _ => raise DRULE_ERR{function = "SELECT_ELIM",message = ""};


(*---------------------------------------------------------------------------
 * Existential introduction
 *
 *    A |- t[t']
 *  --------------
 *   A |- ?x.t[x]
 *
 *  The parameters are: EXISTS("?x.t[x]", "t'") (|- t[t'])
 *
 *fun EXISTS (fm,tm) th =
 *   let val (x,t) = dest_exists fm
 *       val th1 = BETA_CONV `(\(^x). ^t) ^tm`
 *       (* th1 = |- (\x. t x)t' = t t' *)
 *       val th2 = EQ_MP (SYM th1) th
 *       (* th2 = |- (\x. t x)t' *)
 *       val th3 = SELECT_INTRO th2 
 *       (* th3 = |- (\x. t x)(@x. t x) *)
 *       val th4 = AP_THM(INST_TYPE[(type_of x, `:'a`)]EXISTS_DEF) `\(^x).^t`
 *       (* th4 = |- (?x. t x) = (\P. P($@ P))(\x. t x) *)
 *       val th5 = TRANS th4 (BETA_CONV(snd(dest_eq(concl th4))))
 *       (* th5 = |- (?x. t x) = (\x. t x)(@x. t x) *)
 *   in
 *   EQ_MP (SYM th5) th3
 *   end
 *   handle _ => raise DRULE_ERR{function = "EXISTS",message = ""};
 *
 * Goes better with beta_conv
 * fun EXISTS (w,t) th =
 *    let val {Bvar,Body} = dest_exists w
 *    in
 *    if (aconv (subst [{redex = Bvar, residue = t}] Body) 
 *              (concl th))
 *    then mk_drule_thm(hyp th, w)
 *    else raise DRULE_ERR{function = "EXISTS",message = ""}
 *    end
 *    handle _ => raise DRULE_ERR{function = "EXISTS",message = ""};
 *---------------------------------------------------------------------------*)

fun EXISTS (w,t) th =
 let val {Rator,Rand} = dest_comb w
 in
 if (#Name(dest_const Rator) = "?")
 then if (aconv (Term.beta_conv(mk_comb{Rator=Rand, Rand=t})) (concl th))
      then let val th' = mk_drule_thm(hyp th, w)
           in Thm.note (STEP{Name="EXISTS",
                    Just=[JA_TERM w, JA_TERM t, JA_THM th], Thm=th'}, th')
           end
      else raise DRULE_ERR{function = "EXISTS",
                           message = "incompatible structure"}
 else raise DRULE_ERR{function = "EXISTS",message = "not an existential"}
   end;


(*---------------------------------------------------------------------------
 * Existential elimination
 *
 *   A1 |- ?x.t[x]   ,   A2, "t[v]" |- t'
 *   ------------------------------------     (variable v occurs nowhere)
 *            A1 u A2 |- t'
 *
 *fun CHOOSE (v,th1) th2 =
 *   let val (x,body) = dest_exists(concl th1)
 *       and t'     = concl th2
 *       and v1     = genvar `:bool`
 *       val th3 = AP_THM(INST_TYPE[(type_of v, `:'a`)]EXISTS_DEF)`\(^x).^body`
 *       (* th3 = |- (?x. t x) = (\P. P($@ P))(\x. t x) *)
 *       val th4 = EQ_MP th3 th1
 *       (* th4 = |- (\P. P($@ P))(\x. t x) *)
 *       val th5 = EQ_MP (BETA_CONV(concl th4)) th4
 *       (* th5 = |- (\x. t x)(@x. t x) *)
 *       val th6 = BETA_CONV `(\(^x).^body)^v`
 *       (* th6 = |- (\x. t x)v = t v *)
 *       val Pa = snd(dest_eq(concl th6))
 *       val th7 = UNDISCH(SUBST [(SYM th6,v1)] `^v1 ==> ^t'` (DISCH Pa th2))
 *       (* th7 = |- t' *)
 *   in
 *   SELECT_ELIM th5 (v,th7)
 *   end
 *   handle _ => raise DRULE_ERR{function = "CHOOSE",message = ""};
 *---------------------------------------------------------------------------*)
fun disch(w,wl) = gather (not o aconv w) wl;

fun CHOOSE (v,xth) bth =
   let val {Bvar,Body} = dest_exists (concl xth)
       val bhyp = disch(subst [Bvar |-> v] Body, hyp bth)
   in
   if (not(is_var v) orelse
       (Portable.List.exists (free_in v) 
                             ((concl xth :: hyp xth)@(concl bth :: bhyp))))
   then raise DRULE_ERR{function = "CHOOSE",message = ""}
   else let val th' = mk_drule_thm(union (hyp xth) bhyp, concl bth)
        in Thm.note (STEP{Name="CHOOSE", Thm = th',
			   Just=[JA_TERM v, JA_THM xth, JA_THM bth]}, th')
        end
   end 
   handle _ => raise DRULE_ERR{function = "CHOOSE",message = ""};


(*---------------------------------------------------------------------------
 * SELECT introduction
 *
 *    A |- ?x. t[x]
 *  -----------------
 *   A |- t[@x.t[x]]
 *---------------------------------------------------------------------------*)
local fun alpha_subst ty = [alpha |-> ty]
in
fun SELECT_RULE th =
   let val (tm as {Bvar, Body}) = dest_exists(concl th)
       val v = genvar(type_of Bvar)
       val P = mk_abs tm
       val SELECT_AX' = INST_TYPE(alpha_subst(type_of Bvar)) boolThry.SELECT_AX
       val th1 = SPEC v (SPEC P SELECT_AX')
       val {ant,conseq} = dest_imp(concl th1)
       val th2 = BETA_CONV ant 
       and th3 = BETA_CONV conseq
       val th4 = EQ_MP th3 (MP th1 (EQ_MP(SYM th2)
                                         (ASSUME (rhs(concl th2)))))
   in
   CHOOSE (v,th) th4
   end
   handle _ => raise DRULE_ERR{function = "SELECT_RULE",message = ""}
end;

(*---------------------------------------------------------------------------
 *
 *   A1 |- t1 ==> t2         A2 |- t2 ==> t1
 *  -----------------------------------------
 *            A1 u A2 |- t1 = t2
 *
 *fun IMP_ANTISYM_RULE th1 th2 =
 *   let val (t1,t2) = dest_imp(concl th1)
 *   in
 *   MP (MP (SPEC t2 (SPEC t1 IMP_ANTISYM_AX)) th1) th2
 *   end
 *   handle _ => raise DRULE_ERR{function = "IMP_ANTISYM_RULE",message = ""};
 *---------------------------------------------------------------------------*)

(*---------------------------------------------------------------------------
 *  Modified: TFM 88.10.08 to use "union A1 A2" instead of A1 @ A2 
 *---------------------------------------------------------------------------*)
fun IMP_ANTISYM_RULE th1 th2 =
   let val {ant = ant1, conseq = conseq1} = dest_imp(concl th1)
       and {ant = ant2, conseq = conseq2} = dest_imp(concl th2)
   in
   if (aconv ant1 conseq2 andalso aconv ant2 conseq1)
   then let val th' = mk_drule_thm(union (hyp th1) (hyp th2), 
                                   mk_eq{lhs=ant1, rhs=conseq1}) 
        in Thm.note (STEP{Name="IMPANTISYMRULE", Thm=th',
			  Just=[JA_THM th1, JA_THM th2]}, th')
        end
   else raise DRULE_ERR{function = "IMP_ANTISYM_RULE",message = ""}
   end
   handle _ => raise DRULE_ERR{function = "IMP_ANTISYM_RULE",message = ""};


(*---------------------------------------------------------------------------
 *  |- !x. t    ---->    x', |- t[x'/x]	 
 *---------------------------------------------------------------------------*)
fun SPEC_VAR th =
   let val {Bvar,...} = dest_forall (concl th)
       val bv' = variant (free_varsl (hyp th)) Bvar
   in (bv', SPEC bv' th)
   end;


(*---------------------------------------------------------------------------
 *
 *       A |-  (!x. t1 = t2)
 *   ---------------------------
 *    A |- (?x.t1)  =  (?x.t2)
 *
 *fun MK_EXISTS bodyth =
 *   let val (x, sth) = SPEC_VAR bodyth
 *       val (a,b) = dest_eq (concl sth)
 *       val (abimp,baimp) = EQ_IMP_RULE sth
 *       fun HALF (p,q) pqimp =
 *          let val xp = mk_exists(x,p) 
 *              and xq = mk_exists(x,q)
 *          in
 *          DISCH xp (CHOOSE (x, ASSUME xp)
 *                           (EXISTS (xq,x) 
 *                                   (MP pqimp (ASSUME p))))
 *          end
 *   in
 *   IMP_ANTISYM_RULE (HALF (a,b) abimp) (HALF (b,a) baimp)
 *   end
 *   handle _ => raise DRULE_ERR{function = "MK_EXISTS",message = ""};
 *---------------------------------------------------------------------------*)
fun MK_EXISTS bodyth =
   let val {Bvar,Body} = dest_forall (concl bodyth)
       val {lhs,rhs} = dest_eq Body 
       val th' = mk_drule_thm (hyp bodyth, 
                      mk_eq{lhs = mk_exists{Bvar = Bvar, Body = lhs},
                            rhs = mk_exists{Bvar = Bvar, Body = rhs}})
   in Thm.note(STEP{Name="MKEXISTS", Just=[JA_THM bodyth], Thm=th'},th')
   end
   handle _ => raise DRULE_ERR{function = "MK_EXISTS",message = ""};


(*---------------------------------------------------------------------------
 *               A |-  t1 = t2
 *   ------------------------------------------- (xi not free in A)
 *    A |- (?x1 ... xn. t1)  =  (?x1 ... xn. t2)
 *---------------------------------------------------------------------------*)
fun LIST_MK_EXISTS l th = itlist (fn x => fn th => MK_EXISTS(GEN x th)) l th;


(*---------------------------------------------------------------------------
 * ! abstraction
 *
 *          A |- t1 = t2
 *     -----------------------
 *      A |- (!x.t1) = (!x.t2)
 *---------------------------------------------------------------------------*)
val bool = Type.mk_type{Tyop = "bool", Args = []};
fun pred_ty ty = Type.mk_type{Tyop = "fun", Args = [ty,bool]}

fun FORALL_EQ x =
   let val forall = AP_TERM(mk_const{Name = "!", 
                                     Ty = pred_ty(pred_ty(type_of x))})
   in
   fn th => forall (ABS x th)
   end
   handle _ => raise DRULE_ERR{function = "FORALL_EQ",message = ""};


(*---------------------------------------------------------------------------
 * ? abstraction
 *
 *          A |- t1 = t2
 *     -----------------------
 *      A |- (?x.t1) = (?x.t2)
 *---------------------------------------------------------------------------*)
fun EXISTS_EQ x =
   let val exists = AP_TERM(mk_const{Name = "?", 
                                     Ty = pred_ty(pred_ty(type_of x))})
   in
   fn th => exists (ABS x th)
   end
   handle _ => raise DRULE_ERR{function = "EXISTS_EQ",message = ""};


(*---------------------------------------------------------------------------
 * @ abstraction
 *
 *          A |- t1 = t2
 *     -----------------------
 *      A |- (@x.t1) = (@x.t2)
 *---------------------------------------------------------------------------*)
fun SELECT_EQ x =
 let val ty = type_of x
 in fn th => 
   AP_TERM (mk_const{Name = "@",
                     Ty = Type.mk_type{Tyop="fun", Args=[pred_ty ty,ty]}})
           (ABS x th)
 end handle _ => raise DRULE_ERR{function = "SELECT_EQ",message = ""};


(*---------------------------------------------------------------------------
 *
 *     A1 |- t1 == u1   ...   An |- tn = un       A |- t[ti]
 *    -------------------------------------------------------
 *               A1 u ... An u A |-  t[ui]
 *
 *fun GSUBS substfn ths th =
 *   let val ls = map (lhs o concl) ths
 *       val vars = map (genvar o type_of) ls
 *       val w = substfn (combine(vars,ls)) (concl th)
 *   in
 *   SUBST (combine(ths,vars)) w th
 *   end;
 *
 *---------------------------------------------------------------------------*)
local
fun GSUBS substfn ths th =
   let val (hth,cth) = dest_thm th
       val (h',s) = itlist (fn th => fn (H,L) =>
                              let val (h,c) = dest_thm th
                                  val {lhs,rhs} = dest_eq c 
                              in (union h H, (lhs |-> rhs)::L)
                              end) ths (hth,[])
       val th' = mk_drule_thm (h', substfn s cth)
   in Thm.note(STEP{Name="GSUBS", Just=JA_THM th::map JA_THM ths,Thm=th'},th')
   end
in    
fun SUBS ths th = GSUBS subst ths th handle _
                  => raise DRULE_ERR{function = "SUBS",message = ""}
fun SUBS_OCCS nlths th =
   let val (nll, ths) = unzip nlths 
   in GSUBS (subst_occs nll) ths th 
   end
   handle _ => raise DRULE_ERR{function = "SUBS_OCCS",message = ""}
end;


(*---------------------------------------------------------------------------
 *       A |- ti == ui
 *    --------------------
 *     A |- t[ti] = t[ui]
 *
 *fun SUBST_CONV thvars template tm = 
 *   SUBST thvars `^tm = ^template` (REFL tm)
 *   handle _ => raise DRULE_ERR{function = "SUBST_CONV", message = ""};
 *---------------------------------------------------------------------------*)
fun SUBST_CONV replacements template tm =
   let val (ltheta, rtheta, hyps) =
      itlist (fn {var,thm} => fn (ltheta,rtheta,hyps) =>
              let val (h,c) = dest_thm thm
                  val {lhs,rhs} = dest_eq c
              in ((var |-> lhs)::ltheta, (var |-> rhs)::rtheta, union h hyps)
              end) replacements ([],[],[])
   in 
    if (aconv (subst ltheta template) tm)
    then let val th' = mk_drule_thm(hyps, 
                           mk_eq{lhs=tm, rhs=subst rtheta template})
         in Thm.note (STEP{Name = "SUBS_CONV",
                Just=[JA_TERM template, JA_TERM tm] @ 
                     map (fn {thm,var} => JA_PAIR (JA_THM thm, JA_TERM var))
                         replacements, Thm=th'}, th')
         end
    else raise DRULE_ERR{function = "SUBST_CONV",message = ""}
   end
   handle _ => raise DRULE_ERR{function = "SUBST_CONV",message = ""};


(*---------------------------------------------------------------------------
 * Beta-conversion to the rhs of an equation
 *
 *   A |- t1 = (\x.t2)t3
 *  --------------------
 *   A |- t1 = t2[t3/x]
 *---------------------------------------------------------------------------*)
fun RIGHT_BETA th = TRANS th (BETA_CONV(#rhs(dest_eq(concl th))))
                    handle _ => raise DRULE_ERR{function = "RIGHT_BETA",
						message = ""};

(*---------------------------------------------------------------------------
 *  "(\x1 ... xn.t)t1 ... tn" --> 
 *    |- (\x1 ... xn.t)t1 ... tn = t[t1/x1] ... [tn/xn]
 *---------------------------------------------------------------------------*)
fun LIST_BETA_CONV tm =
   let val {Rator,Rand} = dest_comb tm 
   in
   RIGHT_BETA (AP_THM (LIST_BETA_CONV Rator) Rand)
   end
   handle _ => REFL tm;


fun RIGHT_LIST_BETA th = TRANS th (LIST_BETA_CONV(#rhs(dest_eq(concl th))));
end; (* Drule1 *)


structure Drule2 : Drule2_sig =
struct
open Exception
open Lib
open Parse;
open CoreHol;
open Thm;
open Dsyntax;
open Term;
open Drule1;

infix 5 |->;

fun DRULE_ERR{function,message} = HOL_ERR{origin_structure = "Drule",
					  origin_function = function,
					  message = message}

(*---------------------------------------------------------------------------
 *       |- !t1 t2. t1 ==> t2 ==> t1 /\ t2
 *---------------------------------------------------------------------------*)
val AND_INTRO_THM =
   let val t = --`t:bool`--
       and t1 = --`t1:bool`--
       and t2 = --`t2:bool`--
       val t12 = --`^t1 ==> (^t2 ==> ^t)`--
       val th1 = GEN t (DISCH t12 (MP (MP (ASSUME t12)
                                          (ASSUME t1))
                                      (ASSUME t2)))
       val th2 = RIGHT_BETA(AP_THM (RIGHT_BETA(AP_THM boolThry.AND_DEF t1)) t2)
   in
   GEN t1 (GEN t2 (DISCH t1 (DISCH t2 (EQ_MP (SYM th2) th1))))
   end;

(*---------------------------------------------------------------------------
 * Conjunction introduction rule
 *
 *   A1 |- t1  ,  A2 |- t2
 *  -----------------------
 *    A1 u A2 |- t1 /\ t2
 *
 *fun CONJ th1 th2 = MP (MP (SPEC (concl th2) (SPEC (concl th1) AND_INTRO_THM))
 *                          th1) 
 *                      th2;
 *---------------------------------------------------------------------------*)
fun CONJ th1 th2 = 
  let val th' = mk_drule_thm(union(hyp th1) (hyp th2),
                   mk_conj{conj1 = concl th1, conj2 = concl th2})
  in Thm.note (STEP{Name="CONJ", Just=[JA_THM th1, JA_THM th2], Thm=th'},th')
  end;
 

(*---------------------------------------------------------------------------
 * |- !t1 t2. t1 /\ t2 ==> t1
 *---------------------------------------------------------------------------*)
val AND1_THM =
  let val t1 = --`t1:bool`--
      and t2 = --`t2:bool`--
      val th1 = ASSUME (--`^t1 /\ ^t2`--)
      val th2 = RIGHT_BETA(AP_THM (RIGHT_BETA(AP_THM boolThry.AND_DEF t1)) t2)
      val th3 = SPEC t1 (EQ_MP th2 th1)
      val th4 = DISCH t1 (DISCH t2 (ADD_ASSUM t2 (ASSUME t1)))
  in
  GEN t1 (GEN t2 (DISCH (--`^t1 /\ ^t2`--) (MP th3 th4)))
  end;


(*---------------------------------------------------------------------------
 * Left conjunct extraction
 *
 *   A |- t1 /\ t2
 *   -------------
 *      A |- t1
 *
 *fun CONJUNCT1 th =
 *   let val (t1,t2) = dest_conj(concl th)
 *   in
 *   MP (SPEC t2 (SPEC t1 AND1_THM)) th
 *   end
 *   handle _ => raise DRULE_ERR{function = "CONJUNCT1",message = ""};
 *
 *---------------------------------------------------------------------------*)
fun CONJUNCT1 th = 
  let val th' = mk_drule_thm(hyp th, #conj1(dest_conj(concl th)))
  in Thm.note(STEP{Name="CONJUNCT1", Just=[JA_THM th], Thm=th'}, th')
  end
  handle _ => raise DRULE_ERR{function = "CONJUNCT1", message = ""};

(*---------------------------------------------------------------------------
 *    |- !t1 t2. t1 /\ t2 ==> t2 
 *---------------------------------------------------------------------------*)
val AND2_THM =
  let val t1 = --`t1:bool`--
      and t2 = --`t2:bool`--
      val th1 = ASSUME (--`^t1 /\ ^t2`--)
      val th2 = RIGHT_BETA(AP_THM (RIGHT_BETA(AP_THM boolThry.AND_DEF t1)) t2)
      val th3 = SPEC t2 (EQ_MP th2 th1)
      val th4 = DISCH t1 (DISCH t2 (ADD_ASSUM t1 (ASSUME t2)))
  in
  GEN t1 (GEN t2 (DISCH (--`^t1 /\ ^t2`--) (MP th3 th4)))
  end;


(*---------------------------------------------------------------------------
 *  Right conjunct extraction
 *
 *   A |- t1 /\ t2
 *   -------------
 *      A |- t2
 *
 *fun CONJUNCT2 th =
 *   let val (t1,t2) = dest_conj(concl th)
 *   in
 *   MP (SPEC t2 (SPEC t1 AND2_THM)) th
 *   end
 *   handle _ => raise DRULE_ERR{function = "CONJUNCT2",message = ""};
 *---------------------------------------------------------------------------*)
fun CONJUNCT2 th = 
  let val th' = mk_drule_thm(hyp th, #conj2(dest_conj(concl th))) 
  in Thm.note (STEP{Name="CONJUNCT2", Just=[JA_THM th], Thm=th'}, th')
  end
  handle _ => raise DRULE_ERR{function = "CONJUNCT2",  message = ""};

(*---------------------------------------------------------------------------
 *   |- !t1 t2. (t1 /\ t2) = (t2 /\ t1)  
 *---------------------------------------------------------------------------*)
val CONJ_SYM =
  let val t1 = --`t1:bool`--
      and t2 = --`t2:bool`--
      val th1 = ASSUME (--`^t1 /\ ^t2`--)
      and th2 = ASSUME (--`^t2 /\ ^t1`--)
  in
  GEN t1 (GEN t2 (IMP_ANTISYM_RULE
                 (DISCH (--`^t1 /\ ^t2`--)
                        (CONJ(CONJUNCT2 th1)(CONJUNCT1 th1)))
                 (DISCH (--`^t2 /\ ^t1`--)
                        (CONJ(CONJUNCT2 th2)(CONJUNCT1 th2)))))
  end;


(*---------------------------------------------------------------------------
 * |- !t1 t2 t3. t1 /\ (t2 /\ t3) = (t1 /\ t2) /\ t3 
 *---------------------------------------------------------------------------*)
val CONJ_ASSOC =
  let val t1 = --`t1:bool`--
      and t2 = --`t2:bool`--
      and t3 = --`t3:bool`--
      val th1 = ASSUME (--`^t1 /\ (^t2 /\ ^t3)`--)
      val th2 = ASSUME (--`(^t1 /\ ^t2) /\ ^t3`--)
      val th3 = DISCH (--`^t1 /\ (^t2 /\ ^t3)`--)
                   (CONJ (CONJ(CONJUNCT1 th1)
                              (CONJUNCT1(CONJUNCT2 th1)))
                         (CONJUNCT2(CONJUNCT2 th1)))
      and th4 = DISCH (--`(^t1 /\ ^t2) /\ ^t3`--)
                   (CONJ (CONJUNCT1(CONJUNCT1 th2))
                         (CONJ(CONJUNCT2(CONJUNCT1 th2))
                              (CONJUNCT2 th2)))
  in
  GEN t1 (GEN t2 (GEN t3 (IMP_ANTISYM_RULE th3 th4)))
  end;


(*---------------------------------------------------------------------------
 * let CONJUNCTS_CONV (t1,t2) =
 *  letrec CONJUNCTS th =
 *   (CONJUNCTS (CONJUNCT1 th) @ CONJUNCTS (CONJUNCT2 th)) ? [th]
 *  in
 *  letrec build_conj thl t =
 *   (let l,r = dest_conj t
 *    in  CONJ (build_conj thl l) (build_conj thl r)
 *   )
 *   ? find (\th. (concl th) = t) thl
 *  in
 *   (IMP_ANTISYM_RULE
 *     (DISCH t1 (build_conj (CONJUNCTS (ASSUME t1)) t2))
 *     (DISCH t2 (build_conj (CONJUNCTS (ASSUME t2)) t1))
 *   ) ? failwith `CONJUNCTS_CONV`;;
 *---------------------------------------------------------------------------*)

fun CONJUNCTS_CONV (t1,t2) =
   let fun CONJUNCTS th = (CONJUNCTS (CONJUNCT1 th) @ CONJUNCTS (CONJUNCT2 th))
                          handle _ => [th]
       fun build_conj thl t =
          let val {conj1,conj2} = dest_conj t
           in  CONJ (build_conj thl conj1) (build_conj thl conj2)
          end handle _ => first (fn th => (concl th) = t) thl
   in
   IMP_ANTISYM_RULE (DISCH t1 (build_conj (CONJUNCTS (ASSUME t1)) t2))
                    (DISCH t2 (build_conj (CONJUNCTS (ASSUME t2)) t1))
   end
   handle _ => raise DRULE_ERR{function = "CONJUNCTS_CONV",message =""};

(*---------------------------------------------------------------------------
 * let CONJ_SET_CONV l1 l2 =
 *  CONJUNCTS_CONV (list_mk_conj l1, list_mk_conj l2)
 *  ? failwith `CONJ_SET_CONV`;;
 *
 *---------------------------------------------------------------------------*)

fun CONJ_SET_CONV l1 l2 = 
   CONJUNCTS_CONV (list_mk_conj l1, list_mk_conj l2)
   handle _ => raise DRULE_ERR{function = "CONJ_SET_CONV", message = ""};

(*---------------------------------------------------------------------------
 * let FRONT_CONJ_CONV tml t =
 *  letrec remove x l =
 *     if ((hd l) = x)
 *     then tl l
 *     else (hd l).(remove x (tl l))
 *  in
 *  (CONJ_SET_CONV tml (t.(remove t tml)))
 *  ? failwith `FRONT_CONJ_CONV`;;
 *---------------------------------------------------------------------------*)
fun FRONT_CONJ_CONV tml t =
   let fun remove x l =
          if (hd l = x)
          then tl l
          else (hd l::remove x (tl l))
   in (CONJ_SET_CONV tml (t::(remove t tml)))
   end handle _ => raise DRULE_ERR{function = "FRONT_CONJ_CONV", message = ""};

(*---------------------------------------------------------------------------
 *   |- (t1 /\ ... /\ t /\ ... /\ tn) = (t /\ t1 /\ ... /\ tn)
 * 
 * local
 * val APP_AND = AP_TERM(--`/\`--)
 * in
 * fun FRONT_CONJ_CONV tml t =
 *    if (t = hd tml)
 *    then REFL(list_mk_conj tml)
 *    else if ((null(tl(tl tml)) andalso (t = hd(tl tml))))
 *         then SPECL tml CONJ_SYM
 *         else let val th1 = APP_AND (FRONT_CONJ_CONV (tl tml) t)
 *                  val {conj1,conj2} = dest_conj(rhs(concl th1))
 *                  val {conj1 = c2, conj2 = c3} = dest_conj conj2
 *                  val th2 = AP_THM(APP_AND (SPECL[conj1,c2]CONJ_SYM)) c3
 *              in
 *              TRANS (TRANS (TRANS th1 (SPECL[conj1,c2,c3]CONJ_ASSOC)) th2)
 *                    (SYM(SPECL[c2,conj1,c3]CONJ_ASSOC))
 *              end
 *              handle _ => raise DRULE_ERR{function = "FRONT_CONJ_CONV",
 *                                          message = ""}
 * end;
 *---------------------------------------------------------------------------*)

(*---------------------------------------------------------------------------
 * |- (t1 /\ ... /\ tn) = (t1' /\ ... /\ tn') where {t1,...,tn}={t1',...,tn'} 
 * 
 * The genuine derived rule below only works if its argument
 * lists are the same length.
 * 
 * fun CONJ_SET_CONV l1 l2 =
 *    if (l1 = l2)
 *    then REFL(list_mk_conj l1)
 *   else if (hd l1 = hd l2)
 *        then AP_TERM (--`$/\ ^(hd l1)`--) (CONJ_SET_CONV(tl l1)(tl l2))
 *        else let val th1 = SYM(FRONT_CONJ_CONV l2 (hd l1))
 *                 val l2' = conjuncts(lhs(concl th1))
 *                 val th2 = AP_TERM (--`$/\ ^(hd l1)`--)
 *                                   (CONJ_SET_CONV(tl l1)(tl l2'))
 *             in
 *             TRANS th2 th1
 *             end
 *             handle _ => raise DRULE_ERR{function = "CONJ_SET_CONV",
 * 		                        message = ""};
 * 
 * fun CONJ_SET_CONV l1 l2 =
 *   (if (set_eq l1 l2)
 *    then mk_drule_thm([],mk_eq{lhs = list_mk_conj l1, rhs = list_mk_conj l2})
 *    else raise DRULE_ERR{function = "CONJ_SET_CONV",message = ""})
 *    handle _ => raise DRULE_ERR{function = "CONJ_SET_CONV",message = ""};
 *---------------------------------------------------------------------------*)


(*---------------------------------------------------------------------------
 * |- t1 = t2  if t1 and t2 are equivalent using idempotence, symmetry and 
 *                associativity of /\. I have not (yet) coded a genuine 
 *                derivation - it would be straightforward, but tedious.
 * 
 * fun CONJUNCTS_CONV(t1,t2) =
 *    if (set_eq (strip_conj t1)(strip_conj t2))
 *    then mk_drule_thm([],mk_eq{lhs = t1, rhs = t2})
 *    else raise DRULE_ERR{function = "CONJUNCTS_CONV",message = ""};
 *---------------------------------------------------------------------------*)

(*---------------------------------------------------------------------------
 *           A,t |- t1 = t2
 *    -----------------------------
 *      A |- (t /\ t1) = (t /\ t2)
 *---------------------------------------------------------------------------*)
fun CONJ_DISCH t th =
   let val {lhs,rhs} = dest_eq(concl th)
       and th1 = DISCH t th
       val left_t = mk_conj{conj1 = t, conj2 = lhs}
       val right_t = mk_conj{conj1 = t, conj2 = rhs}
       val th2 = ASSUME left_t
       and th3 = ASSUME right_t
       val th4 = DISCH left_t
                       (CONJ (CONJUNCT1 th2)
                             (EQ_MP(MP th1 (CONJUNCT1 th2))
                                   (CONJUNCT2 th2)))
       and th5 = DISCH right_t 
                       (CONJ (CONJUNCT1 th3)
                             (EQ_MP(SYM(MP th1 (CONJUNCT1 th3)))
                                   (CONJUNCT2 th3)))
   in
   IMP_ANTISYM_RULE th4 th5
   end;

(*---------------------------------------------------------------------------
 *                    A,t1,...,tn |- t = u
 *    --------------------------------------------------------
 *      A |- (t1 /\ ... /\ tn /\ t) = (t1 /\ ... /\ tn /\ u)
 *---------------------------------------------------------------------------*)
val CONJ_DISCHL = itlist CONJ_DISCH;

(*---------------------------------------------------------------------------
 *  |- !t1 t2. t1 ==> t1 \/ t2 
 *---------------------------------------------------------------------------*)
val OR_INTRO_THM1 =
  let val t = --`t:bool`--
      and t1 = --`t1:bool`--
      and t2 = --`t2:bool`--
      val th1 = ADD_ASSUM (--`^t2 ==> ^t`--) (MP (ASSUME (--`^t1 ==> ^t`--))
                                              (ASSUME t1))
      val th2 = GEN t (DISCH (--`^t1 ==> ^t`--) (DISCH (--`^t2 ==> ^t`--) th1))
      val th3 = RIGHT_BETA(AP_THM (RIGHT_BETA(AP_THM boolThry.OR_DEF t1)) t2)
  in
  GEN t1 (GEN t2 (DISCH t1 (EQ_MP (SYM th3) th2)))
  end;


(*---------------------------------------------------------------------------
 * Left disjunction introduction
 *
 *      A |- t1
 *  ---------------
 *   A |- t1 \/ t2
 *
 *fun DISJ1 th t2 = MP (SPEC t2 (SPEC (concl th) OR_INTRO_THM1)) th
 *           handle _ => raise DRULE_ERR{function = "DISJ1",message = ""};
 *---------------------------------------------------------------------------*)
fun DISJ1 th w = 
  let val th' = mk_drule_thm(hyp th, mk_disj{disj1 = concl th, disj2 = w})
  in Thm.note (STEP{Name="DISJ1", Just=[JA_THM th, JA_TERM w], Thm=th'},th')
  end;

(*---------------------------------------------------------------------------
 * |- !t1 t2. t2 ==> t1 \/ t2 
 *---------------------------------------------------------------------------*)
val OR_INTRO_THM2 =
  let val t = --`t:bool`--
      and t1 = --`t1:bool`--
      and t2 = --`t2:bool`--
      val th1 = ADD_ASSUM (--`^t1 ==> ^t`--) (MP (ASSUME (--`^t2 ==> ^t`--)) 
                                                         (ASSUME t2))
      val th2 = GEN t (DISCH (--`^t1 ==> ^t`--) (DISCH (--`^t2 ==> ^t`--) th1))
      val th3 = RIGHT_BETA(AP_THM (RIGHT_BETA(AP_THM boolThry.OR_DEF t1)) t2)
  in
  GEN t1 (GEN t2 (DISCH t2 (EQ_MP (SYM th3) th2)))
  end;


(*---------------------------------------------------------------------------
 * Right disjunction introduction
 *
 *      A |- t2
 *  ---------------
 *   A |- t1 \/ t2
 *
 *fun DISJ2 t1 th = MP (SPEC (concl th) (SPEC t1 OR_INTRO_THM2)) th
 *          handle _ => raise DRULE_ERR{function = "DISJ2",message = ""};
 *---------------------------------------------------------------------------*)
fun DISJ2 w th = 
  let val th' = mk_drule_thm(hyp th, mk_disj{disj1 = w, disj2 = concl th})
  in Thm.note (STEP{Name="DISJ2", Just=[JA_TERM w, JA_THM th], Thm=th'},th')
  end;

(*---------------------------------------------------------------------------
 * |- !t t1 t2. (t1 \/ t2) ==> (t1 ==> t) ==> (t2 ==> t) ==> t
 *---------------------------------------------------------------------------*)
val OR_ELIM_THM =
   let val t = --`t:bool`--
       and t1 = --`t1:bool`--
       and t2 = --`t2:bool`--
       val th1 = ASSUME (--`^t1 \/ ^t2`--)
       and th2 = RIGHT_BETA(AP_THM (RIGHT_BETA(AP_THM boolThry.OR_DEF t1)) t2)
       val th3 = SPEC t (EQ_MP th2 th1)
       val th4 = MP (MP th3 (ASSUME (--`^t1 ==> ^t`--)))
                    (ASSUME (--`^t2 ==> ^t`--))
       val th4 = DISCH (--`^t1 ==> ^t`--) (DISCH (--`^t2 ==> ^t`--) th4)
   in
   GEN t (GEN t1 (GEN t2 (DISCH (--`^t1 \/ ^t2`--) th4)))
   end;


(*---------------------------------------------------------------------------
 * Disjunction elimination
 *
 *   A |- t1 \/ t2   ,   A1,t1 |- t   ,   A2,t2 |- t
 *   -----------------------------------------------
 *               A u A1 u A2 |- t
 *
 *fun DISJ_CASES th1 th2 th3 =
 *   let val (t1,t2) = dest_disj(concl th1)
 *       and t = concl th2
 *       val th4 = SPEC t2 (SPEC t1 (SPEC t OR_ELIM_THM))
 *   in
 *   MP (MP (MP th4 th1) (DISCH t1 th2)) (DISCH t2 th3)
 *   end
 *   handle _ => raise DRULE_ERR{function = "DISJ_CASES",message = ""};
 *---------------------------------------------------------------------------*)
fun DISJ_CASES dth ath bth =
  if ((is_disj (concl dth)) andalso (aconv (concl ath) (concl bth)))
  then let val {disj1,disj2} = dest_disj (concl dth) 
           val th' = mk_drule_thm(union (hyp dth) 
                                        (union (disch(disj1, hyp ath))
                                               (disch(disj2, hyp bth))),
	                          concl ath)
        in Thm.note (STEP{Name="DISJCASES",
                       Just=[JA_THM dth, JA_THM ath, JA_THM bth],Thm=th'},th')
        end
  else raise DRULE_ERR{function = "DISJ_CASES",message = ""};


(*---------------------------------------------------------------------------
 * |- !t. F ==> t  
 *---------------------------------------------------------------------------*)
val FALSITY =
   let val t = --`t:bool`--
   in
   GEN t (DISCH (--`F`--) 
                (SPEC t (EQ_MP boolThry.F_DEF 
                               (ASSUME (--`F`--)))))
   end;


(*---------------------------------------------------------------------------
 * |- !t.(t ==> F) ==> ~t 
 *---------------------------------------------------------------------------*)
val IMP_F =
   let val t = --`t:bool`--
       val th1 = RIGHT_BETA(AP_THM boolThry.NOT_DEF t)
   in
   GEN t (DISCH (--`^t ==> F`--) (EQ_MP (SYM th1) (ASSUME (--`^t ==> F`--))))
   end;


(*---------------------------------------------------------------------------
 * NOT introduction
 *
 *     A |- t ==> F
 *     ------------
 *       A |- ~t
 *
 *fun NOT_INTRO th =
 *   let val (t,_) = dest_imp(concl th)
 *   in
 *   MP (SPEC t IMP_F) th
 *   end
 *   handle _ => raise DRULE_ERR{function = "NOT_INTRO",message = ""};
 *---------------------------------------------------------------------------*)
local val simply_not_the_case = --`F`--
in
fun NOT_INTRO th =
   let val {ant,conseq} = dest_imp(concl th)
   in
   if (conseq = simply_not_the_case)
   then let val th' = mk_drule_thm(hyp th, mk_neg ant)
        in Thm.note(STEP{Name="NOTINTRO", Just=[JA_THM th], Thm=th'},th')
        end
   else raise DRULE_ERR{function = "NOT_INTRO",message = ""}
   end
   handle _ => raise DRULE_ERR{function = "NOT_INTRO",message = ""}
end;


(*---------------------------------------------------------------------------
 *       A,t1 |- t2                A,t |- F
 *     --------------              --------
 *     A |- t1 ==> t2               A |- ~t
 *---------------------------------------------------------------------------*)
local val simply_not_the_case = --`F`--
in
fun NEG_DISCH t th =
  (if (concl th = simply_not_the_case) 
      then NOT_INTRO(DISCH t th) 
        else DISCH t th)
  handle _ => raise DRULE_ERR{function = "NEG_DISCH",message = ""}
end;


(*---------------------------------------------------------------------------
 * |- !t. ~t ==>(t ==> F)  
 *---------------------------------------------------------------------------*)
val F_IMP =
   let val t = --`t:bool`--
       val th1 = RIGHT_BETA(AP_THM boolThry.NOT_DEF t)
   in
   GEN t (DISCH (--`~^t`--) 
                (EQ_MP th1 (ASSUME (--`~^t`--))))
   end;


(*---------------------------------------------------------------------------
 * Negation elimination
 *
 *       A |- ~ t
 *     --------------
 *      A |- t ==> F
 *
 *fun NOT_ELIM th =
 *   let val (_,t) = dest_comb(concl th)
 *   in
 *   MP (SPEC t F_IMP) th
 *   end
 *   handle _ => raise DRULE_ERR{function = "NOT_ELIM",message = ""};
 *---------------------------------------------------------------------------*)
local val not_the_case = --`F`--
in
fun NOT_ELIM th =
   let val {Rator,Rand} = dest_comb(concl th)
   in
   if (#Name(dest_const Rator) = "~")
   then let val th' = mk_drule_thm(hyp th, 
                         mk_imp{ant = Rand, conseq = not_the_case})
        in Thm.note(STEP{Name="NOTELIM", Just=[JA_THM th], Thm=th'},th')
        end
   else raise DRULE_ERR{function = "NOT_ELIM",message = ""}
   end
   handle _ => raise DRULE_ERR{function = "NOT_ELIM",message = ""}
end;

(*---------------------------------------------------------------------------
 *    A |- ~(t1 = t2)
 *   -----------------
 *    A |- ~(t2 = t1)
 *---------------------------------------------------------------------------*)
local fun flip {lhs,rhs} = {lhs = rhs, rhs = lhs}
in
fun NOT_EQ_SYM th =
   let val t = (mk_eq o flip o dest_eq o dest_neg o concl) th
   in
   MP (SPEC t IMP_F) (DISCH t (MP th (SYM(ASSUME t))))
   end
end;

(*---------------------------------------------------------------------------
 * |- !t. (T /\ t) = t 
 *---------------------------------------------------------------------------*)
val AND_CLAUSE1 =
   let val t = --`t:bool`--
       val th1 = DISCH (--`T /\ ^t`--) (CONJUNCT2(ASSUME (--`T /\ ^t`--)))
       and th2 = DISCH t (CONJ TRUTH (ASSUME t))
   in
   GEN t (IMP_ANTISYM_RULE th1 th2)
   end;


(*---------------------------------------------------------------------------
 *  |- !t. (t /\ T) = t 
 *---------------------------------------------------------------------------*)
val AND_CLAUSE2 =
   let val t = --`t:bool`--
       val th1 = DISCH (--`^t /\ T`--) (CONJUNCT1(ASSUME (--`^t /\ T`--)))
       and th2 = DISCH t (CONJ (ASSUME t) TRUTH)
   in
   GEN t (IMP_ANTISYM_RULE th1 th2)
   end;


(*---------------------------------------------------------------------------
 *   |- !t. (F /\ t) = F 
 *---------------------------------------------------------------------------*)
val AND_CLAUSE3 =
   let val t = --`t:bool`--
       val th1 = IMP_TRANS (SPEC t (SPEC (--`F`--) AND1_THM)) 
                           (SPEC (--`F`--) FALSITY)
       and th2 = SPEC (--`F /\ ^t`--) FALSITY
   in
   GEN t (IMP_ANTISYM_RULE th1 th2)
   end;

(*---------------------------------------------------------------------------
 *   |- !t. (t /\ F) = F 
 *---------------------------------------------------------------------------*)
val AND_CLAUSE4 =
   let val t = --`t:bool`--
       val th1 = IMP_TRANS (SPEC (--`F`--) (SPEC t AND2_THM)) 
                           (SPEC (--`F`--) FALSITY)
       and th2 = SPEC (--`^t /\ F`--) FALSITY
   in
   GEN t (IMP_ANTISYM_RULE th1 th2)
   end;


(*---------------------------------------------------------------------------
 *    |- !t. (t /\ t) = t 
 *---------------------------------------------------------------------------*)
val AND_CLAUSE5 =
   let val t = --`t:bool`--
       val th1 = DISCH (--`^t /\ ^t`--) (CONJUNCT1(ASSUME (--`^t /\ ^t`--)))
       and th2 = DISCH t (CONJ(ASSUME t)(ASSUME t))
   in
   GEN t (IMP_ANTISYM_RULE th1 th2)
   end;

(*---------------------------------------------------------------------------
 *  |- !t. (T /\ t) = t /\
 *         (t /\ T) = t /\
 *         (F /\ t) = F /\
 *         (t /\ F) = F /\
 *         (t /\ t) = t
 *---------------------------------------------------------------------------*)
val AND_CLAUSES =
   let val t = --`t:bool`--
   in
   GEN t (CONJ 
           (SPEC t AND_CLAUSE1)
            (CONJ
             (SPEC t AND_CLAUSE2)
              (CONJ
               (SPEC t AND_CLAUSE3)
                 (CONJ (SPEC t AND_CLAUSE4) 
                       (SPEC t AND_CLAUSE5)))))
   end;


(*---------------------------------------------------------------------------
 *   |- !t. (T \/ t) = T 
 *---------------------------------------------------------------------------*)
val OR_CLAUSE1 =
   let val t = --`t:bool`--
       val th1 = DISCH (--`T \/ ^t`--) TRUTH
       and th2 = DISCH (--`T`--) (DISJ1 TRUTH t)
   in
   GEN t (IMP_ANTISYM_RULE th1 th2)
   end;

(*---------------------------------------------------------------------------
 *  |- !t. (t \/ T) = T 
 *---------------------------------------------------------------------------*)
val OR_CLAUSE2 =
   let val t = --`t:bool`--
       val th1 = DISCH (--`^t \/ T`--) TRUTH
       and th2 = DISCH (--`T`--) (DISJ2 t TRUTH)
   in
   GEN t (IMP_ANTISYM_RULE th1 th2)
   end;

(*---------------------------------------------------------------------------
 *    |- (F \/ t) = t 
 *---------------------------------------------------------------------------*)
val OR_CLAUSE3 =
   let val t = --`t:bool`--
       val th1 = DISCH (--`F \/ ^t`--) (DISJ_CASES (ASSUME (--`F \/ ^t`--))
                                        (UNDISCH (SPEC t FALSITY))
                                        (ASSUME t))
       and th2 = SPEC t (SPEC (--`F`--) OR_INTRO_THM2)
   in
   GEN t (IMP_ANTISYM_RULE th1 th2)
   end;

(*---------------------------------------------------------------------------
 *    |- !t. (t \/ F) = t
 *---------------------------------------------------------------------------*)
val OR_CLAUSE4 =
   let val t = --`t:bool`--
       val th1 = DISCH (--`^t \/ F`--) (DISJ_CASES (ASSUME (--`^t \/ F`--))
                                             (ASSUME t)
                                             (UNDISCH (SPEC t FALSITY)))
       and th2 = SPEC (--`F`--) (SPEC t OR_INTRO_THM1)
   in
   GEN t (IMP_ANTISYM_RULE th1 th2)
   end;

(*---------------------------------------------------------------------------
 *   |- !t. (t \/ t) = t 
 *---------------------------------------------------------------------------*)
val OR_CLAUSE5 =
   let val t = --`t:bool`--
       val th1 = DISCH (--`^t \/ ^t`--) (DISJ_CASES(ASSUME (--`^t \/ ^t`--))
                                                (ASSUME t)
                                                (ASSUME t))
       and th2 = DISCH t (DISJ1(ASSUME t)t)
   in
   GEN t (IMP_ANTISYM_RULE th1 th2)
   end;

(*---------------------------------------------------------------------------
 * |- !t. (T \/ t) = T /\
 *        (t \/ T) = T /\
 *        (F \/ t) = t /\
 *        (t \/ F) = t /\
 *        (t \/ t) = t
 *---------------------------------------------------------------------------*)
val OR_CLAUSES =
   let val t = --`t:bool`--
   in
   GEN t (CONJ 
          (SPEC t OR_CLAUSE1)
          (CONJ
           (SPEC t OR_CLAUSE2)
           (CONJ 
            (SPEC t OR_CLAUSE3)
            (CONJ (SPEC t OR_CLAUSE4) 
                  (SPEC t OR_CLAUSE5)))))
   end;


(*---------------------------------------------------------------------------
 *  |- !t. (T ==> t) = t  
 *---------------------------------------------------------------------------*)
val IMP_CLAUSE1 =
   let val t = --`t:bool`--
       val th1 = DISCH (--`T ==> ^t`--) (MP (ASSUME (--`T ==> ^t`--)) TRUTH)
       and th2 = DISCH t (DISCH (--`T`--) (ADD_ASSUM (--`T`--) (ASSUME t)))
       and th3 = SPEC t (SPEC (--`T ==> ^t`--) boolThry.IMP_ANTISYM_AX)
   in
   GEN t (MP (MP th3 th1) th2)
   end;

(*---------------------------------------------------------------------------
 *  |- !t. (F ==> t) = T 
 *---------------------------------------------------------------------------*)
val IMP_CLAUSE2 =
   let val t = --`t:bool`--
   in
   GEN t (EQT_INTRO(SPEC t FALSITY))
   end;

(*---------------------------------------------------------------------------
 *  |- !t. (t ==> T) = T 
 *---------------------------------------------------------------------------*)
val IMP_CLAUSE3 =
   let val t = --`t:bool`--
   in
   GEN t (EQT_INTRO(DISCH t (ADD_ASSUM t TRUTH)))
   end;

(*---------------------------------------------------------------------------
 *  |- ((T ==> F) = F) /\ ((F ==> F) = T) 
 *---------------------------------------------------------------------------*)
val IMP_CLAUSE4 =
   let val th1 = DISCH (--`T ==> F`--) (MP (ASSUME (--`T ==> F`--)) TRUTH)
       and th2 = SPEC (--`T ==> F`--) FALSITY
       and th3 = EQT_INTRO(DISCH (--`F`--) (ASSUME (--`F`--)))
   in
   CONJ(MP (MP (SPEC (--`F`--)
               (SPEC (--`T ==> F`--) boolThry.IMP_ANTISYM_AX)) th1) th2) th3
   end;

(*---------------------------------------------------------------------------
 *  |- !t. (t ==> F) = ~t 
 *---------------------------------------------------------------------------*)
val IMP_CLAUSE5 =
    let val t = --`t:bool`--
        val th1 = SPEC t IMP_F
        and th2 = SPEC t F_IMP
    in
    GEN t (IMP_ANTISYM_RULE th1 th2)
    end;

(*---------------------------------------------------------------------------
 *  |- !t. (T ==> t) = t /\
 *         (t ==> T) = T /\
 *         (F ==> t) = T /\
 *         (t ==> t) = t /\
 *         (t ==> F) = ~t
 *---------------------------------------------------------------------------*)
val IMP_CLAUSES =
   let val t = --`t:bool`--
   in GEN t
      (CONJ (SPEC t IMP_CLAUSE1)
            (CONJ (SPEC t IMP_CLAUSE3)
                  (CONJ (SPEC t IMP_CLAUSE2)
                        (CONJ (EQT_INTRO(DISCH t (ASSUME t)))
                              (SPEC t IMP_CLAUSE5)))))
   end;

(*---------------------------------------------------------------------------
 *  Contradiction rule
 *
 *   A |- F
 *   ------
 *   A |- t
 *
 *let CONTR tm th = MP (SPEC tm FALSITY) th ? failwith `CONTR`;
 *---------------------------------------------------------------------------*)
local val not_the_case = --`F`--
in
fun CONTR w fth =
   if (type_of w = bool)
   then if (concl fth = not_the_case)
        then let val th' = mk_drule_thm(hyp fth, w)
             in Thm.note (STEP{Name="CONTR",
                               Just=[JA_TERM w, JA_THM fth],Thm=th'},th')
             end
        else raise DRULE_ERR{function = "CONTR",message = ""}
   else raise DRULE_ERR{function = "CONTR",message = "term is not boolean"}
end;


(* ---------------------------------------------------------------------*)
(* EQF_INTRO: inference rule for introducing equality with "F".		*)
(*									*)
(* 	         ~tm							*)
(*	     -----------    EQF_INTRO					*)
(*	        tm = F							*)
(*									*)
(* [TFM 90.05.08]							*)
(* ---------------------------------------------------------------------*)

local
val F = --`F`--
and Fth = ASSUME (--`F`--)
in
fun EQF_INTRO th = 
   IMP_ANTISYM_RULE (NOT_ELIM th) 
                    (DISCH F (CONTR (dest_neg (concl th)) Fth))
   handle _ => raise DRULE_ERR{function = "EQF_INTRO",message = ""}
end;

(* ---------------------------------------------------------------------*)
(* EQF_ELIM: inference rule for eliminating equality with "F".		*)
(*									*)
(*	      |- tm = F							*)
(*	     -----------    EQF_ELIM					*)
(* 	       |- ~ tm							*)
(*									*)
(* [TFM 90.08.23]							*)
(* ---------------------------------------------------------------------*)
local val check = assert ((curry (op =) "F") o #Name o dest_const)
in
fun EQF_ELIM th =
   let val {lhs,rhs} = dest_eq(concl th)
       val _ = check rhs
   in
   NOT_INTRO(DISCH lhs (EQ_MP th (ASSUME lhs)))
   end
   handle _ => raise DRULE_ERR{function = "EQF_ELIM",message = ""}
end;

(*---------------------------------------------------------------------------
 *  |- !t. t \/ ~t 
 *---------------------------------------------------------------------------*)
val EXCLUDED_MIDDLE =
   let val t = --`t:bool`--
       val th1 = RIGHT_BETA(AP_THM boolThry.NOT_DEF t)
       val th2 = DISJ1 (EQT_ELIM(ASSUME (--`^t = T`--))) (--`~ ^t`--)
       and th3 = DISJ2 t (EQ_MP(SYM th1)(DISCH t(EQ_MP(ASSUME (--`^t = F`--))
                                                      (ASSUME t))))
   in
   GEN t (DISJ_CASES (SPEC t boolThry.BOOL_CASES_AX) th2 th3)
   end;

(*---------------------------------------------------------------------------
 * Classical contradiction rule
 *
 *   A,"~t" |- F
 *   --------------
 *       A |- t
 *
 *fun CCONTR t th =
 *   let val th1 = RIGHT_BETA(AP_THM boolThry.NOT_DEF t)
 *       and v   = genvar (--`:bool`--)
 *       val th2 = EQT_ELIM (ASSUME (--`^t = T`--))
 *       val th3 = SUBST [(th1,v)] (--`^v ==> F`--) (DISCH (--`~ ^t`--) th)
 *       val th4 = SUBST[(ASSUME(--`^t = F`--),v)] (--`(^v ==> F) ==> F`--) th3
 *       val th5 = MP th4 (EQT_ELIM (CONJUNCT2 IMP_CLAUSE4))
 *       val th6 = EQ_MP (SYM(ASSUME (--`^t = F`--))) th5
 *   in
 *   DISJ_CASES (SPEC t boolThry.BOOL_CASES_AX) th2 th6
 *   end
 *   handle _ => raise DRULE_ERR{function = "CCONTR",message = ""};
 *---------------------------------------------------------------------------*)
local val simply_not_the_case = --`F`--
in
fun CCONTR w fth = 
 if (concl fth = simply_not_the_case)
 then let val th' = mk_drule_thm(disch(mk_neg w, hyp fth), w)
      in Thm.note(STEP{Name="CCONTR",Just=[JA_TERM w, JA_THM fth],Thm=th'},th')
      end
 else raise DRULE_ERR{function = "CCONTR",message = ""}
end;


(*---------------------------------------------------------------------------
 * Instantiate variables in a theorem 
 *---------------------------------------------------------------------------*)
local exception LOCAL_ERR
in
fun INST [] th = th
  | INST (inst_list as (_::_)) th =
     let val (asl,w) = dest_thm th
         and vars = map (assert is_var o #redex) inst_list
     in 
   if Portable.List.exists (fn v => Portable.List.exists (free_in v) asl) vars
   then raise LOCAL_ERR
   else let val th' = mk_drule_thm(asl, subst inst_list w)
        in Thm.note (STEP{Name="INST",
                Just = JA_THM th :: 
                       map (fn {redex,residue} => 
                            JA_PAIR(JA_TERM redex, JA_TERM residue)) inst_list,
				   Thm=th'}, th')
        end
  end
  handle LOCAL_ERR => raise DRULE_ERR{function = "INST",
                          message = "attempt to substitute for a variable \
                                       \that is free in the assumptions"}
       | _ => raise DRULE_ERR{function = "INST",message = ""}
end;


(*---------------------------------------------------------------------------
 * |- !t. ~t ==> (t=F) 
 *---------------------------------------------------------------------------*)
val NOT_F =
   let val t = --`t:bool`--
       val th1 = MP (SPEC t F_IMP) (ASSUME (--`~ ^t`--))
       and th2 = SPEC t FALSITY
       and th3 = SPEC (--`F`--) (SPEC t boolThry.IMP_ANTISYM_AX)
   in
   GEN t (DISCH (--`~^t`--) (MP (MP th3 th1) th2))
   end;


(*---------------------------------------------------------------------------
 *  |- !t. ~(t /\ ~t)  
 *---------------------------------------------------------------------------*)
val NOT_AND =
   let val th = ASSUME (--`t /\ ~t`--)
   in NOT_INTRO(DISCH (--`t /\ ~t`--) (MP(CONJUNCT2 th) (CONJUNCT1 th)))
   end;

end; (* Drule2 *)


structure Drule3 : Drule3_sig =
struct
open Exception
open Lib
open Parse;
open CoreHol;
open Thm;
open Dsyntax;
open Term;
open Drule2;

infix 3 ##
infix 5 |->;

fun DRULE_ERR{function,message} = HOL_ERR{origin_structure = "Drule",
					 origin_function = function,
					 message = message}

(* ---------------------------------------------------------------------*)
(* ISPEC: specialization, with type instantation if necessary.		*)
(*									*)
(*     A |- !x:ty.tm							*)
(*  -----------------------   ISPEC "t:ty'" 				*)
(*      A |- tm[t/x]							*)
(*									*)
(* (where t is free for x in tm, and ty' is an instance of ty)		*)
(* ---------------------------------------------------------------------*)
fun ISPEC t th = 
   let val {Bvar,...} = dest_forall(concl th) handle _ => 
                        raise DRULE_ERR{function = "ISPEC",
                          message=": input theorem not universally quantified"}
       val(_,inst) = Match.match_term Bvar t handle _ => 
                     raise DRULE_ERR{function = "ISPEC",
                              message=": can't type-instantiate input theorem"}
   in SPEC t (INST_TYPE inst th)
      handle _ => raise DRULE_ERR{function = "ISPEC",
                               message = ": type variable free in assumptions"}
   end;
	 
(* ---------------------------------------------------------------------*)
(* ISPECL: iterated specialization, with type instantation if necessary.*)
(*									*)
(*        A |- !x1...xn.tm						*)
(*  ---------------------------------   ISPECL ["t1",...,"tn"]		*)
(*      A |- tm[t1/x1,...,tn/xn]					*)
(*									*)
(* (where ti is free for xi in tm)					*)
(* ---------------------------------------------------------------------*)
local
fun curried_mk_pair t1 t2 = mk_pair{fst = t1, snd = t2}
val tup = end_itlist curried_mk_pair
fun strip [] = (fn _ => [])
  | strip (ts as (h::t)) = 
        let val f = strip (tl ts) 
        in fn tm => let val{Bvar,Body} = dest_forall tm 
                    in (Bvar::f Body) 
                    end
        end
in
fun ISPECL [] = I
  | ISPECL [tm] = ISPEC tm
  | ISPECL ts = 
    let val stripfn = strip ts 
        and tst = tup ts 
    in fn th => 
       let val xs = stripfn (concl th) handle _ 
                    => raise DRULE_ERR{function = "ISPECL",
                              message = ": list of terms too long for theorem"}
           val (_,inst) = Match.match_term (tup xs) tst handle _
                          => raise DRULE_ERR{function = "ISPECL",
                            message = ": can't type-instantiate input theorem"}
       in SPECL ts (INST_TYPE inst th) handle _ 
          => raise DRULE_ERR{function = "ISPECL",
                             message = ": type variable free in assumptions"}
       end
    end
end;


(* ---------------------------------------------------------------------*)
(* SELECT_REFL = |- !x. (@y. y = x) = x                                 *)
(*                                                                      *)
(* changed ISPECL to nested ISPEC since ISPECL requires tupling in the  *)
(* logic, but at this stage we don't have the theory of pairs.  (KLS)   *)
(* ---------------------------------------------------------------------*)

val SELECT_REFL =
  let val th1 = ISPEC (--`x:'a`--) 
                      (ISPEC (--`\y:'a. y = x`--) boolThry.SELECT_AX)
      val ths = map BETA_CONV [--`(\y:'a. y = x) x`--, 
                               --`(\y:'a. y = x)(@y. y = x)`--]
      val th2 = SUBST[{var= --`u:bool`--, thm=el 1 ths},
                      {var= --`v:bool`--, thm=el 2 ths}]
                     (--`u ==> v`--) th1 
  in
  GEN (--`x:'a`--) (MP th2 (REFL (--`x:'a`--)))
  end;

(*---------------------------------------------------------------------------*)
(* SELECT_UNIQUE = |- !P x. (!y. P y = (y = x)) ==> ($@ P = x)               *)
(*---------------------------------------------------------------------------*)

val SELECT_UNIQUE =
  let fun mksym tm = DISCH tm (SYM(ASSUME tm))
      val th0 = IMP_ANTISYM_RULE (mksym (--`y:'a = x`--))
                                 (mksym (--`x:'a = y`--))
      val th1 = SPEC (--`y:'a`--) (ASSUME (--`!y:'a. P y = (y = x)`--))
      val th2 = EXT(GEN (--`y:'a`--) (TRANS th1 th0))
      val th3 = AP_TERM (--`$@ :('a->bool)->'a`--) th2
      val th4 = TRANS (BETA_CONV (--`(\y:'a. y = x) y`--)) th0
      val th5 = AP_TERM (--`$@ :('a->bool)->'a`--) (EXT(GEN (--`y:'a`--) th4))
      val th6 = TRANS (TRANS th3 (SYM th5)) (SPEC (--`x:'a`--) SELECT_REFL) 
  in
  GENL [(--`P:'a->bool`--), (--`x:'a`--)] 
       (DISCH (--`!y:'a. P y = (y = x)`--) th6)
  end;


(*---------------------------------------------------------------------------
 * Generalise a theorem over all variables free in conclusion but not in hyps
 *
 *         A |- t[x1,...,xn]
 *    ----------------------------
 *     A |- !x1...xn.t[x1,...,xn]
 *---------------------------------------------------------------------------*)
fun GEN_ALL th = itlist GEN (set_diff (free_vars(concl th)) 
                                      (free_varsl (hyp th))) th;


(*---------------------------------------------------------------------------
 *  Discharge all hypotheses 
 * 
 *       A, t1, ... , tn |- t
 *  -------------------------------
 *   A  |- t1 ==> ... ==> tn ==> t
 * 
 * You can write a simpler version using "itlist DISCH (hyp th) th", but this
 * may discharge two equivalent (alpha-convertible) assumptions.
 *---------------------------------------------------------------------------*)
fun DISCH_ALL th = DISCH_ALL (DISCH (hd (hyp th)) th) handle _ => th;


(*----------------------------------------------------------------------------
 *
 *    A |- t1 ==> ... ==> tn ==> t
 *  -------------------------------
 *       A, t1, ..., tn |- t
 *---------------------------------------------------------------------------*)
fun UNDISCH_ALL th =
   if (is_imp (concl th))
   then UNDISCH_ALL (UNDISCH th)
   else th;

(* ---------------------------------------------------------------------*)
(* SPEC_ALL : thm -> thm						*)
(*									*)
(*     A |- !x1 ... xn. t[xi]						*)
(*    ------------------------   where the xi' are distinct 		*)
(*        A |- t[xi'/xi]	 and not free in the input theorem	*)
(*									*)
(* BUGFIX: added the "distinct" part and code to make the xi's not free *)
(* in the conclusion !x1...xn.t[xi].		        [TFM 90.10.04]	*)
(*									*)
(* OLD CODE:								*)
(* 									*)
(* let SPEC_ALL th =							*)
(*     let vars,() = strip_forall(concl th) in				*)
(*     SPECL (map (variant (freesl (hyp th))) vars) th;;		*)
(* ---------------------------------------------------------------------*)

local fun f v (vs,l) = 
        let val v' = variant vs v 
        in (v'::vs, v'::l) end
in
fun SPEC_ALL th =
   let val (hvs,con) = (free_varsl ## I) (dest_thm th)
       val fvs = free_vars con 
       and vars = fst(strip_forall con) 
   in
   SPECL (snd(itlist f vars (hvs@fvs,[]))) th
   end
end;


(*---------------------------------------------------------------------------
 * Use the conclusion of the first theorem to delete a hypothesis of
 *   the second theorem.
 *
 *    A |- t1 	B, t1 |- t2
 *    -----------------------
 *         A u B |- t2
 *---------------------------------------------------------------------------*)
fun PROVE_HYP ath bth =  MP (DISCH (concl ath) bth) ath;


(*---------------------------------------------------------------------------
 * A |- t1/\t2  ---> A |- t1, A |- t2 
 *---------------------------------------------------------------------------*)
fun CONJ_PAIR th = (CONJUNCT1 th, CONJUNCT2 th) handle _ 
                   => raise DRULE_ERR{function = "CONJ_PAIR",message = ""};


(*---------------------------------------------------------------------------
 * ["A1|-t1"; ...; "An|-tn"]  ---> "A1u...uAn|-t1 /\ ... /\ tn", where n>0  
 *---------------------------------------------------------------------------*)
val LIST_CONJ = end_itlist CONJ ;


(*---------------------------------------------------------------------------
 * "A |- t1 /\ (...(... /\ tn)...)"   
 *   --->  
 *   [ "A|-t1"; ...; "A|-tn"],  where n>0 
 *
 *Inverse of LIST_CONJ : flattens only right conjuncts.
 *You must specify n, since tn could itself be a conjunction
 *---------------------------------------------------------------------------*)
fun CONJ_LIST 1 th = [th] |
    CONJ_LIST n th =  (CONJUNCT1 th) :: (CONJ_LIST (n-1) (CONJUNCT2 th))
                      handle _ => raise DRULE_ERR{function = "CONJ_LIST",
						  message = ""};


(*---------------------------------------------------------------------------
 * "A |- t1 /\ ... /\ tn"   --->  [ "A|-t1"; ...; "A|-tn"],  where n>0
 *
 *Flattens out all conjuncts, regardless of grouping
 *---------------------------------------------------------------------------*)
fun CONJUNCTS th = ((CONJUNCTS (CONJUNCT1 th))@(CONJUNCTS(CONJUNCT2 th)))
                   handle _ => [th];

(*---------------------------------------------------------------------------
 * "|- !x. (t1 /\ ...) /\ ... (!y. ... /\ tn)" 
 *   --->  [ "|-t1"; ...; "|-tn"],  where n>0 
 *
 *Flattens out conjuncts even in bodies of forall's
 *---------------------------------------------------------------------------*)
fun BODY_CONJUNCTS th =
   if (is_forall (concl th))
   then  BODY_CONJUNCTS (SPEC_ALL th)
   else if (is_conj (concl th))
        then ((BODY_CONJUNCTS (CONJUNCT1 th))@(BODY_CONJUNCTS (CONJUNCT2 th)))
        else [th];

(*---------------------------------------------------------------------------
 * Put a theorem 
 *
 *       |- !x. t1 ==> !y. t2 ==> ... ==> tm ==>  t 
 *
 * into canonical form by stripping out quantifiers and splitting
 * conjunctions apart.
 * 
 * 	t1 /\ t2	--->		t1,   t2
 *      (t1/\t2)==>t	--->		t1==> (t2==>t)
 *      (t1\/t2)==>t	--->		t1==>t, t2==>t
 *      (?x.t1)==>t2	--->		t1[x'/x] ==> t2
 *      !x.t1		--->		t1[x'/x]
 *      (?x.t1)==>t2    --->            t1[x'/x] ==> t2)
 *---------------------------------------------------------------------------*)
fun IMP_CANON th =
   let val w = concl th
   in
   if (is_conj w)
   then ((IMP_CANON (CONJUNCT1 th))@(IMP_CANON (CONJUNCT2 th)))
   else if (is_imp w)
        then let val {ant,...} = dest_imp w 
             in
             if (is_conj ant)
             then let val {conj1,conj2} = dest_conj ant
                  in
	          IMP_CANON (DISCH conj1
                               (DISCH conj2 (MP th (CONJ (ASSUME conj1) 
                                                         (ASSUME conj2)))))
                  end
	     else if (is_disj ant)
                  then let val {disj1,disj2} = dest_disj ant
                       in
                       ((IMP_CANON (DISCH disj1 
                                          (MP th (DISJ1 (ASSUME disj1)
                                                        disj2)))) @
                        (IMP_CANON (DISCH disj2
                                          (MP th (DISJ2 disj1
                                                        (ASSUME disj2))))))
                       end
	          else if (is_exists ant)
                       then let val {Bvar,Body} = dest_exists ant 
	                        val bv' = variant (thm_free_vars th) Bvar
                                val body' = subst [Bvar |-> bv'] Body
                            in
	                    IMP_CANON (DISCH body'(MP th(EXISTS(ant, bv')
                                                              (ASSUME body'))))
                            end
                        else map (DISCH ant) (IMP_CANON (UNDISCH th))
             end
        else if (is_forall w)
             then IMP_CANON (SPEC_ALL th)
             else [th]
   end;


(*---------------------------------------------------------------------------
 *  A1 |- t1   ...   An |- tn      A |- t1==>...==>tn==>t
 *   -----------------------------------------------------
 *            A u A1 u ... u An |- t
 *---------------------------------------------------------------------------*)
val LIST_MP  = rev_itlist (fn x => fn y => MP y x) ;


(*---------------------------------------------------------------------------
 *      A |-t1 ==> t2
 *    -----------------
 *    A |-  ~t2 ==> ~t1
 *
 * Rewritten by MJCG to return "~t2 ==> ~t1" rather than "~t2 ==> t1 ==>F".
 *---------------------------------------------------------------------------*)
local val imp_th = GEN_ALL(el 5 (CONJUNCTS(SPEC_ALL IMP_CLAUSES)))
in
fun CONTRAPOS impth =
   let val {ant,conseq} = dest_imp (concl impth) 
       val notb = mk_neg conseq
   in
   DISCH notb (EQ_MP (SPEC ant imp_th)
                     (DISCH ant (MP (ASSUME notb)
                                    (MP impth (ASSUME ant)))))
   end
   handle _ => raise DRULE_ERR{function = "CONTRAPOS",message = ""}
end;


(*---------------------------------------------------------------------------
 *      A |- t1 \/ t2
 *   --------------------
 *     A |-  ~ t1 ==> t2
 *
 *---------------------------------------------------------------------------*)
fun DISJ_IMP dth =
   let val {disj1,disj2} = dest_disj (concl dth)
       val nota = mk_neg disj1
   in
   DISCH nota
        (DISJ_CASES dth (CONTR disj2 (MP (ASSUME nota) (ASSUME disj1)))
                        (ASSUME disj2))
   end handle _ => raise DRULE_ERR{function = "DISJ_IMP",message = ""};


(*---------------------------------------------------------------------------
 *  A |- t1 ==> t2
 *  ---------------
 *   A |- ~t1 \/ t2
 *---------------------------------------------------------------------------*)
fun IMP_ELIM th =
   let val {ant,conseq} = dest_imp (concl th)
       val not_t1 = mk_neg ant
   in
   DISJ_CASES (SPEC ant EXCLUDED_MIDDLE)
              (DISJ2 not_t1 (MP th (ASSUME ant)))
              (DISJ1 (ASSUME not_t1) conseq)
   end
   handle _ => raise DRULE_ERR{function = "IMP_ELIM",message = ""};


(*----------------------------------------------------------------------------
 *    |- (~~t = t) /\ (~T = F) /\ (~F = T) 
 *---------------------------------------------------------------------------*)
val NOT_CLAUSES =
 CONJ
  (GEN (--`t:bool`--)
    (IMP_ANTISYM_RULE
      (DISJ_IMP(IMP_ELIM(DISCH (--`t:bool`--) (ASSUME (--`t:bool`--)))))
      (DISCH (--`t:bool`--)
       (NOT_INTRO(DISCH (--`~t`--) (UNDISCH (NOT_ELIM(ASSUME (--`~t`--)))))))))
  (CONJ (IMP_ANTISYM_RULE
          (DISCH (--`~T`--) 
                 (MP (MP (SPEC (--`T`--) F_IMP) (ASSUME (--`~T`--))) TRUTH))
          (SPEC (--`~T`--) FALSITY))
        (IMP_ANTISYM_RULE (DISCH (--`~F`--) TRUTH)
                          (DISCH (--`T`--) (MP (SPEC (--`F`--) IMP_F)
                                               (SPEC (--`F`--) FALSITY)))));


(*---------------------------------------------------------------------------
 *  A |- t1 \/ t2     A1, t1 |- t3      A2, t2 |- t4
 *   ------------------------------------------------
 *                A u A1 u A2 |- t3 \/ t4
 *---------------------------------------------------------------------------*)
fun DISJ_CASES_UNION dth ath bth =
    DISJ_CASES dth (DISJ1 ath (concl bth)) (DISJ2 (concl ath) bth);

end; (* Drule3 *)


structure Drule : Drule_sig =
struct
open Exception
open Lib
open Parse;
open CoreHol;
open Thm;
open Dsyntax;
open Term;
open Drule3;

infix 5 |->;

fun DRULE_ERR{function,message} = HOL_ERR{origin_structure = "Drule",
					  origin_function = function,
					  message = message}

(*---------------------------------------------------------------------------
 * Forward chain using an inference rule on top-level sub-parts of a theorem
 * Could be extended to handle other connectives
 * Commented out.
 *
 *fun SUB_CHAIN rule th =
 *   let val w = concl th 
 *   in
 *   if (is_conj w)
 *   then CONJ (rule(CONJUNCT1 th)) (rule(CONJUNCT2 th))
 *   else if (is_disj w)
 *        then let val (a,b) = dest_disj w 
 *             in	
 *             DISJ_CASES_UNION th (rule (ASSUME a)) (rule (ASSUME b))
 *             end
 *        else if (is_imp w)
 *             then let val (a,b) = dest_imp w 
 *                  in  
 *                  DISCH a (rule (UNDISCH th))
 *                  end
 *             else if (is_forall w)
 *                  then let val (x', sth) = SPEC_VAR th 
 *                       in
 *	               GEN x' (rule sth)
 *                       end
 *                  else th
 *   end;
 *
 *infix thenf orelsef;
 *fun f thenf g = fn x => g(f x);
 *fun f orelsef g = (fn x => (f x) handle _ => (g x));
 *
 *(* Repeatedly apply the rule (looping if it never fails) *)
 *fun REDEPTH_CHAIN rule x =
 *   (SUB_CHAIN (REDEPTH_CHAIN rule) thenf
 *    ((rule thenf (REDEPTH_CHAIN rule)) orelsef I))
 *   x;
 *
 *
 *(* Apply the rule no more than once in any one place *)
 *fun ONCE_DEPTH_CHAIN rule x =
 *   (rule  orelsef  SUB_CHAIN (ONCE_DEPTH_CHAIN rule))
 *   x;
 *
 *
 *(* "depth SPEC" : Specialize a theorem whose quantifiers are buried inside *)
 *fun DSPEC x = ONCE_DEPTH_CHAIN (SPEC x);
 *val DSPECL = rev_itlist DSPEC;
 *
 *val CLOSE_UP = GEN_ALL o DISCH_ALL;
 *---------------------------------------------------------------------------*)


(*---------------------------------------------------------------------------
 *   |- !x. x=x 
 *---------------------------------------------------------------------------*)
val EQ_REFL = GEN (--`x : 'a`--) (REFL (--`x : 'a`--));


(*---------------------------------------------------------------------------
 *   |- !x. (x=x) = T 
 *---------------------------------------------------------------------------*)
val REFL_CLAUSE = GEN (--`x: 'a`--) (EQT_INTRO(SPEC (--`x:'a`--) EQ_REFL));


(*---------------------------------------------------------------------------
 *   |- !x y. x=y  ==>  y=x  
 *---------------------------------------------------------------------------*)
val EQ_SYM =
 let val x = --`x:'a`--
     and y = --`y:'a`--
 in
 GEN x (GEN y (DISCH (--`^x = ^y`--) (SYM(ASSUME (--`^x = ^y`--)))))
 end;


(*---------------------------------------------------------------------------
 *    |- !x y. (x = y) = (y = x)
 *---------------------------------------------------------------------------*)
val EQ_SYM_EQ =
   GEN (--`x:'a`--)
    (GEN (--`y:'a`--) 
      (IMP_ANTISYM_RULE (SPEC (--`y:'a`--) (SPEC (--`x:'a`--) EQ_SYM))
                        (SPEC (--`x:'a`--) (SPEC (--`y:'a`--) EQ_SYM))));

(*---------------------------------------------------------------------------
 *    |- !f g. (!x. f x = g x)  ==>  f=g 
 *---------------------------------------------------------------------------*)
val EQ_EXT =
   let val f = (--`f:'a->'b`--)
       and g = (--`g: 'a -> 'b`--)
   in
   GEN f (GEN g (DISCH (--`!x:'a. ^f (x:'a) = ^g (x:'a)`--)
                       (EXT(ASSUME (--`!x:'a. ^f (x:'a) = ^g (x:'a)`--)))))
   end;


(*---------------------------------------------------------------------------
 *    |- !x y z. x=y  /\  y=z  ==>  x=z 
 *---------------------------------------------------------------------------*)
val EQ_TRANS =
   let val x = --`x:'a`--
       and y = --`y:'a`--
       and z = --`z:'a`--
       val xyyz  = (--`(^x = ^y) /\ (^y = ^z)`--)
   in
   GEN x
    (GEN y
     (GEN z
      (DISCH xyyz
       (TRANS (CONJUNCT1(ASSUME xyyz)) 
              (CONJUNCT2(ASSUME xyyz))))))
   end;


(*---------------------------------------------------------------------------
 *     |- ~(T=F) /\ ~(F=T) 
 *---------------------------------------------------------------------------*)
val BOOL_EQ_DISTINCT =
   let val TF = --`T = F`--
       and FT = --`F = T`--
   in
   CONJ
    (NOT_INTRO(DISCH TF (EQ_MP (ASSUME TF) TRUTH)))
    (NOT_INTRO(DISCH FT (EQ_MP (SYM(ASSUME FT)) TRUTH)))
   end;


(*---------------------------------------------------------------------------
 *     |- !t. (T = t) = t
 *---------------------------------------------------------------------------*)
val EQ_CLAUSE1 =
   let val t = --`t:bool`--
       val Tt = --`T = ^t`--
       val th1 = DISCH Tt (EQ_MP (ASSUME Tt) TRUTH)
       and th2 = DISCH t (SYM(EQT_INTRO(ASSUME t)))
   in
   GEN t (IMP_ANTISYM_RULE th1 th2)
   end;


(*---------------------------------------------------------------------------
 *  |- !t. (t = T) = t 
 *---------------------------------------------------------------------------*)
val EQ_CLAUSE2 =
   let val t = --`t:bool`--
       val tT = --`^t = T`--
       val th1 = DISCH tT (EQ_MP (SYM (ASSUME tT)) TRUTH)
       and th2 = DISCH t (EQT_INTRO(ASSUME t))
   in
   GEN t (IMP_ANTISYM_RULE th1 th2)
   end;

 
(*---------------------------------------------------------------------------
 *    |- !t. (F = t) = ~t 
 *---------------------------------------------------------------------------*)
val EQ_CLAUSE3 =
   let val t = --`t:bool`--
       val Ft = --`F = ^t`--
       val tF = --`^t = F`--
       val th1 = DISCH Ft (MP (SPEC t IMP_F)
                              (DISCH t (EQ_MP(SYM(ASSUME Ft))
                                             (ASSUME t))))
       and th2 = IMP_TRANS (SPEC t NOT_F)
                           (DISCH tF (SYM(ASSUME tF)))
   in
   GEN t (IMP_ANTISYM_RULE th1 th2)
   end;


(*---------------------------------------------------------------------------
 *  |- !t. (t = F) = ~t 
 *---------------------------------------------------------------------------*)
val EQ_CLAUSE4 =
   let val t = --`t:bool`--
       val tF = --`^t = F`--
       val th1 = DISCH tF (MP (SPEC t IMP_F)
                              (DISCH t (EQ_MP(ASSUME tF)
                                             (ASSUME t))))
       and th2 = SPEC t NOT_F
   in
   GEN t (IMP_ANTISYM_RULE th1 th2)
   end;
 

(*---------------------------------------------------------------------------
 *  |- !t.  (T = t)  =  t  /\
 *          (t = T)  =  t  /\
 *          (F = t)  =  ~t /\
 *          (t = F)  =  ~t
 *---------------------------------------------------------------------------*)
val EQ_CLAUSES =
   let val t = --`t:bool`--
   in
   GEN t (CONJ
           (SPEC t EQ_CLAUSE1)
            (CONJ
              (SPEC t EQ_CLAUSE2)
                (CONJ (SPEC t EQ_CLAUSE3)
                      (SPEC t EQ_CLAUSE4))))
   end;


(*---------------------------------------------------------------------------
 *     A1 |- f = g    A2 |- x = y		
 *     ---------------------------
 *       A1 u A2 |- f x = g y
 *
 *fun MK_COMB (funth,argth) = 
 *   let val f = lhs (concl funth)
 *       and x = lhs (concl argth)
 *   in
 *   SUBS_OCCS [([2], funth), ([2], argth)] (REFL (Comb(f,x))))
 *   ? failwith `MK_COMB`;
 *---------------------------------------------------------------------------*)
fun MK_COMB (funth,argth) =
   let val {lhs = f, rhs = g} = dest_eq (concl funth)
       and {lhs = x, rhs = y} = dest_eq (concl argth)
       val th' = mk_drule_thm(union (hyp funth) (hyp argth), 
                   mk_eq{lhs = mk_comb{Rator = f, Rand = x},
                         rhs = mk_comb{Rator = g, Rand = y}})
   in
     Thm.note (STEP{Name="MKCOMB",
                    Just=[JA_THM funth, JA_THM argth], Thm=th'},th')
   end
   handle _ => raise DRULE_ERR{function = "MK_COMB",message = ""};


(*---------------------------------------------------------------------------
 *       A |- !x. (t1 = t2)
 *     ----------------------
 *     A |- (\x.t1) = (\x.t2)
 *
 *fun MK_ABS qth =
 *   let val (x,body) = dest_forall (concl qth) 
 *       val ufun = mk_abs(x, lhs body)
 *       and vfun = mk_abs(x, rhs body)
 *       val gv = genvar (type_of x) 
 *   in
 *   EXT (GEN gv
 *	 (TRANS (TRANS (BETA_CONV (mk_comb(ufun,gv)))
 *                       (SPEC gv qth))
 *	        (SYM (BETA_CONV (mk_comb(vfun,gv))))))
 *   end
 *   handle _ => raise DRULE_ERR{function = "MK_ABS",message = ""};
 *---------------------------------------------------------------------------*)
fun MK_ABS th =
   let val {Bvar,Body} = dest_forall(concl th)
       val {lhs,rhs} = dest_eq Body
       val th' = mk_drule_thm(hyp th, 
                   mk_eq{lhs = mk_abs{Bvar = Bvar, Body = lhs},
                         rhs = mk_abs{Bvar = Bvar, Body = rhs}})
   in Thm.note (STEP{Name="MKABS", Just=[JA_THM th], Thm=th'},th')
   end
   handle _ => raise DRULE_ERR{function = "MK_ABS",message = ""};


(*---------------------------------------------------------------------------
 *     A |- !x. t1 x = t2
 *     ------------------
 *      A |-  t1 = \x.t2
 *
 *fun HALF_MK_ABS qth =
 *   let val {Bvar,Body} = dest_forall (concl qth) 
 *       val t = rhs Body
 *       and gv = genvar (type_of Bvar) 
 *       val tfun = mk_abs{Bvar = Bvar, Body = t}
 *   in
 *   EXT (GEN gv 		(* |- !gv. u gv =< (\x.t) gv  *)
 *	 (TRANS (SPEC gv qth)
 *                (SYM (BETA_CONV (mk_comb{Rator = tfun, Rand = gv})))))
 *   end
 *   handle _ => raise DRULE_ERR{function = "HALF_MK_ABS",message = ""};
 *---------------------------------------------------------------------------*)


(*---------------------------------------------------------------------------
 * Equivalence of alpha-convertable terms 
 *
 *     t1, t2 alpha-convertable
 *     -------------------------
 *            |- t1 = t2
 *
 *fun ALPHA t1 t2 =
 *  (if (t1=t2)
 *   then REFL t1
 *   else
 *   case (t1,t2)
 *     of (Comb(t11,t12),
 *         Comb(t21,t22))
 *          => let val th1 = ALPHA t11 t21
 *                 and th2 = ALPHA t12 t22
 *             in 
 *             TRANS (AP_THM th1 t12) (AP_TERM t21 th2)
 *             end 
 *        |
 *        (Abs(x1,_),
 *         Abs(x2,t2'))
 *         => let val th1 = ALPHA_CONV x2 t1
 *                val (_,t1') = dest_abs(rhs(concl th1))
 *                val th2 = ALPHA t1' t2'
 *            in 
 *            TRANS th1 (ABS x2 th2)
 *            end
 *        | (_,_)  => raise DRULE_ERR{function = "ALPHA",message = ""}
 *  ) handle _ => raise DRULE_ERR{function = "ALPHA",message = ""};
 *---------------------------------------------------------------------------*)
fun ALPHA t1 t2 =
   if (aconv t1 t2)
   then let val th' = mk_drule_thm([],mk_eq{lhs = t1, rhs = t2})
     in Thm.note(STEP{Name="ALPHA", Just=[JA_TERM t1, JA_TERM t2],Thm=th'},th')
     end
   else raise DRULE_ERR{function = "ALPHA",message = ""};


(*---------------------------------------------------------------------------
 * Rename the bound variable of a lambda-abstraction
 *
 *       "x"   "(\y.t)"   --->   |- "\y.t = \x. t[x/y]"  
 *
 *---------------------------------------------------------------------------*)

fun ALPHA_CONV x t =
   let val x' = variant (free_vars t) x
       val cmb = mk_comb{Rator = t, Rand = x'}
       val th1 = SYM(ETA_CONV(mk_abs{Bvar = x', Body = cmb}))
       and th2 = ABS x' (BETA_CONV cmb)
   in
   TRANS th1 th2
   end
   handle _ => raise DRULE_ERR{function = "ALPHA_CONV",message = ""};


(*----------------------------------------------------------------------------
 * Version of  ALPHA_CONV that renames "x" when necessary, but then it doesn't
 * meet the specification. Is that really a problem? Notice that this version 
 * of ALPHA_CONV is more efficient.
 *
 *fun ALPHA_CONV x t = 
 *  if (Term.free_in x t)
 *  then ALPHA_CONV (variant (free_vars t) x) t
 *  else ALPHA t (mk_abs{Bvar = x,
 *                       Body = Term.beta_conv(mk_comb{Rator = t,Rand = x})});
 *---------------------------------------------------------------------------*)

(*---------------------------------------------------------------------------
 * Rename bound variables
 *
 *       "x"   "(\y.t)"   --->    |- "\y.t  = \x. t[x/y]"  
 *       "x"   "(!y.t)"   --->    |- "!y.t  = !x. t[x/y]"  
 *       "x"   "(?y.t)"   --->    |- "?y.t  = ?x. t[x/y]"  
 *       "x"   "(?!y.t)"  --->    |- "?!y.t = ?!x. t[x/y]"  
 *       "x"   "(@y.t)"   --->    |- "@y.t  = @x. t[x/y]"  
 *---------------------------------------------------------------------------*)
local val check = assert (Theory.is_binder o #Name o dest_const)
in
fun GEN_ALPHA_CONV x t =
   if (is_abs t) 
   then ALPHA_CONV x t 
   else let val {Rator, Rand} = dest_comb t
            val _ = check Rator
        in
        AP_TERM Rator (ALPHA_CONV x Rand)
        end
        handle _ => raise DRULE_ERR{function = "GEN_ALPHA_CONV",message = ""}
end;


(*---------------------------------------------------------------------------
 *    |- !t1: 'a.!t2:'a. COND T t1 t2 = t1 
 *---------------------------------------------------------------------------*)
val COND_CLAUSE1 =
 let val (x,t1,t2,v) = (--`x:'a`--, 
                        --`t1:'a`--,
                        --`t2:'a`--, 
                        genvar(==`:bool`==))
     val th1 = RIGHT_BETA(AP_THM
                 (RIGHT_BETA(AP_THM
                    (RIGHT_BETA(AP_THM boolThry.COND_DEF (--`T`--))) t1))t2)
     val TT = EQT_INTRO(REFL (--`T`--))
     val th2 = SUBST [{var = v, thm = SYM TT}]
                     (--`(^v ==> (^x=^t1)) = (^x=^t1)`--) 
                     (el 1 (CONJUNCTS(SPEC (--`^x=^t1`--) IMP_CLAUSES)))
     and th3 = DISCH (--`T=F`--)
                     (MP (SPEC (--`^x=^t2`--) FALSITY)
                         (UNDISCH(MP (SPEC (--`T=F`--) F_IMP) 
                                     (CONJUNCT1 BOOL_EQ_DISTINCT))))
     val th4 = DISCH (--`^x=^t1`--)
                     (CONJ(EQ_MP(SYM th2)(ASSUME (--`^x=^t1`--)))th3)
     and th5 = DISCH (--`((T=T) ==> (^x=^t1))/\((T=F) ==> (^x=^t2))`--)
                     (MP (CONJUNCT1(ASSUME (--`((T=T) ==> (^x=^t1))/\
                                               ((T=F) ==> (^x=^t2))`--)))
                         (REFL (--`T`--)))
     val th6 = MP (MP (SPEC (--`((T=T) ==> (^x=^t1))/\((T=F) ==> (^x=^t2))`--) 
                            (SPEC (--`^x=^t1`--) boolThry.IMP_ANTISYM_AX))
                      th4)
                  th5
     val th7 = TRANS th1 (SYM(SELECT_EQ x th6))
     val th8 = EQ_MP (SYM(BETA_CONV (--`(\^x.^x = ^t1) ^t1`--))) (REFL t1)
     val th9 = MP (SPEC t1 (SPEC (--`\^x.^x = ^t1`--) boolThry.SELECT_AX)) th8
 in
 GEN t1 (GEN t2 (TRANS th7 (EQ_MP (BETA_CONV(concl th9)) th9)))
 end;


(*---------------------------------------------------------------------------
 *    |- !tm1:'a.!tm2:'a. COND F tm1 tm2 = tm2 
 *
 *   Note that there is a bound variable conflict if we use use t1
 *   and t2 as the variable names. That would be a good test of the 
 *   substitution algorithm.
 *---------------------------------------------------------------------------*)
val COND_CLAUSE2 =
   let val (x,t1,t2,v) = (--`x:'a`--,
                          --`tm1:'a`--,
                          --`tm2:'a`--, 
                          genvar (==`:bool`==))
       val th1 = RIGHT_BETA(AP_THM
                   (RIGHT_BETA(AP_THM
                     (RIGHT_BETA(AP_THM boolThry.COND_DEF (--`F`--))) t1))t2)
       val FF = EQT_INTRO(REFL (--`F`--))
       val th2 = SUBST [{var = v, thm = SYM FF}]
                       (--`(^v ==> (^x=^t2))=(^x=^t2)`--)
                       (el 1 (CONJUNCTS(SPEC (--`^x=^t2`--) IMP_CLAUSES)))
       and th3 = DISCH (--`F=T`--) (MP (SPEC (--`^x=^t1`--) FALSITY)
                                 (UNDISCH (MP (SPEC (--`F=T`--) F_IMP) 
                                              (CONJUNCT2 BOOL_EQ_DISTINCT))))
       val th4 = DISCH (--`^x=^t2`--)
                       (CONJ th3 (EQ_MP(SYM th2)(ASSUME (--`^x=^t2`--))))
       and th5 = DISCH (--`((F=T) ==> (^x=^t1)) /\ ((F=F) ==> (^x=^t2))`--)
                       (MP (CONJUNCT2(ASSUME (--`((F=T) ==> (^x=^t1)) /\
                                                 ((F=F) ==> (^x=^t2))`--)))
                           (REFL (--`F`--)))
       val th6 = MP (MP (SPEC (--`((F=T) ==> (^x=^t1)) /\
                                  ((F=F) ==> (^x=^t2))`--)
                              (SPEC (--`^x=^t2`--) boolThry.IMP_ANTISYM_AX))
                        th4)
                    th5
       val th7 = TRANS th1 (SYM(SELECT_EQ x th6))
       val th8 = EQ_MP (SYM(BETA_CONV (--`(\^x.^x = ^t2) ^t2`--)))
                       (REFL t2)
       val th9 = MP (SPEC t2 (SPEC (--`\^x.^x = ^t2`--) boolThry.SELECT_AX)) th8
   in
   GEN t1 (GEN t2 (TRANS th7 (EQ_MP (BETA_CONV(concl th9)) th9)))
   end;



(*---------------------------------------------------------------------------
 *    |- !t1:'a.!t2:'a. ((T => t1 | t2) = t1) /\ ((T => t1 | t2) = t2) 
 *---------------------------------------------------------------------------*)
val COND_CLAUSES =
   let val (t1,t2) = (--`t1:'a`--, --`t2:'a`--)
   in
   GEN t1 (GEN t2 (CONJ(SPEC t2(SPEC t1 COND_CLAUSE1))
                       (SPEC t2(SPEC t1 COND_CLAUSE2))))
   end;


(*--------------------------------------------------------------------- *)
(* COND_ID: 								*)
(*									*)
(* |- b. !t:*. (b => t | t) = t						*)
(*									*)
(*					                   TFM 90.07.23 *)
(*--------------------------------------------------------------------- *)

val COND_ID =
   let val b = --`b:bool`--
       and t = --`t:'a`--
       val def = INST_TYPE [==`:'b`==  |->  ==`:'a`==] boolThry.COND_DEF
       val th1 = itlist (fn x => RIGHT_BETA o (C AP_THM x)) 
                        [t,t,b] def
       val p = genvar (==`:bool`==)
       val asm1 = ASSUME (--`((^b=T)==>^p) /\ ((^b=F)==>^p)`--)
       val th2 = DISJ_CASES (SPEC b boolThry.BOOL_CASES_AX)
                            (UNDISCH (CONJUNCT1 asm1))
                            (UNDISCH (CONJUNCT2 asm1))
       val imp1 = DISCH (concl asm1) th2 
       val asm2 = ASSUME p
       val imp2 = DISCH p (CONJ (DISCH (--`^b=T`--)
                                       (ADD_ASSUM (--`^b=T`--) asm2))
	                        (DISCH (--`^b=F`--)
                                       (ADD_ASSUM (--`^b=F`--) asm2)))
       val lemma = SPEC (--`x:'a = ^t`--)
                        (GEN p (IMP_ANTISYM_RULE imp1 imp2))
       val th3 = TRANS th1 (SELECT_EQ (--`x:'a`--) lemma)
       val th4 = EQ_MP (SYM(BETA_CONV (--`(\x.x = ^t) ^t`--)))
                       (REFL t)
       val th5 = MP (SPEC t (SPEC (--`\x.x = ^t` --) boolThry.SELECT_AX)) th4
       val lemma2 = EQ_MP (BETA_CONV(concl th5)) th5 
   in
   GEN b (GEN t (TRANS th3 lemma2))
   end;

(* ---------------------------------------------------------------------*)
(* IMP_CONJ implements the following derived inference rule:		*)
(*									*)
(*  A1 |- P ==> Q    A2 |- R ==> S					*)
(* --------------------------------- IMP_CONJ				*)
(*   A1 u A2 |- P /\ R ==> Q /\ S					*)
(* ---------------------------------------------------------------------*)

fun IMP_CONJ th1 th2 = 
    let val {ant = A1, ...} = dest_imp (concl th1) 
        and {ant = A2, ...} = dest_imp (concl th2)
        val conj = mk_conj{conj1 = A1, conj2 = A2}
        val (a1,a2) = CONJ_PAIR (ASSUME conj)
    in
    DISCH conj (CONJ (MP th1 a1) (MP th2 a2))
    end;

(* ---------------------------------------------------------------------*)
(* EXISTS_IMP : existentially quantify the antecedent and conclusion 	*)
(* of an implication.							*)
(*									*)
(*        A |- P ==> Q							*)
(* -------------------------- EXISTS_IMP `x`				*)
(*   A |- (?x.P) ==> (?x.Q)						*)
(*									*)
(* ---------------------------------------------------------------------*)

fun EXISTS_IMP x th =
    if (not (is_var x))
    then raise DRULE_ERR{function = "EXISTS_IMP",
			 message = "first argument not a variable"}
    else let val {ant,conseq} = dest_imp(concl th)
             val th1 = EXISTS (mk_exists{Bvar = x, Body = conseq},x)
                              (UNDISCH th) 
             val asm = mk_exists{Bvar = x, Body = ant}
         in
         DISCH asm (CHOOSE (x,ASSUME asm) th1)
         end
         handle _ => raise DRULE_ERR{function = "EXISTS_IMP",
                                     message = "variable free in assumptions"};


(*---------------------------------------------------------------------------
 *   For rewriting 
 *---------------------------------------------------------------------------*)

(*---------------------------------------------------------------------------
 *   |- !t. (!x.t)  =  t 
 *---------------------------------------------------------------------------*)
val FORALL_SIMP =
 let val t = --`t:bool`--
     val x = --`x:'a`--
 in
 GEN t (IMP_ANTISYM_RULE
        (DISCH (--`!^x.^t`--) (SPEC x (ASSUME (--`!^x.^t`--))))
        (DISCH t (GEN x (ASSUME t))))
 end;

(*---------------------------------------------------------------------------
 *   |- !t. (?x.t)  =  t  
 *---------------------------------------------------------------------------*)
val EXISTS_SIMP =
   let val t = --`t:bool`--
       and x = --`x:'a`--
       val ext = --`?^x.^t`--
   in
   GEN t (IMP_ANTISYM_RULE (DISCH ext 
                                  (CHOOSE((--`p:'a`--), ASSUME ext)
                                         (ASSUME t)))
                           (DISCH t (EXISTS(ext, --`r:'a`--)
                                    (ASSUME t))))
   end;

(*---------------------------------------------------------------------------
 *    |- !t1 t2. (\x. t1)t2  =  t1 
 *---------------------------------------------------------------------------*)
val ABS_SIMP = GEN_ALL(BETA_CONV (--`(\x:'a.t1:'b)t2`--));


end; (* Drule *)
