structure Rules : Rules_sig = 
struct

type Type = USyntax.Type
type Preterm  = USyntax.Preterm
type Term = USyntax.Term
type Thm = CoreHol.Thm.thm
type Tactic = Abbrev.tactic;

structure USyntax  = USyntax;
structure Utils = USyntax.Utils;
structure Thm = CoreHol.Thm;

open Utils;
open Mask;
open CoreHol;
open Term Thm Dsyntax Drule Conv Let_conv Taut_thms;
infix 3 |->


fun RULES_ERR{func,mesg} = Utils.ERR{module = "Rules",func=func,mesg=mesg};

val dest_thm = Thm.dest_thm

  (* Inference rules *)
val REFL = Thm.REFL
val ASSUME = Thm.ASSUME
val MP = Thm.MP
val MATCH_MP = Conv.MATCH_MP
val CONJUNCT1 = Drule.CONJUNCT1
val CONJUNCT2 = Drule.CONJUNCT2
val CONJUNCTS = Drule.CONJUNCTS
val DISCH = Thm.DISCH
val UNDISCH = Drule.UNDISCH
val INST_TYPE = Thm.INST_TYPE o map (fn (A |-> B) => {redex=A, residue=B})
val SPEC = Drule.SPEC
val ISPEC = Drule.ISPEC
val ISPECL = Drule.ISPECL
val GEN = Drule.GEN
val GENL = Drule.GENL
val LIST_CONJ = Drule.LIST_CONJ
val BETA_RULE = Conv.BETA_RULE;


val DISCH_ALL = Drule.DISCH_ALL
val IMP_TRANS = Drule.IMP_TRANS
val SPEC_ALL  = Drule.SPEC_ALL
val GEN_ALL   = Drule.GEN_ALL
val CHOOSE    = Drule.CHOOSE
val EXISTS    = Drule.EXISTS
val SUBS      = Drule.SUBS
val SYM       = Drule.SYM
val PROVE_HYP = Drule.PROVE_HYP


(*---------------------------------------------------------------------------
 * It's intentional that we store the termination conditions on the
 * reference list, even if we fail in capturing the TC. The reason for
 * this is that we don't want to put nested TCs on the assumptions. 
 * Therefore, we capture them onto the ref. list and attempt to handle
 * them specially. 
 *---------------------------------------------------------------------------*)
local fun !!v M = Dsyntax.mk_forall{Bvar=v, Body=M}
      val mem = Utils.mem aconv
      fun set_diff a b = filter (fn x => not (mem x b)) a
in
fun solver (f,R) tc_list simps context tm =
  let fun genl tm = itlist !! (set_diff (rev(free_vars tm)) [f,R]) tm
      val nested = can(find_term (aconv f))
      val rcontext = rev context
      val antl = case rcontext of [] => [] 
                               | _   => [list_mk_conj(map concl rcontext)]
      val TC = genl(list_mk_imp(antl, tm))
      val _ = tc_list := (TC :: !tc_list)
  in if (nested TC)
     then raise RULES_ERR{func="solver", mesg="nested function"}
     else case rcontext
          of [] => SPEC_ALL(ASSUME TC)
          |  _  => MP (SPEC_ALL (ASSUME TC)) (LIST_CONJ rcontext)
  end
end;



fun CONTEXT_REWRITE_RULE(f,R){thms,congs,th} = 
let val tc_list = ref[]: term list ref
    open RW 
    val th1 = REWRITE_RULE Fully (Pure thms,Context([],DONT_ADD), Congs congs,
                                  Solver(solver (f,R) tc_list)) th
    val restricted = can(find_term
                          (Utils.holds(fn c => (#Name(dest_const c)="%"))))
in (th1, filter (not o restricted) (!tc_list))
end;


fun simpl_conv thl = 
  let open RW
      val RWC = Rewrite Fully (Simpls(Implicit.implicit_simpls(),thl),
                              Context([],DONT_ADD),Congs[],Solver always_fails)
      fun simpl tm =
       let val th = Conv.THENC(RWC, Conv.DEPTH_CONV GEN_BETA_CONV) tm
           val {lhs,rhs} = dest_eq(concl th)
       in if (aconv lhs rhs) then th else TRANS th (simpl rhs)
       end
  in simpl
  end;


fun simplify thl = 
  let val rewrite = RW.PURE_RW_RULE thl
      fun simpl th =
       let val th' = CONV_RULE (DEPTH_CONV GEN_BETA_CONV) (rewrite th)
           val (_,c1) = dest_thm th
           val (_,c2) = dest_thm th'
       in if (aconv c1 c2) then th else simpl th'
       end
  in simpl
  end;

val RIGHT_ASSOC = RW.PURE_RW_RULE[GSYM DISJ_ASSOC];


fun FILTER_DISCH_ALL P th =
   let val (asl,_) = dest_thm th
   in itlist DISCH (filter (Utils.holds P) asl) th
   end;

(*----------------------------------------------------------------------------
 *
 *         A |- M
 *   -------------------   [v_1,...,v_n]
 *    A |- ?v1...v_n. M
 *
 *---------------------------------------------------------------------------*)
fun EXISTL vlist thm =
   itlist (fn v => fn thm => EXISTS(mk_exists{Bvar=v,Body=concl thm},v) thm)
          vlist thm;

(*----------------------------------------------------------------------------
 *
 *       A |- M[x_1,...,x_n]
 *   ----------------------------   [(x |-> y)_1,...,(x |-> y)_n]
 *       A |- ?y_1...y_n. M
 *
 *---------------------------------------------------------------------------*)
fun IT_EXISTS theta thm =
 itlist (fn (b as (redex |-> residue)) => fn thm => 
    EXISTS(mk_exists{Bvar = residue,
                     Body = subst[{redex=redex, residue=residue}] (concl thm)},
            redex) thm)
    theta thm;



(*----------------------------------------------------------------------------
 *
 *                   A1 |- M1, ..., An |- Mn
 *     ---------------------------------------------------
 *     [A1 |- M1 \/ ... \/ Mn, ..., An |- M1 \/ ... \/ Mn]
 *
 *---------------------------------------------------------------------------*)

fun EVEN_ORS thms =
  let fun blue ldisjs [] _ = []
        | blue ldisjs (th::rst) rdisjs =
            let val rdisj_tl = list_mk_disj(tl rdisjs)
            in itlist DISJ2 ldisjs (DISJ1 th rdisj_tl)
               :: blue (ldisjs@[concl th]) rst (tl rdisjs)
            end handle _ 
            => [itlist DISJ2 ldisjs th]
   in
   blue [] thms (map concl thms)
   end;


(*---------------------------------------------------------------------------
 *
 *       |- A1 \/ ... \/ An     [A1 |- M, ..., An |- M]
 *     ---------------------------------------------------
 *                           |- M
 *
 *
 * The order of the theorems in the list doesn't matter: an operation akin
 * to sorting lines them up with the disjuncts in the theorem.
 *---------------------------------------------------------------------------*)

fun organize eq =    (* a bit slow - analogous to insertion sort *)
 let fun extract a alist =
     let fun ex (_,[]) = raise RULES_ERR{func = "organize",
                                         mesg = "not a permutation.1"}
           | ex(left,h::t) = if (eq h a) then (h,rev left@t) else ex(h::left,t)
     in ex ([],alist)
     end
     fun place [] [] = []
       | place (a::rst) alist =
           let val (item,next) = extract a alist
           in item::place rst next
           end
       | place _ _ = raise RULES_ERR{func = "organize",
                                     mesg = "not a permutation.2"}
 in place
 end;

fun DISJ_CASESL disjth thl =
 let val (_,c) = dest_thm disjth
     fun eq th atm = exists (aconv atm) (#1(dest_thm th))
     val tml = strip_disj c
     fun DL th [] = raise RULES_ERR{func="DISJ_CASESL",mesg="no cases"}
       | DL th [th1] = PROVE_HYP th th1
       | DL th [th1,th2] = DISJ_CASES th th1 th2
       | DL th (th1::rst) = DISJ_CASES th th1 
                               (DL(ASSUME(#disj2(dest_disj(concl th)))) rst)
 in DL disjth (organize eq tml thl)
 end;

val prove = Tactical.prove;

end; (* Rules *)
