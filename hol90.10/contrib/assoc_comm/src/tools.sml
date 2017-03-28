signature Ac_tools_sig =
sig
  structure Acu : Acu_sig
  type ac_eqns (* {A:thm, C:thm} list *)
  val AC_CANCEL_TAC : ac_eqns -> tactic
  val AC_REFL : ac_eqns -> term -> thm
  val var_extension :term list -> thm -> thm
  val AC_REWR_CONV : ac_eqns -> thm -> conv
  val AC_MP : ac_eqns -> thm -> thm -> thm
  val AC_MATCH_MP : ac_eqns -> thm -> thm -> thm
(*
  val AC_MP_TAC : ac_eqns -> thm_tactic
  val AC_ACCEPT_TAC : ac_eqns -> thm_tactic
  val AC_MATCH_ACCEPT_TAC : ac_eqns -> thm_tactic
  val AC_MATCH_MP_TAC : ac_eqns -> thm_tactic
*)
end;

functor AC_TOOLS(structure Acu :Acu_sig) : Ac_tools_sig =
struct

open Rsyntax;
structure Acu = Acu;
structure Ac_term = Acu.Ac_term;

fun AC_TOOLS_ERR{func,mesg} = 
         HOL_ERR{origin_structure = "Ac_tools",
                 origin_function = func,
                 message = mesg};

(* finds "op" in `!<vlist>. op <arglist> = rhs` *)

val extract_constant = 
  fst o strip_comb o #lhs o dest_eq o snd o strip_forall o concl;

type ac_eqns = {A:thm, C:thm} list

(* Puts ac_eqns into standard form, extracts the head operator, and checks
 * that the head operator is the same for the A and C theorems.
 ***)
fun process_ac_eqns ACthms =
   itlist (fn {A,C} => fn (athms,cthms,ac_ops) =>
             let val Athm = Ac_term.std_assoc_form A
                 val Cthm = Ac_term.std_comm_form C
                 val ah = extract_constant Athm
                 val ch = extract_constant Cthm
             in 
             if (ah = ch)
             then (Athm::athms, Cthm::cthms, ah::ac_ops)
             else raise AC_TOOLS_ERR{func = "process_ac_eqns",
                               mesg = "A and C thms do not agree on operator"}
             end)
          ACthms ([],[],[]);

fun MK_COMB_TAC (asl,tm) =
   if (is_eq tm)
   then let val {lhs,rhs} = dest_eq tm
        in if (is_comb lhs andalso is_comb rhs)
           then let val {Rator = ratorl,Rand = randl} = dest_comb lhs
                    val {Rator = ratorr,Rand = randr} = dest_comb rhs
                in ([(asl,mk_eq{lhs = ratorl, rhs = ratorr}),
                     (asl,mk_eq{lhs = randl, rhs = randr})],
                    fn [th1,th2] => Drule.MK_COMB(th1,th2))
                end
            else raise AC_TOOLS_ERR{func = "MK_COMB_TAC", mesg = ""}
        end
   else raise AC_TOOLS_ERR{func = "MK_COMB_TAC", mesg = "not an eq"};

        
fun AC_CANCEL_TAC (AC_thms:ac_eqns) : tactic =
let val (Athms,Cthms,ac_consts) = process_ac_eqns AC_thms
    val ASSOC_CONV = REWRITE_CONV Athms
    val COMM_CONV = ONCE_REWRITE_CONV Cthms
    val ROT1_CONV = COMM_CONV THENC ASSOC_CONV
    val ROT1_LHS_TAC = CONV_TAC (RATOR_CONV (RAND_CONV ROT1_CONV))
    val mk_ac = Ac_term.mk_ac ac_consts
    val is_ac = Lib.C mem ac_consts
    val intersect = Ac_lib.op_intersect Ac_term.ac_term_eq

    fun opr tm = 
       if (is_var tm orelse is_const tm)
       then tm
       else if (is_comb tm)
            then rator(rator tm)
            else raise AC_TOOLS_ERR{func = "AC_CANCEL_TAC.opr", 
                                    mesg = "Bad term structure"}
    fun Ac_opr (Ac_term.Ac_app(c,_)) = c
      | Ac_opr (Ac_term.Ac_const c) = c
      | Ac_opr (Ac_term.Ac_var v) = v
    (* 
     *     L = R  (|- L = tm_ac op L')  (|- R = tm_ac op R')
     *   ---------------------------------------------------
     *    |- (L = R) = (tm_ac op L' = tm_ac op R')
     ***)
    fun BRING_CONV tm_ac M =
       let val {lhs=Mlhs,rhs=Mrhs} = dest_eq M
           val eq_tm_ac = Ac_term.ac_term_eq tm_ac
           fun bring Mthm =
              let val {lhs,rhs} = dest_eq(concl Mthm)
                  val rhs_larm = rand(rator rhs)
              in if (eq_tm_ac (mk_ac rhs_larm))
                 then (rhs_larm,Mthm)
                 else bring (TRANS Mthm (ROT1_CONV rhs))
              end
           val (tm_ac1,lhs_thm) = bring (REFL Mlhs)
           val (tm_ac2,rhs_thm) = bring (REFL Mrhs)
           val tm_ac_equiv = prove(mk_eq{lhs=tm_ac1, rhs=tm_ac2},CANCEL)
           val v = genvar(type_of Mrhs)
           val (oprator,[_,oprand]) = strip_comb(Dsyntax.rhs(concl lhs_thm))
           val lhs_thm' = SUBST [{var = v, thm = tm_ac_equiv}]
                                (mk_eq{lhs = Mlhs, 
                                       rhs = list_mk_comb(oprator,[v,oprand])})
                                lhs_thm
           val u = genvar(type_of Mlhs)
       in 
       SUBST [{var=u,thm=lhs_thm'},{var=v,thm=rhs_thm}] 
             (mk_eq{lhs = M, rhs = mk_eq{lhs = u, rhs = v}})
             (REFL M)
       end
    and FINITO ac_tm (g as (asl,tm)) =
         let val {lhs,rhs} = dest_eq tm
             val ac_opr = Ac_opr ac_tm
             val lhs_opr = opr lhs
             val rhs_opr = opr rhs
         in if (ac_opr = lhs_opr)   (* lhs "atomic" *)
            then if (ac_opr = rhs_opr) (* rhs "atomic" *)
                 then CANCEL g      (* recurse *)
                 else ALL_TAC g    (* mismatch, stop *)
            else if (ac_opr = rhs_opr) 
                 then ALL_TAC g   (* mismatch, stop *)
                 else NO_TAC  g   (* neither side is atomic, do a BRING_CONV *)
         end
    and F [] tac = tac
      | F [tm_ac] tac = 
           tac 
           THEN (FINITO tm_ac 
                 ORELSE (CONV_TAC (BRING_CONV tm_ac)
                         THEN (REFL_TAC ORELSE AP_TERM_TAC)))
      | F (tm_ac::rst) tac =
          F rst (tac THEN (CONV_TAC (BRING_CONV tm_ac))
                     THEN (REFL_TAC ORELSE AP_TERM_TAC))
    and CANCEL (g as (asl,tm)) =
         if not(is_eq tm) 
         then ALL_TAC g
         else let val{lhs,rhs} = dest_eq tm
              in case (mk_ac lhs, mk_ac rhs)
                   of (Ac_term.Ac_app(c,lhs'), Ac_term.Ac_app(d,rhs'))
                        => if (c<>d)
                           then ALL_TAC g
                           else if (is_ac c)
                                then F (intersect lhs' rhs')
                                       (CONV_TAC ASSOC_CONV)
                                       g
                                else (MK_COMB_TAC THENL[CANCEL,CANCEL]) g
                    | _ => (REFL_TAC ORELSE ALL_TAC) g
              end
  in CANCEL
  end;

fun AC_REFL AC_thms tm = prove(tm, AC_CANCEL_TAC AC_thms);

(***********************************************************************
 Tests for CANCEL
 ***********************************************************************
local 
val thm = theorem "arithmetic"
in
val CANCEL = AC_CANCEL_TAC [{A=thm"ADD_ASSOC", C=thm"ADD_SYM"},
                            {A=thm"MULT_ASSOC",C=thm"MULT_SYM"}]
end;
   

Goalstack.g `1 + (3*(2+1))*4 + 2 = 1 + 2 + (1+2)*3`;
Goalstack.g `1 + 3*4*5 = ((5*3)*4 + 1)`;
Goalstack.g `SUC(1+2) = SUC(2+1)`;
Goalstack.g `1 + SUC(3*4*5) + 2*(7+x+y) = SUC((5*3)*4) +(1+2*(x+7+y))`;
Goalstack.g `((n + p'' + 1) + p' + p''' + 1 = p' + n)
              =
              ((n + p') + p'' + p''' + 1 + 1 = n + p')`;

*)


(* Place holder addition to an AC-rewrite theorem. If you want to rewrite
 *
 *     `0 + 3 + 0`
 *
 * with  |- x + x = 2*x, to get the match, you need to add a "place-holder"
 * variable to the rewrite rule.
 ***)
fun var_extension ac_ops thm =
   let val thm' = SPEC_ALL thm
       val ac_op = extract_constant thm
       val _ = assert (Lib.C mem ac_ops) ac_op
       val ty = Ac_term.binary_op_type ac_op
       val v = genvar ty
   in GEN_ALL(AP_TERM (mk_comb{Rator = ac_op, Rand = v}) thm')
   end;

fun AC_REWR_CONV (ACthms:ac_eqns) =
   let val ac_equiv = AC_REFL ACthms
       val (_,_,ac_consts) = process_ac_eqns ACthms
       val ac_matcher = Acu.hol_ac_match ac_consts
   in
   fn th =>
     let val pth = GSPEC (GEN_ALL th)
         val pat = Dsyntax.lhs(concl pth)
         val matchfn = hd o ac_matcher pat
     in
     fn tm => 
       let val theta = matchfn tm
                       handle _ => raise AC_TOOLS_ERR{func = "AC_REWR_CONV",
                                                      mesg="can't find match"}
           val eqn = INST_TY_TERM (theta,[]) pth
           val equiv_thm = ac_equiv(mk_eq{lhs=tm, rhs=Dsyntax.lhs(concl eqn)})
                           handle _ => raise AC_TOOLS_ERR{func="AC_REWR_CONV",
                           mesg="can't prove instantiated terms AC equivalent"}
       in TRANS equiv_thm eqn
       end 
     end
   end;


fun AC_MP ACthms =
   let val ac_equiv = AC_REFL ACthms
   in
   fn impth =>
   let val (hy,c) = dest_thm impth
       val {ant,conseq} = dest_imp c
             handle _ => raise AC_TOOLS_ERR{func = "AC_MP",
                                            mesg = "not an implication"}
       val v = genvar(==`:bool`==)
       val template = mk_imp{ant = v, conseq = conseq}
   in
   fn th => MP (SUBST[{var=v,thm=ac_equiv(mk_eq{lhs=ant,rhs=concl th})}] 
                     template impth)
               th
            handle _ => raise AC_TOOLS_ERR{func = "AC_MP",
                          mesg = "antecedent is not AC equivalent to argument"}
   end end;


(* Example
 * val th1 = mk_thm([],--`!x y z. x < y /\ y < z ==> x < z`--);
 * val th' = mk_thm([],--`(2+3+1)<(3+4+5) /\ 1 < ((2+1)+3)`--);
 * AC_MATCH_MP[{A=CONJ_ASSOC,C=CONJ_SYM},
 *             {A=theorem"arithmetic" "ADD_ASSOC",
 *              C=theorem"arithmetic" "ADD_SYM"}]
 *       th1 th';
 *
 * val it = |- 1 < 5 + 4 + 3 : thm
 *
 *****************************************************************)

fun AC_MATCH_MP ACthms =
   let val ac_equiv = AC_REFL ACthms
       val (_,_,ac_consts) = process_ac_eqns ACthms
       val ac_matcher = Acu.hol_ac_match ac_consts
   in
   fn impth =>
   let val (hy,c) = dest_thm impth
       val (vs,imp) = strip_forall c
       val pat = #ant(dest_imp imp)
                 handle _ => raise AC_TOOLS_ERR{func = "AC_MATCH_MP",
                                                mesg = "not an implication"}
       val fvs = set_diff (free_vars pat) (free_varsl hy)
       val gth = GSPEC (GENL fvs (SPECL vs impth))
       val pat' = #ant(dest_imp(concl gth))
       val matchfn = hd o ac_matcher pat'
   in
   fn th => 
     let val tm = concl th
         val theta = matchfn tm
         val impl = INST_TY_TERM(theta,[]) gth
         val {ant,conseq} = dest_imp (concl impl)
         val equiv_thm = ac_equiv(mk_eq{lhs=ant,rhs=tm})
         val v = genvar(==`:bool`==)
         val template = mk_imp{ant = v, conseq = conseq}
     in 
     MP (SUBST[{var=v,thm=equiv_thm}] template impl) th
     end
     handle _ => raise AC_TOOLS_ERR{func = "AC_MATCH_MP",
                                    mesg = "does not AC match"}
   end end;

(*  UNDER CONSTRUCTION ...
(* Solves a goal that is AC equivalent to a theorem
 *
 * 	   A
 *     ========= ACCEPT_TAC "|- A'"
 * 	   -
 ********)
fun AC_ACCEPT_TAC ACthms = 
   let val ac_equiv = AC_REFL ACthms
   in 
   fn th => fn (_,w) =>
    ([], fn [] => ac_equiv(mk_eq{lhs = w, rhs = Thm.concl th}))
   else raise AC_TOOLS_ERR{func = "AC_ACCEPT_TAC",mesg = ""};


(* ---------------------------------------------------------------------*)
(* Finish off a goal that is AC-equivalent to an instantiated theorem   *)
(* ---------------------------------------------------------------------*)
fun AC_MATCH_ACCEPT_TAC ac_eqns thm : tactic =
    let val fmatch = Conv.PART_MATCH I thm 
        fun atac (asl,w) = ([], K (fmatch w))
    in
    REPEAT GEN_TAC THEN atac
    end
    handle _ => raise AC_TOOLS_ERR{func = "AC_MATCH_ACCEPT_TAC",mesg = ""};



local
fun efn v (tm,th) =
   let val ntm = Dsyntax.mk_exists{Bvar = v,Body = tm} 
   in 
   (ntm,Drule.CHOOSE (v, Thm.ASSUME ntm) th)
   end
in
fun AC_MATCH_MP_TAC ac_eqns thm :tactic =
   let val (gvs,imp) = Dsyntax.strip_forall (Thm.concl thm) 
       val {ant,conseq} = Dsyntax.dest_imp imp 
                       handle _ => raise RESOLVE_ERR{func = "MATCH_MP_TAC",
                                                 mesg ="Not an implication"}
       val (cvs,con) = Dsyntax.strip_forall conseq
       val th1 = Drule.SPECL cvs (Drule.UNDISCH (Drule.SPECL gvs thm))
       val (vs,evs) = partition (C Term.free_in con) gvs 
       val th2 = uncurry Thm.DISCH (itlist efn evs (ant,th1))
   in
   fn (A,g) => let val (vs,gl) = Dsyntax.strip_forall g
                   val ins = Match.match_term con gl 
                             handle _ =>
				 raise AC_TOOLS_ERR{func = "MATCH_MP_TAC",
                                                   mesg = "No match"}
                   val ith = Conv.INST_TY_TERM ins th2 
                   val ant = #ant(Dsyntax.dest_imp(Thm.concl ith)) 
                   val gth = Drule.GENL vs (Drule.UNDISCH ith) 
                             handle _ =>
				 raise AC_TOOLS_ERR{func = "MATCH_MP_TAC",
                                               mesg = "Generalized var(s)."}
               in
               ([(A,ant)], fn thl => Thm.MP (Thm.DISCH ant gth) (hd thl))
               end
   end
end;

*)

end; (* AC_TOOLS *)

local
structure Ac_term = AC_TERM(Ac_lib)
structure Ac_subst = AC_SUBST(structure Ac_lib = Ac_lib
                              structure Ac_term = Ac_term)
structure Polynomial = POLYNOMIAL (Ac_lib)
structure Acu = ACU(structure Ac_lib = Ac_lib
                    structure Ac_subst = Ac_subst
                    structure Polynomial = Polynomial)
in
structure Ac_tools = AC_TOOLS(structure Acu = Acu)
end;
