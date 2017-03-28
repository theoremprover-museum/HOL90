structure Canon_Port : Canon_Port_sig = 
struct

type term = CoreHol.Term.term
type thm = CoreHol.Thm.thm
type tactic = Abbrev.tactic
type conv = Abbrev.conv
type thm_tactic = Abbrev.thm_tactic;

open liteLib ho_matchLib CoreHol Parse;
open Lib Term Dsyntax Thm Drule Tactical Tactic Conv Taut_thms Thm_cont;
open LiteLib Equal Ho_rewrite Theorems;
open Psyntax;
infix THEN THENC;

fun quote2term q tystring =
  Parse.term_parser (QUOTE "(" :: (q @ [QUOTE ("):"^tystring)]))
fun predify q = quote2term q "bool"


fun freesl tml = itlist (union o free_vars) tml [];;

fun TAUT x = Ho_rewrite.TAUT(predify x);

fun BINOP_CONV conv tm =
  let
    val (lop,r) = dest_comb tm
    val (opn,l) = dest_comb lop
  in
    MK_COMB(AP_TERM opn (conv l),conv r)
  end


fun get_heads lconsts tm (sofar as (cheads,vheads)) =
  let val (v,bod) = dest_forall tm in
    get_heads (subtract lconsts [v]) bod sofar
  end handle _ =>
    let val (l,r) =  dest_conj tm handle _ => dest_disj tm
    in
      get_heads lconsts l (get_heads lconsts r sofar)
    end handle _ =>
      let val tm' = dest_neg tm
      in
        get_heads lconsts tm' sofar
      end handle _ =>
        let
          val (hop,args) = strip_comb tm
          val len = length args
          val newheads =
            if is_const hop orelse mem hop lconsts then
              (insert (hop,len) cheads,vheads)
            else
              if len > 0 then
                (cheads,insert (hop,len) vheads)
              else
                sofar
        in
          itlist (get_heads lconsts) args newheads
        end;


fun get_thm_heads th sofar = 
      get_heads (freesl(hyp th)) (concl th) sofar;;


local
  val I_THM = Theory.theorem"combin" "I_THM"
  val APP_CONV =
    let val th = prove (--`!(f:'a->'b) x. f x = I f x`--,
                        REWRITE_TAC[I_THM])
    in
      REWR_CONV th
    end
  fun APP_N_CONV n tm =
    if n = 1 then APP_CONV tm
    else (RATOR_CONV (APP_N_CONV (n - 1)) THENC APP_CONV) tm

  fun FOL_CONV hddata tm =
    if is_forall tm then
      BINDER_CONV (FOL_CONV hddata) tm
    else
      if is_conj tm orelse is_disj tm then
        BINOP_CONV (FOL_CONV hddata) tm
      else
        let
          val (opn,args) = strip_comb tm
          val th = rev_itlist (C (curry MK_COMB))
            (map (FOL_CONV hddata) args) (REFL opn)
          val tm' = rand(concl th)
          val n = length args - assoc opn hddata handle _ => 0
        in
          if n = 0 then th
          else TRANS th (APP_N_CONV n tm')
        end
in
  fun GEN_FOL_CONV (cheads,vheads) =
    let
      val hddata =
        if vheads = [] then
          let
            val hops = mk_set (map fst cheads)
            fun getmin h =
              let val ns = mapfilter
                (fn (k,n) => if k = h then n else fail()) cheads
              in
                (if length ns < 2 then fail() else h,
                 end_itlist (curry Portable.Int.min) ns)
              end
          in
            mapfilter getmin hops
          end
        else
          map (fn t => if is_const t andalso fst(dest_const t) = "="
                         then (t,2) else (t,0))
          (mk_set (map fst (vheads @ cheads)))
    in
      FOL_CONV hddata
    end
end


local
  val NOT_EXISTS_UNIQUE_THM = Tactical.prove(
    --`~(?!x:'a. P x) = (!x. ~P x) \/ ?x x'. P x /\ P x' /\ ~(x = x')`--,
    REWRITE_TAC [Theorems.EXISTS_UNIQUE_THM, DE_MORGAN_THM, 
                 Theorems.NOT_EXISTS_THM] 
     THEN CONV_TAC (REDEPTH_CONV NOT_FORALL_CONV)
     THEN REWRITE_TAC [NOT_IMP, CONJ_ASSOC])
  val common_tauts =
    [TAUT `~(~p) = p`,
     TAUT `~(p /\ q) = ~p \/ ~q`,
     TAUT `~(p \/ q) = ~p /\ ~q`,
     TAUT `~(p ==> q) = p /\ ~q`,
     TAUT `p ==> q = ~p \/ q`,
     NOT_FORALL_THM,
     NOT_EXISTS_THM,
     EXISTS_UNIQUE_THM,
     NOT_EXISTS_UNIQUE_THM]
  and dnf_tauts =
    map TAUT [`~(p = q) = (p /\ ~q) \/ (~p /\ q)`,
              `(p = q) = (p /\ q) \/ (~p /\ ~q)`]
  and cnf_tauts =
    map TAUT [`~(p = q) = (p \/ q) /\ (~p \/ ~q)`,
              `(p = q) = (p \/ ~q) /\ (~p \/ q)`]
  val NNFC_CONV =
    GEN_REWRITE_CONV TOP_SWEEP_CONV (common_tauts @ cnf_tauts)
in
  val NNF_CONV =
    GEN_REWRITE_CONV TOP_SWEEP_CONV (common_tauts @ dnf_tauts)
  and NNFC_CONV =
    let
      fun SINGLE_SWEEP_CONV conv tm =
        let
          val th = conv tm
          val tm' = rand(concl th)
          val th' = if is_abs tm' then NNFC_CONV tm'
                    else SUB_CONV (SINGLE_SWEEP_CONV conv) tm'
        in
          TRANS th th'
        end handle _ =>
          if is_abs tm then
            NNFC_CONV tm
          else
            SUB_CONV (SINGLE_SWEEP_CONV conv) tm ;
    in
      SINGLE_SWEEP_CONV
      (GEN_REWRITE_CONV I (common_tauts @ dnf_tauts))
    end
end


val DELAMB_CONV =
  let
    val pth = prove(
      --`(((\x. s x) = t) = (!x:'a. s x:'b = t x)) /\
         ((s = \x. t x) = (!x. s x = t x))`--,
      CONV_TAC (DEPTH_CONV FUN_EQ_CONV) THEN BETA_TAC THEN
      REWRITE_TAC [])
    val qconv =
      THENQC ((TOP_DEPTH_QCONV BETA_CONV),
              (REPEATQC (THENCQC
                         ((GEN_REWRITE_CONV
                             ONCE_DEPTH_QCONV [pth]),
                          (TRY_CONV(TOP_DEPTH_QCONV BETA_CONV))))))
  in
    TRY_CONV qconv
  end;

val PROP_CNF_CONV =
  GEN_REWRITE_CONV REDEPTH_CONV
   [TAUT `a \/ (b /\ c) = (a \/ b) /\ (a \/ c)`,
    TAUT `(a /\ b) \/ c = (a \/ c) /\ (b \/ c)`,
    GSYM CONJ_ASSOC, GSYM DISJ_ASSOC];;


val PRESIMP_CONV =
  GEN_REWRITE_CONV DEPTH_CONV
   [NOT_CLAUSES, AND_CLAUSES, OR_CLAUSES, IMP_CLAUSES, EQ_CLAUSES,
    FORALL_SIMP, EXISTS_SIMP, EXISTS_OR_THM, FORALL_AND_THM,
    LEFT_EXISTS_AND_THM, RIGHT_EXISTS_AND_THM,
    LEFT_FORALL_OR_THM, RIGHT_FORALL_OR_THM];


val REFUTE_THEN =
  let val conv = REWR_CONV(TAUT `p = ~p ==> F`)
  in
    fn ttac => CONV_TAC conv THEN DISCH_THEN ttac
  end;;

val SKOLEM_CONV =
  GEN_REWRITE_CONV REDEPTH_CONV
   [RIGHT_AND_EXISTS_THM,
    LEFT_AND_EXISTS_THM,
    OR_EXISTS_THM,
    RIGHT_OR_EXISTS_THM,
    LEFT_OR_EXISTS_THM,
    SKOLEM_THM];

end;

