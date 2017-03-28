fun UTILS_ERR{func,mesg} =
      HOL_ERR{origin_structure = "Utils",
              origin_function = func,
              message = mesg};


(*----------------------------------------------------------------------------
 *
 *             MISCELLANEOUS SUPPORT
 *
 *---------------------------------------------------------------------------*)


infix 3 -->;
fun (ty1 --> ty2) = Type.mk_type{Tyop="fun", Args = [ty1,ty2]};


(*--------------------------------------------------------------------------
 * I am not sure if this really does give NNF, but it's useful
 * interactively, especially when doing proof by contradiction.
 *--------------------------------------------------------------------------*)
val NNF_CONV =
   let val DE_MORGAN = REWRITE_CONV
                        [Q.TAUT_CONV`~(x==>y) = (x /\ ~y)`,
                         Q.TAUT_CONV`~x \/ y = (x ==> y)`,DE_MORGAN_THM]
       val QUANT_CONV = NOT_EXISTS_CONV ORELSEC NOT_FORALL_CONV
   in REDEPTH_CONV (QUANT_CONV ORELSEC CHANGED_CONV DE_MORGAN)
   end;

val NNF_TAC = CONV_TAC NNF_CONV;

exception NOT_SUBSET;
fun WEAKEN_TAC (K:term list):tactic = fn  (G,a) =>
   if (Lib.all (Lib.C mem G) K)
   then ([(K,a)], fn [th] => itlist ADD_ASSUM (set_diff G K) th)
   else raise NOT_SUBSET;


(*----------------------------------------------------------------------------
 *            v    (|- !v_1...v_n. M[v_1...v_n])
 *   TUPLE   -------------------------------------------------
 *              !v. M[FST v, FST(SND v), ... SND(SND ... v)]
 *---------------------------------------------------------------------------*)
local val mk_comb = Psyntax.mk_comb
      val mk_const = Psyntax.mk_const
      fun trav tm = 
        let fun itr tm A =
           let val ty = type_of tm
               val {Tyop = "prod", Args = [ty1,ty2]} = Type.dest_type ty
           in itr (mk_comb(mk_const("FST", ty-->ty1), tm))
                  (itr(mk_comb(mk_const("SND", ty-->ty2),tm)) A)
           end handle _ => (tm::A)
        in itr tm [] end
      val pthm = theorem"pair" "PAIR"
      fun full_strip_pair tm =
        let fun strip tm A =
            if (is_pair tm) 
            then let val {fst,snd} = dest_pair tm
                  in strip fst (strip snd A) end
            else (tm::A)
        in strip tm [] end
in 
fun TUPLE v thm = GEN v (SPECL (trav v) thm)
fun TUPLE_TAC vtuple:tactic = fn (asl,w) =>
   let val {Bvar,Body} = dest_forall w
       val w1 = Term.subst [Bvar |-> vtuple] Body
       val w2 = list_mk_forall(full_strip_pair vtuple,w1)
   in ([(asl,w2)], fn [th] => PURE_REWRITE_RULE[pthm](TUPLE Bvar th))
   end
end;


(* A generally useful rewrite rule *)
val _ = add_implicit_rewrites[Q.prove`(!x:'a. ?y. x = y) /\ !x:'a. ?y. y = x`
(CONJ_TAC THEN GEN_TAC THEN Q.EXISTS_TAC`x` THEN REFL_TAC)];


(*---------------------------------------------------------------------------
 * Handling lets 
 *
 * The following is support for "pulling" lets to the top level of the term;
 * and a tactic that will then plunk the let-binding on the assumptions.
 * Pulling lets to the top level is done via higher-order rewriting. 
 *---------------------------------------------------------------------------*)
val PULL_LET = Q.prove
`!(P:'b->bool) (M:'a) N. P (let x = M in N x) = (let x = M in P (N x))`
(Rewrite.REWRITE_TAC[LET_DEF] THEN BETA_TAC THEN Rewrite.REWRITE_TAC[]);

val PULL_LET2 = Q.prove
`!(P:'c->bool) (M:'a#'b) N.
    P (let (x,y) = M in N x y) = (let (x,y) = M in P (N x y))`
(Rewrite.REWRITE_TAC[LET_DEF] THEN GEN_TAC 
 THEN TUPLE_TAC(Term`x,y:'a#'b`)
 THEN CONV_TAC (DEPTH_CONV GEN_BETA_CONV)
 THEN Rewrite.REWRITE_TAC[]);

val PULL_LET3X2 = Q.prove
`!(P:'g->bool) (M:('a#'b)#('c#'d)#('e#'f)) N.
    P (let ((v1,v2),(v3,v4),(v5,v6)) = M in N v1 v2 v3 v4 v5 v6) 
 = (let ((v1,v2),(v3,v4),(v5,v6)) = M in P (N v1 v2 v3 v4 v5 v6))`
(Rewrite.REWRITE_TAC[LET_DEF] THEN GEN_TAC THEN BETA_TAC
 THEN TUPLE_TAC(Term`((v1,v2),(v3,v4),(v5,v6)):('a#'b)#('c#'d)#('e#'f)`)
 THEN CONV_TAC (DEPTH_CONV GEN_BETA_CONV)
 THEN Rewrite.REWRITE_TAC[]);

val LET_THM = BETA_RULE (Q.AP_THM (Q.AP_THM LET_DEF `f:'a->'b`) `x:'a`);

(* Construct a paired abstraction *)
fun mk_aabs(vstr,body) = mk_abs{Bvar=vstr,Body=body}
                         handle _ => mk_pabs{varstruct = vstr, body = body};

fun dest_aabs tm = 
   let val {Bvar,Body} = dest_abs tm
   in (Bvar,Body)
   end handle _ => let val {varstruct,body} = dest_pabs tm
                   in (varstruct,body) end;

fun mk_fst tm = 
  let val ty = type_of tm
      val {Tyop="prod",Args=[alpha,beta]} = dest_type ty
      val FST = mk_const{Name="FST", Ty=mk_type{Tyop="fun",Args=[ty,alpha]}}
  in 
    mk_comb{Rator=FST, Rand = tm}
  end;

fun mk_snd tm = 
  let val ty = type_of tm
      val {Tyop="prod",Args=[alpha,beta]} = dest_type ty
      val SND = mk_const{Name="SND", Ty=mk_type{Tyop="fun",Args=[ty,beta]}}
  in 
    mk_comb{Rator=SND, Rand = tm}
  end;


(*---------------------------------------------------------------------------
 * Builds a list of projection terms for "rhs", based on structure 
 * of "tuple". Not used.

fun flat_vstruct0 tuple rhs =
  if (is_var tuple) then [rhs]
  else let val {fst,snd} = dest_pair tuple
       in flat_vstruct0 fst (mk_fst rhs) @ flat_vstruct0 snd (mk_snd rhs)
       end;
 *---------------------------------------------------------------------------*)

(*---------------------------------------------------------------------------
 * That was the clean implementation. Now for the one that gets used, we 
 * add an extra field to the return value, so that it can be made into 
 * an equality. 
 *---------------------------------------------------------------------------*)
local val dum = mk_var{Name="__dummy__", Ty=Type`:one`}
in
fun flat_vstruct tuple rhs =
  let fun flat tuple (v,rhs) =
      if (is_var tuple) then [(tuple, rhs)]
      else let val {fst,snd} = dest_pair tuple
           in   flat fst (v, mk_fst rhs) @ flat snd (v, mk_snd rhs)
           end
  in map Psyntax.mk_eq (flat tuple (dum,rhs))
  end
end;


(*---------------------------------------------------------------------------
 *
 *              Gamma |- (<vstruct> = M) ==> N
 *     --------------------------------------------------
 *              Gamma |- let <vstruct> = M in N
 *
 *---------------------------------------------------------------------------*)

local val LET_THM1 = GSYM LET_THM
      val PAIR = theorem"pair" "PAIR"
      val PAIR_RW = Rewrite.PURE_REWRITE_RULE [PAIR]
      fun lhs_repl th = {var=Dsyntax.lhs(concl th), thm=th}
in 
fun LET_INTRO thm =
  let val {ant,conseq} = dest_imp(concl thm)
      val {lhs,rhs} = dest_eq ant
      val bindings = flat_vstruct lhs rhs
      val thl = map ASSUME bindings
      val th0 = UNDISCH thm
      val th1 = SUBS thl th0
      val Bredex = mk_comb{Rator=mk_aabs(lhs,conseq),Rand=rhs}
      val th2 = EQ_MP (GSYM(GEN_BETA_CONV Bredex)) th1
      val th3 = Rewrite.PURE_ONCE_REWRITE_RULE[LET_THM1] th2
      val vstruct_thm = SUBST_CONV (map lhs_repl thl) lhs lhs;
      val th4 = PROVE_HYP (PAIR_RW vstruct_thm) th3
  in
  rev_itlist (fn bind => fn th => 
                 let val th' = DISCH bind th
                     val {lhs,rhs} = dest_eq bind
                 in MP (INST [lhs |-> rhs] th') (REFL rhs) end) 
               bindings th4
  end
end;

local fun insert x L = if (mem x L) then L else x::L
in
fun free_vars_lr tm =
  let fun frees tm A = 
       case (dest_term tm)
       of CONST _ => []
        | VAR _ => insert tm A
        | COMB{Rator,Rand} => frees Rand (frees Rator A)
        | LAMB{Bvar,Body} => Lib.set_diff (frees Body A) [Bvar]
  in rev(frees tm [])
  end
end;

(*---------------------------------------------------------------------------
 * Returns the variants and the "away" list augmented with the variants.
 *---------------------------------------------------------------------------*)
fun variants away0 vlist = 
 rev_itlist (fn v => fn (V,away) => 
    let val v' = variant away v in  (v'::away, v'::V) end) 
 vlist ([],away0);

fun unpabs tm = 
   let val (vstr,body) = dest_aabs tm
       val V = free_vars_lr vstr
   in list_mk_abs(V,body)
   end;

local
fun dot 0 vstr tm away = (vstr,tm)
  | dot n vstr tm away =
    let val {Bvar,Body} = dest_abs tm
        val v' = variant away Bvar
        val tm'  = beta_conv(mk_comb{Rator=tm, Rand=v'})
        val vstr' = subst[Bvar |-> v'] vstr
    in dot (n-1) vstr' tm' (v'::away)
    end
in
(*---------------------------------------------------------------------------
 * Alpha convert to ensure that variables bound by the "let" are not 
 * free in the assumptions of the goal. Alpha-convert in reverse on way 
 * back from achieving the goal.
 *---------------------------------------------------------------------------*)
val LET_INTRO_TAC :tactic = 
fn  (asl,w) =>
  let val {func,arg} = dest_let w
      val func' = unpabs func
      val (vstr,body) = dest_aabs func 
      val away0 = Lib.op_union aconv (free_vars func) (free_varsl asl)
      val (vstr', body') = dot (length (free_vars vstr)) vstr func' away0
      val bind = mk_eq{lhs=vstr', rhs=arg}
  in
  ([(asl,mk_imp{ant=bind,conseq=body'})], 
   fn [th] => let val let_thm = LET_INTRO th
               in EQ_MP (ALPHA (concl let_thm) w) let_thm end)
  end
end;

(*---------------------------------------------------------------------------
 * Test.
 *
    set_goal([Term`x:bool`, Term`x':bool`], 
             Term`let (x':bool,(x:bool)) = M in x'' x x' : bool`);
 *
 *---------------------------------------------------------------------------*)

(* g`!P x M N. (!x. x=M ==> P(N x)) ==> P(let (x = M) in N)`; *)


val GAP_TAC:tactic = W (ACCEPT_TAC o mk_thm);

fun be tactic = (b(); e tactic);

fun NTAC n tac = funpow n (curry (op THEN) tac) ALL_TAC;

fun Sterm q = let val tmp = !Globals.show_types
                  val _ = Globals.show_types := true
              in Lib.K (print_term(Parse.term_parser q)) 
                       (Globals.show_types := tmp);
                 Lib.say"\n"
              end;

fun DEST_IFF thm = 
   let val (th1,th2) = EQ_IMP_RULE thm
   in {ltor = th1, rtol = th2}
   end;


fun GEN_CASES_TAC case_thm:tactic = fn (g as (asl,w)) =>
   let val {Bvar,Body} = dest_forall w
   in (GEN_TAC THEN STRUCT_CASES_TAC (ISPEC Bvar case_thm)) g
   end;


(*---------------------------------------------------------------------------
 * This isn't good enough, because it nukes the thm_count and the 
 * counting_thms flag.
 *---------------------------------------------------------------------------*)
fun count f x =
  let val _ = Thm.reset_thm_count()
      val _ = counting_thms true
      val y = try f x
      val {ABS,ASSUME,BETA_CONV,DISCH,INST_TYPE,MP,
           REFL,SUBST,drule,other,...} = thm_count()
  in
    Lib.say("Total inferences = "
                 ^Lib.int_to_string(ABS + ASSUME + BETA_CONV + DISCH + 
                              INST_TYPE + MP + REFL + SUBST + drule + other)
             ^".\n");
    y end;
