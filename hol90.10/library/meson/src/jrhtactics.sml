signature jrh_SIG =
  sig
    type thm
    type tactic
    type justification
    type Goal
    type Goalstate
    type Tactic
    type refinement
    type Thm_Tactic
    type Thm_Tactical

    val by : Tactic -> refinement
    val bys : Tactic list -> refinement
    val rotate : int -> refinement

    val mk_Goalstate : Goal -> Goalstate

    val THEN : Tactic * Tactic -> Tactic
    val ORELSE : Tactic * Tactic -> Tactic
    val THENL : Tactic * Tactic list -> Tactic
    val convert : Tactic -> tactic

    (* some actual tactics *)
    val ALL_TAC : Tactic
    val ACCEPT_TAC : Thm_Tactic
    val ASSUME_TAC : Thm_Tactic
    val CONTR_TAC : Thm_Tactic
    val DISJ_CASES_TAC : Thm_Tactic
    val POP_ASSUM : Thm_Tactic -> Tactic
    val POP_ASSUM_LIST : (thm list -> Tactic) -> Tactic
    val FIRST_ASSUM : Thm_Tactic -> Tactic
    val ASSUM_LIST : (thm list -> Tactic) -> Tactic
    val RULE_ASSUM_TAC : (thm -> thm) -> Tactic

    val REPEAT : Tactic -> Tactic
    val EVERY : Tactic list -> Tactic
    val MAP_EVERY : ('a -> Tactic) -> 'a list -> Tactic
    val CHOOSE_TAC : Thm_Tactic
    val FIRST_X_ASSUM : Thm_Tactic -> Tactic

    (* some theorem tacticals *)
    val CONJUNCTS_THEN : Thm_Tactical
    val DISJ_CASES_THEN : Thm_Tactical
    val ORELSE_TCL: Thm_Tactical * Thm_Tactical -> Thm_Tactical
  end ;



structure jrh : jrh_SIG =
  struct
    type thm = CoreHol.Thm.thm
    type tactic = Abbrev.tactic

    open liteLib
    open Lib CoreHol;
    open Term Thm Drule;
    open LiteLib
    open Psyntax

    type Goal = (thm list * term)
    type justification = thm list -> thm
    type Goalstate = Goal list * justification
    type Tactic = Goal -> Goalstate
    type Thm_Tactic = thm -> Tactic
    type Thm_Tactical = Thm_Tactic -> Thm_Tactic
    type refinement = Goalstate -> Goalstate

    infix >-;
    fun (f >- g) x = g(f x);

    fun butlast l = #1(Lib.front_last l)
    fun mk_Goalstate g = ([g], hd)

    fun by t (gs, vf) =
      case gs of
        [] => raise Fail "Can't apply tactic to empty Goal list"
      | g::others =>
          let
            val (newgs, vf1) = t g
          in
            (newgs @ others,
             fn thl =>
             let val (t_thms, rest) = Lib.split_after (* chopn *)
                                         (length newgs) thl
             in
               vf ((vf1 t_thms)::rest)
             end)
          end


    local
      fun rotate_p1 ([], just) = ([], just)
        | rotate_p1 ((g::gs), just) =
          let
            val newgs = gs @ [g]
            fun newj ths = just (last ths::butlast ths)
          in
            (newgs, newj)
          end

      fun rotate_n1 ([], just) = ([], just)
        | rotate_n1 (gs, just) =
          let
            val (newg, newgs) = (last gs, butlast gs)
            fun newj (th::ths) = just (ths @ [th])
          in
            (newg::newgs, newj)
          end
    in
      fun rotate n =
        if n > 0 then
          funpow n rotate_p1
        else
          funpow (~n) rotate_n1
    end

    local
      (* the first parameter n is used to record the rotations performed
         on the state, so that once the tactic list has been exhausted
         the goal list can be put back into order *)
      fun bysn n [] g = rotate n g
        | bysn n (t::ts) (g as (gl,j)) =
          let
            val newg as (newgl,j') = by t g
            val k = length newgl + 1 - length gl
          in
            bysn (n - k) ts (rotate k newg)
          end
    in
      fun bys l = bysn 0 l
    end



    infix THENL
    fun (t1 THENL tlist) g =
      bys tlist (by t1 (mk_Goalstate g))

    infix THEN
    fun (t1 THEN t2) g =
      let
        val g as (gls, jf) = by t1 (mk_Goalstate g)
      in
        bys (replicate (t2, length gls)) g
      end

    fun convert (T:Tactic) ((asl:term list), (g:term)) =
      let
        val (gs, jf) = T (map ASSUME asl, g)
        val newgs = map (fn (asl, g) => (map concl asl, g)) gs
      in
        (newgs, jf)
      end

    (* our actual Tactics *)
    fun ASSUME_TAC th : Tactic =
      fn (asl, g) =>
      ([(th::asl, g)],
       fn [resth] => PROVE_HYP th resth)

    fun POP_ASSUM thf (a::asl, g) = thf a (asl, g)
    fun ASSUM_LIST thlf (asl, g) = thlf asl (asl, g)
    fun POP_ASSUM_LIST thlf (asl, g) = thlf asl ([], g)
    fun FIRST_ASSUM ttac (asl, g) =
      tryfind (fn th => ttac th (asl, g)) asl

    fun UNDISCH_THEN tm ttac (asl,g) =
      let
        val (th, asl') = remove (fn th => concl th = tm) asl
      in
        ttac th (asl', g)
      end

    fun FIRST_X_ASSUM ttac =
      FIRST_ASSUM (fn th => UNDISCH_THEN (concl th) ttac);

    fun ALL_TAC (asl, g) = ([(asl,g)], fn [th] => th)

    fun EVERY [] = ALL_TAC
      | EVERY (t::ts) = t THEN EVERY ts

    fun MAP_EVERY f l = EVERY (map f l)

    fun RULE_ASSUM_TAC f =
      POP_ASSUM_LIST (MAP_EVERY (f >- ASSUME_TAC) o rev)

    infix ORELSE
    fun (t1 ORELSE t2) g = t1 g handle _ => t2 g
    fun REPEAT t g = ((t THEN REPEAT t) ORELSE ALL_TAC) g


    fun X_CHOOSE_TAC t xth (asl, g) =
      let
        val xtm = concl xth
        val (x, bod) = dest_exists xtm
        val pat =
          ASSUME (Rsyntax.subst [{redex = x, residue = t}] bod)
      in
        ([(pat::asl, g)], fn [th] => CHOOSE (t, xth) th)
      end
    handle (Fail s)  => raise Fail ("X_CHOOSE_TAC: "^s)
         | _ => raise Fail "X_CHOOSE_TAC"

    fun thm_frees thm =
      itlist (union o free_vars) (hyp thm) (free_vars (concl thm))

    fun CHOOSE_TAC xth (asl, g) =
      let
        val x = fst (dest_exists (concl xth))
          handle _ => raise Fail "CHOOSE_TAC"
        val avoids = itlist (union o free_vars o concl) asl
                            (union (free_vars g) (thm_frees xth))
        val newvar = variant avoids x
      in
        X_CHOOSE_TAC newvar xth (asl, g)
      end


    fun CONJUNCTS_THEN ttac th =
      let val (c1, c2) = (CONJUNCT1 th, CONJUNCT2 th)
      in
        ttac c1 THEN ttac c2
      end

    fun DISJ_CASES_TAC dth =
      let
        val dtm = concl dth
        val (l,r) = dest_disj dtm
        val (thl, thr) = (ASSUME l, ASSUME r)
      in
        fn (asl, g) => ([(thl::asl, g), (thr::asl, g)],
                        fn [th1, th2] => DISJ_CASES dth th1 th2)
      end

    fun DISJ_CASES_THEN ttac th =
      DISJ_CASES_TAC th THEN POP_ASSUM ttac;

    infix ORELSE_TCL
    fun (ttcl1 ORELSE_TCL ttcl2) ttac th =
      ttcl1 ttac th handle _ => ttcl2 ttac th

    fun CONTR_TAC cth (asl, g) =
      let
        val th = CONTR g cth
      in
        ([], fn [] => th)
      end

    fun ACCEPT_TAC th (asl, g) =
      if aconv (concl th) g then
        ([], fn [] => th)
      else
        raise Fail "ACCEPT_TAC"

  end

