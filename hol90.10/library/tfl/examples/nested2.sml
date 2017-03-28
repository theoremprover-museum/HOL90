new_theory"nested" handle _ => ();


val thy = "-";
val eqns = Term`(H 0 = 0) /\ 
                (H(SUC x) = H(H x))`;

(* Abbreviations *)
structure R = Rules;
structure S = USyntax;
structure U = S.Utils;

fun genl dont_quantify tm =
   let val V = free_vars_lr tm
       val V' = U.set_diff S.aconv V dont_quantify
   in list_mk_forall (V', tm)
   end;
   
(*---------------------------------------------------------------------------*
 * This might work uniformly over nested and non-nested descriptions, if I   *
 * do it right.                                                              *
 *---------------------------------------------------------------------------*)
 let val {proto_def,WFR,pats,extracta} = HOL_Tfl.Prim.wfrec_eqns eqns
     val R1 = S.rand WFR
     val f = S.lhs proto_def
     val {Name,...} = S.dest_var f
     val (extractants,TCl) = U.unzip extracta
     val TCs = U.Union S.aconv TCl
     val nestedf = mk_select{Bvar=f, 
                     Body=list_mk_conj(map (genl[R1,f] o concl o #1) extracta)}
     val full_rqt = WFR::TCs
     val nested_full_rqt = map (S.subst [f |-> nestedf]) full_rqt
     val R' = S.mk_select{Bvar=R1, Body=list_mk_conj nested_full_rqt}
     val R'abs = S.rand R'
     val (def,theory) = Thry.make_definition thy (U.concat Name "_def") 
                                                 (S.subst[R1 |-> R'] proto_def)
     val fconst = #lhs(S.dest_eq(concl def)) 
     val tych = Thry.typecheck theory
     val baz = R.DISCH (tych proto_def)
                 (U.itlist (R.DISCH o tych) full_rqt (R.LIST_CONJ extractants))
     val def' = R.MP (R.SPEC (tych fconst) 
                             (R.SPEC (tych R') (R.GENL[tych R1, tych f] baz)))
                     def
     val body_th = R.LIST_CONJ (map (R.ASSUME o tych) nested_full_rqt)
     val bar = R.MP (R.BETA_RULE(R.ISPECL[tych R'abs, tych R1] Thms.SELECT_AX))
                     body_th
 in {theory = theory, R=R1,
     rules = U.rev_itlist (U.C R.MP) (R.CONJUNCTS bar) def',
     full_pats_TCs = merge (map pat_of pats) (U.zip (givens pats) TCl),
     patterns = pats}
 end;

