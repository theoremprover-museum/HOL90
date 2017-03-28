(* =====================================================================*)
(* FILE          : rec_type_support.sml                                 *)
(* DESCRIPTION   : Derived rules of inference that are useful for the   *)
(*                 concrete recursive types built by define_type.       *)
(*                 Translated from hol88.                               *)
(*                                                                      *)
(* AUTHOR        : (c) Tom Melham, University of Cambridge              *)
(* TRANSLATOR    : Konrad Slind, University of Calgary                  *)
(* DATE          : September 15, 1991                                   *)
(* =====================================================================*)


structure Rec_type_support : Rec_type_support_sig =
struct

fun REC_TYPE_SUPPORT_ERR{function,message} =
      HOL_ERR{origin_structure = "Rec_type_support",
	      origin_function = function,
	      message = message}

(* =====================================================================*)
(* STRUCTURAL INDUCTION				      (c) T Melham 1990	*)
(* =====================================================================*)

(* ---------------------------------------------------------------------*)
(* Internal function: UNIQUENESS					*)
(*									*)
(* This function derives uniqueness from unique existence:		*)
(* 									*)
(*        |- ?!x. P[x]							*)
(* --------------------------------------- 				*)
(*  |- !v1 v2. P[v1] /\ P[v2] ==> (v1=v2)				*)
(* 									*)
(* The variables v1 and v2 are genvars.					*)
(* ---------------------------------------------------------------------*)
val AP_AND = AP_TERM (--`/\`--);

local
val P = --`P:'a->bool`-- 
and v1 = genvar(==`:'a`==)
and v2 = genvar(==`:'a`==)
val th1 = SPEC P (CONV_RULE (X_FUN_EQ_CONV P) EXISTS_UNIQUE_DEF) 
val th2 = CONJUNCT2(UNDISCH(fst(EQ_IMP_RULE(RIGHT_BETA th1)))) 
val imp = GEN P (DISCH (--`$?! ^P`--) (SPECL [v1, v2] th2)) 
fun AND (e1,e2) = MK_COMB(AP_AND e1, e2)
fun beta_conj{conj1,conj2} = (BETA_CONV conj1, BETA_CONV conj2)
fun conv tm = AND (beta_conj (dest_conj tm)) 
val check = assert (fn c => (#Name(dest_const c) = "?!")) 
and v = genvar (==`:bool`==)
val alpha = ==`:'a`==
fun alpha_subst ty = [{redex = alpha, residue = ty}]
in
fun UNIQUENESS th =
   let val {Rator,Rand} = dest_comb(concl th)
       val _ = check Rator
       val s = alpha_subst (type_of (bvar Rand))
       val uniq = MP (SPEC Rand (INST_TYPE s imp)) th 
       val (V1,V2) = let val i = Term.inst s
                     in 
                     (i v1,i v2) 
                     end
       val red = conv (#ant(dest_imp(concl uniq))) 
   in 
   GEN V1 (GEN V2(SUBST[{var = v, thm = red}] 
                       (mk_imp{ant = v, conseq = mk_eq{lhs = V1, rhs = V2}})
                       uniq))
   end 
   handle _ => raise REC_TYPE_SUPPORT_ERR{function = "UNIQUENESS",message = ""}
end;

(* ---------------------------------------------------------------------*)
(* Internal function: DEPTH_FORALL_CONV					*)
(*									*)
(* DEPTH_FORALL_CONV conv `!x1...xn. tm` applies the conversion conv to *)
(* the term tm to yield |- tm = tm', and then returns:			*)
(*									*)
(*    |- (!x1...xn. tm)  =  (!x1...xn. tm')				*)
(*									*)
(* ---------------------------------------------------------------------*)

fun DEPTH_FORALL_CONV conv tm = 
   let val (vs,th) = (I ## conv) (strip_forall tm) 
   in
   itlist FORALL_EQ vs th 
   end;

(* ---------------------------------------------------------------------*)
(* Internal function: CONJS_CONV					*)
(*									*)
(* CONJS_CONV conv `t1 /\ t2 /\ ... /\ tn` applies conv to each of the  *)
(* n conjuncts t1,t2,...,tn and then rebuilds the conjunction from the  *)
(* results.								*)
(*									*)
(* ---------------------------------------------------------------------*)

fun CONJS_CONV conv tm = 
   let val {conj1,conj2} = dest_conj tm
   in
   MK_COMB(AP_AND (conv conj1), CONJS_CONV conv conj2) 
   end
   handle _ => conv tm;


(* ---------------------------------------------------------------------*)
(* Internal function: CONJS_SIMP					*)
(*									*)
(* CONJS_SIMP conv `t1 /\ t2 /\ ... /\ tn` applies conv to each of the  *)
(* n conjuncts t1,t2,...,tn.  This should reduce each ti to `T`.  I.e.  *)
(* executing conv ti should return |- ti = T.  The result returned by   *)
(* CONJS_SIMP is then: |- (t1 /\ t2 /\ ... /\ tn) = T			*)
(*									*)
(* ---------------------------------------------------------------------*)

local
val T_AND_T = CONJUNCT1 (SPEC (--`T`--) AND_CLAUSES) 
in
val CONJS_SIMP  = 
   let fun simp conv tm = 
          let val {conj1,conj2} = dest_conj tm
          in
          TRANS (MK_COMB(AP_AND (conv conj1), simp conv conj2))
                (T_AND_T)
          end
          handle _ => conv tm 
   in simp 
   end
end;

(* ---------------------------------------------------------------------*)
(* Internal function: T_AND_CONV					*)
(*									*)
(* T_AND_CONV `T /\ t` returns |- T /\ t = t				*)
(*									*)
(* ---------------------------------------------------------------------*)

local
val T_AND = GEN_ALL (CONJUNCT1 (SPEC_ALL AND_CLAUSES))
in
fun T_AND_CONV tm = SPEC (#conj2(dest_conj tm)) T_AND 
end;

(* ---------------------------------------------------------------------*)
(* Internal function: GENL_T						*)
(*									*)
(* GENL_T [x1;...;xn] returns |- (!x1...xn.T) = T			*)
(*									*)
(* ---------------------------------------------------------------------*)

local
val t = --`T`--
val t_eq_t = REFL t
in
fun GENL_T [] = t_eq_t
  | GENL_T l =
      let val gen = list_mk_forall(l,t) 
          val imp1 = DISCH gen (SPECL l (ASSUME gen)) 
          val imp2 = DISCH t (GENL l (ASSUME t)) 
      in IMP_ANTISYM_RULE imp1 imp2 
      end
end;
    
(* ---------------------------------------------------------------------*)
(* Internal function: SIMP_CONV						*)
(*									*)
(* SIMP_CONV is used by prove_induction_thm to simplify to `T` terms of *)
(* the following two forms:						*)
(*									*)
(*   1: !x1...xn. (\x.T)v = (\x1...xn.T) x1 ... xn			*)
(*									*)
(*   2: !x1...xn. (\x.T)v = 						*)
(*      (\y1...ym x1..xn. (y1 /\.../\ ym) \/ t) ((\x.T)u1)...((\x.T)um) *)
(*      					       x1 ... xn	*)
(*									*)
(* If tm, a term of one of these two forms, is the argument to SIMP_CONV*)
(* then the theorem returned is |- tm = T.				*)
(* ---------------------------------------------------------------------*)

local
val v = genvar (==`:bool`==)
and tr = --`T`-- 
val T_OR = GEN v (CONJUNCT1 (SPEC v OR_CLAUSES)) 
fun DISJ_SIMP tm =
   let val {disj1,disj2} = dest_disj tm
       val eqn = SYM(CONJS_SIMP BETA_CONV disj1) 
   in
   SUBST [{var = v, thm = eqn}]
         (mk_eq{lhs = mk_disj{disj1 = v,disj2 = disj2}, rhs = tr})
         (SPEC disj2 T_OR) 
   end
val eq = --`$= :bool->bool->bool`--
and T_EQ_T = EQT_INTRO(REFL tr)
in
fun SIMP_CONV tm =
   let val (vs,{lhs,rhs}) = (I ## dest_eq) (strip_forall tm) 
       val rsimp = (LIST_BETA_CONV THENC (DISJ_SIMP ORELSEC REFL)) rhs 
       and lsimp = AP_TERM eq (BETA_CONV lhs) 
       and gent  = GENL_T vs 
       val eqsimp = TRANS (MK_COMB(lsimp,rsimp)) T_EQ_T 
   in
   TRANS (itlist FORALL_EQ vs eqsimp) gent 
   end
end;

(* ---------------------------------------------------------------------*)
(* Internal function: HYP_SIMP						*)
(*									*)
(* HYP_SIMP is used by prove_induction_thm to simplify induction 	*)
(* hypotheses according to the following scheme:			*)
(*									*)
(*   1: !x1...xn. P t = (\x1...xn.T) x1...xn				*)
(*									*)
(*         simplifies to    						*)
(*									*)
(*      !x1...xn. P t							*)
(*									*)
(*   2: !x1...xn. P t = 						*)
(*        ((\y1..ym x1..xn. y1 /\ ... /\ ym) \/ P t) v1 ... vm x1 ... xn*)
(*									*)
(*         simplifies to						*)
(*									*)
(*      !x1...xn. (v1 /\ ... /\ vm) ==> P t				*)
(*									*)
(* ---------------------------------------------------------------------*)

local
val v = genvar (==`:bool`==)
and tr = --`T`-- 
val EQ_T = GEN v (CONJUNCT1 (CONJUNCT2 (SPEC v EQ_CLAUSES)))
fun R_SIMP tm =
   let val {lhs,rhs} = dest_eq tm 
   in
   if (rhs = tr) 
   then SPEC lhs EQ_T 
   else SPECL [lhs, #disj1(dest_disj rhs)] OR_IMP_THM 
   end
val eq = --`$= :bool->bool->bool`--
in
fun HYP_SIMP tm =
   let val (vs,{lhs,rhs}) = (I ## dest_eq) (strip_forall tm) 
       val eqsimp = AP_TERM (mk_comb{Rator = eq, Rand = lhs})
                            (LIST_BETA_CONV rhs)
       val rsimp = CONV_RULE (RAND_CONV R_SIMP) eqsimp 
   in
   itlist FORALL_EQ vs rsimp
   end
end;

(* ---------------------------------------------------------------------*)
(* Internal function: ANTE_ALL_CONV					*)
(*									*)
(* ANTE_ALL_CONV `!x1...xn. P ==> Q` restricts the scope of as many of	*)
(* the quantified x's as possible to the term Q.  			*)
(* ---------------------------------------------------------------------*)

fun ANTE_ALL_CONV tm = 
   let val (vs,{ant,...}) = (I ## dest_imp) (strip_forall tm) 
       val (ov,iv) = partition (C free_in ant) vs 
       val thm1 = GENL iv (UNDISCH (SPECL vs (ASSUME tm))) 
       val thm2 = GENL ov (DISCH ant thm1) 
       val asm = concl thm2 
       val thm3 = SPECL iv (UNDISCH (SPECL ov (ASSUME asm))) 
       val thm4 = GENL vs (DISCH ant thm3) 
   in
   IMP_ANTISYM_RULE (DISCH tm thm2) (DISCH asm thm4) 
   end;

(* ---------------------------------------------------------------------*)
(* Internal function: CONCL_SIMP					*)
(*									*)
(* CONCL_SIMP `\x.T = P` returns: |- (\x.T = P) = (!y. P y) where y is	*)
(* an appropriately chosen variable.					*)
(* ---------------------------------------------------------------------*)

local
val v = genvar (==`:bool`==)
val T_EQ = GEN v (CONJUNCT1 (SPEC v EQ_CLAUSES))
in
fun CONCL_SIMP tm = 
   let val eq = FUN_EQ_CONV tm 
       val {Bvar,Body} = dest_forall(rhs(concl eq))
       val eqn = RATOR_CONV(RAND_CONV BETA_CONV) Body
       and simp = SPEC (rhs Body) T_EQ 
   in
   TRANS eq (FORALL_EQ Bvar (TRANS eqn simp))
  end
end;

(* ---------------------------------------------------------------------*)
(* prove_induction_thm: prove a structural induction theorem from a type*)
(* axiom of the form returned by define_type.				*)
(*									*)
(* EXAMPLE: 								*)
(*									*)
(* Input: 								*)
(* 									*)
(*    |- !x f. ?! fn. (fn[] = x) /\ (!h t. fn(CONS h t) = f(fn t)h t) 	*)
(* 									*)
(* Output:								*)
(* 									*)
(*    |- !P. P[] /\ (!t. P t ==> (!h. P(CONS h t))) ==> (!l. P l)	*)
(* 									*)
(* ---------------------------------------------------------------------*)
exception PROVE_INDUCTION_THM_ERR;

local
val B = ==`:bool`==
val tr = --`T`--
fun gen 0 = []
  | gen n = (genvar B)::(gen (n-1))
(* fun mk_fn P ty tm = 
   let val (vars,c) = (I ## (rand o #lhs o dest_eq))(strip_forall tm) 
       val n = length(filter (fn t => type_of t = ty) vars) 
   in
   if (n=0) 
   then list_mk_abs (vars, tr) 
   else let val bools = gen n  
            val term = mk_disj{disj1 = list_mk_conj bools,
                               disj2 = mk_comb{Rator = P, Rand = c}} 
        in
        list_mk_abs((bools@vars),term) 
        end 
   end
*)
fun mk_fn P ty tm = 
   let val {lhs,rhs} = dest_eq(snd(strip_forall tm))
       val c = rand lhs
       val args = snd(strip_comb rhs)
       val vars = filter is_var args
       val n = length(filter (fn t => type_of t = ty) vars)
   in if (n=0) 
      then list_mk_abs (vars, tr)
      else let val bools = gen n
               val term = mk_disj {disj1 = list_mk_conj bools,
                                   disj2 = mk_comb{Rator = P, Rand = c}}
           in list_mk_abs((bools@vars),term)
           end
   end
val LCONV = RATOR_CONV o RAND_CONV 
val conv1 = LCONV(CONJS_SIMP SIMP_CONV) THENC T_AND_CONV 
and conv2 = CONJS_CONV (HYP_SIMP THENC TRY_CONV ANTE_ALL_CONV) 
in
fun prove_induction_thm th =
   let val {Bvar,Body} = dest_abs(rand(snd(strip_forall(concl th))))
       val {Args = [ty, rty],...} = dest_type (type_of Bvar)
       val inst = INST_TYPE [{redex = rty, residue = B}] th 
       val P = mk_primed_var{Name = "P", Ty = mk_type{Tyop = "fun",
                                                      Args = [ty,B]}}
       and v = genvar ty 
       and cases = strip_conj Body
       val uniq = let val (vs,tm) = strip_forall(concl inst) 
                      val thm = UNIQUENESS(SPECL vs inst)
                  in
                  GENL vs (SPECL [mk_abs{Bvar = v, Body = tr}, P] thm)
                  end
      val spec = SPECL (map (mk_fn P ty) cases) uniq 
      val simp =  CONV_RULE (LCONV(conv1 THENC conv2)) spec 
   in
   GEN P (CONV_RULE (RAND_CONV CONCL_SIMP) simp)
   end
   handle _ => raise REC_TYPE_SUPPORT_ERR{function = "prove_induction_thm",
					  message = ""}
end;


(* ---------------------------------------------------------------------*)
(* Internal function: NOT_ALL_THENC					*)
(*									*)
(* This conversion first moves negation inwards through an arbitrary	*)
(* number of nested universal quantifiers. It then applies the supplied	*)
(* conversion to the resulting inner negation.  For example if:		*)
(*									*)
(*	conv "~tm" ---> |- ~tm = tm'					*)
(* then									*)
(*									*)
(*       NOT_ALL_THENC conv "~(!x1 ... xn. tm)"				*)
(*									*)
(* yields:								*)
(*									*)
(*       |- ~(!x1...xn.tm) = ?x1...xn.tm'				*)
(* ---------------------------------------------------------------------*)

fun NOT_ALL_THENC conv tm = 
   (NOT_FORALL_CONV THENC 
    (RAND_CONV (ABS_CONV (NOT_ALL_THENC conv)))) tm
    handle _ => conv tm;

(* ---------------------------------------------------------------------*)
(* Internal function: BASE_CONV						*)
(*									*)
(* This conversion does the following simplification:			*)
(*									*)
(*    BASE_CONV "~((\x.~tm)y)"  --->  |- ~((\x.~tm)y) = tm[y/x]		*)
(*									*)
(* ---------------------------------------------------------------------*)

local
val NOT_NOT = CONJUNCT1 NOT_CLAUSES 
and neg = --`$~`--
in
fun BASE_CONV tm =
   let val beta = BETA_CONV (dest_neg tm) 
       val simp = SPEC (rand(rhs(concl beta))) NOT_NOT 
   in
   TRANS (AP_TERM neg beta) simp 
   end
end;

(* ---------------------------------------------------------------------*)
(* Internal function: STEP_CONV						*)
(*									*)
(* This conversion does the following simplification:			*)
(*									*)
(*    STEP_CONV "~(tm' ==> !x1..xn.(\x.~tm)z"  				*)
(*									*)
(* yields:								*)
(*									*)
(*   |- ~(tm' ==> !x1..xn.(\x.~tm)z = tm' /\ ?x1..xn.tm[z/x]  		*)
(* ---------------------------------------------------------------------*)

local
val v1 = genvar (==`:bool`==) 
and v2 = genvar (==`:bool`==)  
in
fun STEP_CONV tm =
   let val {ant,conseq} = dest_imp(dest_neg tm) 
       val th1 = SPEC conseq (SPEC ant NOT_IMP) 
       val simp = NOT_ALL_THENC BASE_CONV (mk_neg conseq)
   in
   SUBST [{var = v2, thm = simp}]
         (mk_eq{lhs = tm, rhs = mk_conj{conj1 = ant, conj2 = v2}})
         th1 
   end
end;

(* ---------------------------------------------------------------------*)
(* Internal function: NOT_IN_CONV					*)
(*									*)
(* This first conversion moves negation inwards through conjunction and	*)
(* universal quantification:						*)
(*									*)
(*   NOT_IN_CONV  "~(!x1..xn.c1 /\ ... /\ !x1..xm.cn)"			*)
(*									*)
(* to transform the input term into:					*)
(*									*)
(*   ?x1..xn.~c1 \/ ... \/ ?x1..xm.~cn					*)
(*									*)
(* It then applies either BASE_CONV or STEP_CONV to each subterm ~ci.	*)
(* ---------------------------------------------------------------------*)

local
val DE_MORG = GENL [--`A:bool`--, --`B:bool`--]
                   (CONJUNCT1(SPEC_ALL DE_MORGAN_THM))
and cnv = BASE_CONV ORELSEC STEP_CONV 
and v1 = genvar (==`:bool`==)
and v2 = genvar (==`:bool`==)
in
fun NOT_IN_CONV tm =
   let val {conj1,conj2} = dest_conj(dest_neg tm) 
       val thm = SPEC conj2 (SPEC conj1 DE_MORG) 
       val cth = NOT_ALL_THENC cnv (mk_neg conj1) 
       and csth = NOT_IN_CONV (mk_neg conj2) 
   in
   SUBST [{var = v1, thm = cth},{var = v2, thm = csth}] 
         (mk_eq{lhs = tm, rhs = mk_disj{disj1 = v1, disj2 = v2}})
         thm 
   end
   handle _ => NOT_ALL_THENC cnv tm
end;
	    

(* ---------------------------------------------------------------------*)
(* Internal function: STEP_SIMP						*)
(*									*)
(* This rule does the following simplification:				*)
(*									*)
(*    STEP_RULE "?x1..xi. tm1 /\ ?xj..xn. tm2"				*)
(*									*)
(* yields:								*)
(*									*)
(*   ?x1..xi.tm1 /\ ?xj..xn.tm2 |- ?x1..xn.tm2				*)
(*									*)
(* For input terms of other forms, the rule yields:			*)
(*									*)
(*   STEP_RULE "tm" ---> tm |- tm					*)
(* ---------------------------------------------------------------------*)

local
fun EX tm th = EXISTS (mk_exists{Bvar = tm, Body = concl th},tm) th 
fun CH tm th = CHOOSE (tm,ASSUME (mk_exists{Bvar = tm, Body = hd(hyp th)})) th
in
fun STEP_SIMP tm = 
   let val (vs,body) = strip_exists tm 
   in
   itlist (fn t => CH t o EX t) vs (CONJUNCT2 (ASSUME body)) 
   end
   handle _ => ASSUME tm
end;
	 

(* ---------------------------------------------------------------------*)
(* Internal function: DISJ_CHAIN					*)
(*									*)
(* Suppose that 							*)
(*									*)
(*    rule "tmi"  --->   tmi |- tmi'		(for 1 <= i <= n)	*)
(*									*)
(* then:								*)
(*									*)
(*       |- tm1 \/ ... \/ tmn						*)
(*    ---------------------------   DISJ_CHAIN rule			*)
(*      |- tm1' \/ ... \/ tmn' 						*)
(* ---------------------------------------------------------------------*)

fun DISJS_CHAIN rule th = 
   let val concl_th = concl th
   in
   let val {disj1,disj2} = dest_disj concl_th 
       val i1 = rule disj1
       and i2 = DISJS_CHAIN rule (ASSUME disj2) 
   in
   DISJ_CASES th (DISJ1 i1 (concl i2)) (DISJ2 (concl i1) i2) 
   end
   handle _ => MP (DISCH concl_th (rule concl_th)) th
   end;
		

(* ---------------------------------------------------------------------*)
(* prove_cases_thm: prove a cases or "exhaustion" theorem for a concrete*)
(* recursive type from a structural induction theorem of the form 	*)
(* returned by prove_induction_thm.					*)
(*									*)
(* EXAMPLE: 								*)
(*									*)
(* Input: 								*)
(* 									*)
(*    |- !P. P[] /\ (!t. P t ==> (!h. P(CONS h t))) ==> (!l. P l)	*)
(* 									*)
(* Output:								*)
(* 									*)
(*    |- !l. (l = []) \/ (?t h. l = CONS h t)				*)
(* 									*)
(* ---------------------------------------------------------------------*)

fun prove_cases_thm th = 
   let val {Bvar,Body} = dest_forall
                            (#conseq(dest_imp(#Body(dest_forall(concl th)))))
       val v = genvar (type_of Bvar) 
       val pred = mk_abs{Bvar = v, Body = mk_neg(mk_eq{lhs = Bvar,rhs=v})} 
       val th1 = CONV_RULE BETA_CONV (SPEC Bvar (UNDISCH(SPEC pred th)))
       val th2 = NOT_INTRO (DISCH_ALL (MP th1 (REFL Bvar)))
       val th3 = CONV_RULE NOT_IN_CONV th2 
   in
   GEN Bvar (DISJS_CHAIN STEP_SIMP th3) 
   end
   handle _ => raise REC_TYPE_SUPPORT_ERR{function = "prove_cases_thm",
                                          message = "invalid input theorem"};


(* =====================================================================*)
(* PROOF THAT CONSTRUCTORS OF RECURSIVE TYPES ARE ONE-TO-ONE		*)
(* =====================================================================*)

(* ---------------------------------------------------------------------*)
(* Internal function: PAIR_EQ_CONV 					*)
(*									*)
(* A call to PAIR_EQ_CONV "(x1,...,xn) = (y1,...,yn)" returns:		*)
(*									*)
(*   |- ((x1,...,xn) = (y1,...,yn)) = (x1 = y1) /\ ... /\ (xn = yn)	*)
(* 									*)
(* ---------------------------------------------------------------------*)
local
val PAIR_EQ' = theorem "pair" "PAIR_EQ"
val PAIR_EQ = GENL (rev(free_vars (concl PAIR_EQ'))) PAIR_EQ'
val v = genvar (==`:bool`==)
val alpha = ==`:'a`==
val beta = ==`:'b`==
in
fun PAIR_EQ_CONV tm = 
   let val {lhs,rhs} = dest_eq tm
       val {fst = x, snd = xs} = dest_pair lhs
       val {fst = y, snd = ys} = dest_pair rhs
       val xty = type_of x
       and xsty = type_of xs
       val thm = INST_TYPE [{redex = alpha,residue = xty},
                            {redex = beta, residue = xsty}] PAIR_EQ 
       val spec = SPEC ys (SPEC y (SPEC xs (SPEC x thm)))
       val reqn = PAIR_EQ_CONV (mk_eq{lhs = xs, rhs = ys}) 
       val pat = mk_eq{lhs = tm,
                       rhs = mk_conj{conj1 = mk_eq{lhs = x, rhs = y},
                                     conj2 = v}} 
   in
   SUBST [{var = v, thm = reqn}] pat spec 
   end
   handle _ => (REFL tm)
end;


(* ---------------------------------------------------------------------*)
(* Internal function: list_variant					*)
(*									*)
(* makes variants of the variables in l2 such that they are all not in	*)
(* l1 and are all different.						*)
(* ---------------------------------------------------------------------*)
fun list_variant l1 [] = []
  | list_variant l1 (h::t) =
       let val v = variant l1 h
       in
       v::(list_variant (v::l1) t)
       end;

fun mk_subst2 [] [] = []
  | mk_subst2 (a::L1) (b::L2) = {redex = b, residue = a}::mk_subst2 L1 L2;


(* ---------------------------------------------------------------------*)
(* Internal function: prove_const_one_one.				*)
(*									*)
(* This function proves that a single constructor of a recursive type is*)
(* one-to-one (it is called once for each appropriate constructor). The *)
(* theorem input, th, is the characterizing theorem for the recursive 	*)
(* type in question.  The term, tm, is the defining equation for the 	*)
(* constructor in question, taken from the body of the theorem th.	*)
(*									*)
(* For example, if:							*)
(*									*)
(*  th = |- !x f. ?! fn. (fn[] = x) /\ (!h t. fn(CONS h t) = f(fn t)h t)*)
(*									*)
(* and									*)
(*									*)
(*  tm = "!h t. fn(CONS h t) = f(fn t)h t"				*)
(*									*)
(* then prove_const_one_one th tm yields:				*)
(*								 	*)
(*  |- !h t h' t'. (CONS h t = CONS h' t') = (h = h') /\ (t = t')	*)
(*									*)
(* ---------------------------------------------------------------------*)

fun prove_const_one_one th tm = 
   let val (vs,{lhs,...}) = (I ## dest_eq)(strip_forall tm) 
       val C = rand lhs
       fun mk_pair_curried p0 p1 = mk_pair{fst = p0, snd = p1}
       val tup = end_itlist mk_pair_curried (snd(strip_comb C))
       val tupty = type_of tup 
       val eq = mk_eq{lhs = inst [{redex=type_of lhs, residue = tupty}] lhs,
                      rhs = tup}
       val eqn = prove_rec_fn_exists th eq 
       val vvs = list_variant vs vs 
       val C' = subst (mk_subst2 vvs vs) C
       val C_eq_C' = mk_eq{lhs = C, rhs = C'}
       val sndC = snd(strip_comb C)
       val vareqs = list_mk_conj
                      (map2 (fn x => fn y => mk_eq{lhs=x,rhs=y})
                            sndC (snd(strip_comb C')))
       val asms = map2 (fn th => fn v => {var = v, thm = th})
                       (CONJUNCTS (ASSUME vareqs)) sndC
       val imp1 = DISCH vareqs (SUBST_CONV asms C C) 
       val {Bvar,Body} = dest_exists(concl eqn)
       val fndef = ASSUME Body
       val r1 = REWR_CONV fndef (mk_comb{Rator=Bvar,Rand=C}) 
       and r2 = REWR_CONV fndef (mk_comb{Rator=Bvar,Rand=C'}) 
       and asm = AP_TERM Bvar (ASSUME C_eq_C') 
       and v1 = genvar tupty
       and v2 = genvar tupty 
       val thm = SUBST [{var=v1,thm=r1}, {var=v2,thm=r2}]
                       (mk_eq{lhs=v1,rhs=v2})
                       asm
       val aimp = DISCH C_eq_C' (CONV_RULE PAIR_EQ_CONV thm) 
       val imp2 = CHOOSE (Bvar,eqn) aimp 
   in
   GENL vs (GENL vvs (IMP_ANTISYM_RULE imp2 imp1))
   end;

(* ---------------------------------------------------------------------*)
(* prove_constructors_one_one : prove that the constructors of a given	*)
(* concrete recursive type are one-to-one. The input is a theorem of the*)
(* form returned by define_type.					*)
(*									*)
(* EXAMPLE: 								*)
(*									*)
(* Input: 								*)
(* 									*)
(*    |- !x f. ?! fn. (fn[] = x) /\ (!h t. fn(CONS h t) = f(fn t)h t) 	*)
(*									*)
(* Output:								*)
(*									*)
(*    |- !h t h' t'. (CONS h t = CONS h' t') = (h = h') /\ (t = t')	*)
(* ---------------------------------------------------------------------*)

fun prove_constructors_one_one th = 
   let val eqns = strip_conj
                     (#Body(dest_abs(rand(snd(strip_forall(concl th))))))
       val funs = gather (fn tm => is_comb(rand(lhs(snd(strip_forall tm)))))
                         eqns 
   in
   LIST_CONJ (map (prove_const_one_one th) funs) 
   end
   handle _ =>
       raise REC_TYPE_SUPPORT_ERR{function = "prove_constructors_one_one",
				  message = ""};


(* =====================================================================*)
(* DISTINCTNESS OF VALUES FOR EACH CONSTRUCTOR				*)
(* =====================================================================*)

(* ---------------------------------------------------------------------*)
(* prove_constructors_distinct : prove that the constructors of a given	*)
(* recursive type yield distict (non-equal) values.			*)
(*									*)
(* EXAMPLE: 								*)
(*									*)
(* Input: 								*)
(* 									*)
(*    |- !x f. ?! fn. (fn[] = x) /\ (!h t. fn(CONS h t) = f(fn t)h t) 	*)
(* 									*)
(* Output:								*)
(* 									*)
(*    |- !h t. ~([] = CONS h t)						*)
(* ---------------------------------------------------------------------*)

local
val NOT_SUC = theorem "num" "NOT_SUC" 
and INV_SUC = theorem "num" "INV_SUC" 
val SUC = --`SUC`-- 
and zero = --`0`-- 
and lemma = GEN_ALL(NOT_ELIM(NOT_EQ_SYM(SPEC_ALL NOT_SUC))) 
fun geneqs (h::rst) t = 
   let val (vars,{lhs,...}) = (I ## dest_eq) (strip_forall h) 
       val new_lhs = mk_eq{lhs = lhs, rhs = t}
   in
   if (null rst) 
   then ([],new_lhs) 
   else let val (rl,tm) = geneqs rst (mk_comb{Rator = SUC, Rand = t}) 
        in
	((t::rl), mk_conj{conj1 = new_lhs, conj2 = tm}) 
        end 
   end
fun step [_] = []
  | step (h::rst) =
        let val [l,r] = snd(strip_comb(#ant(dest_imp(concl h)))) 
            val th = IMP_TRANS (SPEC r (SPEC l INV_SUC)) h 
        in
        th::(step rst)
        end
fun mk_rot [] = []
  | mk_rot ths =  ths::(mk_rot (step ths) )
fun rule fn1 eth th = 
   let val {lhs,rhs} = dest_eq(#ant(dest_imp(concl th)))
       val asm = mk_eq{lhs = rand lhs, rhs = rand rhs}
       val imp = (IMP_TRANS (DISCH asm (AP_TERM fn1 (ASSUME asm))) th) 
   in
   GEN_ALL (NOT_INTRO(CHOOSE (fn1,eth) imp)) 
   end 
val N = type_of zero
val gv1 = genvar N
and gv2 = genvar N
val pat = mk_imp{ant = mk_eq{lhs = gv1, rhs = gv2},conseq = --`F`--}
fun subsfn rul eq eqs [] acc = acc
  | subsfn rul eq (heq::eqrst) (h::t) acc =
      let val vs = free_vars (rand(rhs(concl eq))) 
          and nvs = free_vars (rand(rhs(concl heq)))
          val eqn = INST (mk_subst2 (list_variant vs nvs) nvs) heq 
          val rnum = rhs(#ant(dest_imp(concl h))) 
          val thm = SUBST [{var = gv1, thm = eq},{var = gv2, thm = eqn}] pat h
      in 
      (rul thm)::(subsfn rul eq eqrst t acc)
      end
fun subs rul (eq::eqs) [] = []
  | subs rul (eq::eqs) (h::t) = subsfn rul eq eqs h (subs rul eqs t)
in
fun prove_constructors_distinct th =
   let val {Bvar,Body} = dest_abs(rand(snd(strip_forall(concl th)))) 
       val {Args = [_,ty],...} = dest_type(type_of Bvar)
       val eqns = strip_conj(inst [{redex = ty, residue = N}] Body)
   in
   if (null(tl eqns))
   then raise REC_TYPE_SUPPORT_ERR{function = "prove_constructors_distinct",
				   message = "1"}
   else let val (nums,eqs) = geneqs eqns zero
            val eth = prove_rec_fn_exists th eqs 
            val rots = mk_rot (map (C SPEC lemma) nums) 
            val {Bvar,Body = asm} = dest_exists(concl eth) 
            val fneqs = map (SYM o SPEC_ALL) (CONJUNCTS (ASSUME asm)) 
        in
        LIST_CONJ (subs (rule Bvar eth) fneqs rots) 
        end
   end
   handle (e as HOL_ERR{origin_structure ="Rec_type_support",
                        origin_function = "prove_constructors_distinct",...})
            => raise e
        | _ => raise REC_TYPE_SUPPORT_ERR
	              {function = "prove_constructors_distinct",
		       message = ""}
end;

end; (* Rec_type_support *)
