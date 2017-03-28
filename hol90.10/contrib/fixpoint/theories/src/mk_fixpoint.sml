(*---------------------------------------------------------------------------
 * Theory of fixedpoints of predicates in HOL
 *  
 *  Original Author : Mike Gordon
 *  Converted to HOL90 by : Chris Toshok
 *---------------------------------------------------------------------------*)


val _ = new_theory "fixpoint";

val _ = add_theory_to_sml "num";

local val thykind = SysParams.theory_file_type
      val path = (!HOLdir)^"contrib/fixpoint/theories/"^thykind^"/"
in
  val _ = theory_path := path::(!theory_path)
end


(*---------------------------------------------------------------------------
 * Definition of the Scott ordering on predicates.
 *---------------------------------------------------------------------------*)

val LESS_DEF = new_infix_definition("LESS_DEF",
 --`$<<< f1 f2 = !x:'a. f1 x ==> f2 x`--,
 450);


(*---------------------------------------------------------------------------
 * Non constructive definition of the least fixed point operator.
 *---------------------------------------------------------------------------*)

val FIX = new_definition("FIX",
--`FIX fun = @f:'a->bool. (fun f = f) /\
                     !f'. (fun f' = f') ==> (f <<< f')`--);
  
(*---------------------------------------------------------------------------
 * A function for getting the iterates f^n x, where
 *
 *  f    : 'a -> 'a
 *  ITER : num -> ('a->'a) -> ('a->'a)
 *
 *  INTER n f x = f^n x
 *---------------------------------------------------------------------------*)

val FUNPOW=new_recursive_definition
 {name = "FUNPOW",
  def = --`(FUNPOW 0       f x = (x:'a)) /\
           (FUNPOW (SUC n) f x = f(FUNPOW n f x))`--,
  fixity = Prefix,
  rec_axiom = theorem "prim_rec" "num_Axiom"};


(*---------------------------------------------------------------------------
 * Limit of a chain of predicates
 *  
 *   U c = c(0) u c(1) u ... u c(n) u ... = \x.?n. c n x
 *   n
 *---------------------------------------------------------------------------*)
val SUP =
 new_definition("SUP",
     (--`SUP c = \x:'a.?n:num. c n x`--));


(*---------------------------------------------------------------------------
 * The bottom (least defined) predicate.
 *---------------------------------------------------------------------------*)
val BOT = new_definition ("BOT",
                          (--`BOT : 'a->bool = \x.F`--));


(*---------------------------------------------------------------------------
 * Limit of the chain of iterates
 *
 *     BOT u fun BOT u fun(fun BOT) ... u fun^n BOT u ...
 *
 *     LIM_FUNPOW fun = U FUNPOW n fun BOT
 *                    n
 *
 *                  = SUP (\n. FUNPOW n fun BOT)
 *---------------------------------------------------------------------------*)
val LIM_FUNPOW=new_definition ("LIM_FUNPOW",
(--`LIM_FUNPOW(fun:('a->bool)->('a->bool)) = SUP (\n.FUNPOW n fun BOT)`--));


(*---------------------------------------------------------------------------
 * c : num -> ('a->bool) is a chain if
 *
 *     c(0) <<< c(1) <<< ... <<< c(n) <<< ...
 *---------------------------------------------------------------------------*)
val CHAINF=new_definition("CHAINF",
               (--`CHAINF (c:num->'a->bool) = !n.(c n) <<< (c(SUC n))`--));


(*---------------------------------------------------------------------------
 * An example of a chain that will be useful to us is:
 *
 *     p1 <<< p2 <<< p2 <<< ... <<< p2 <<< ...
 *---------------------------------------------------------------------------*)
val TRIV_CHAINF =new_definition ("TRIV_CHAINF",
                (--`TRIV_CHAINF p1 p2 :num->'a = \n. (n=0) => p1 | p2`--));


val TRIV_CHAINF_LEMMA = 
store_thm ("TRIV_CHAINF_LEMMA",
(--`!(p1:'a->bool) p2. p1 <<< p2 ==> CHAINF(TRIV_CHAINF p1 p2)`--),
               REPEAT STRIP_TAC
               THEN REWRITE_TAC [CHAINF, TRIV_CHAINF]
               THEN BETA_TAC THEN INDUCT_TAC
               THENL [ASM_REWRITE_TAC[NOT_SUC],
		      REWRITE_TAC[NOT_SUC,LESS_DEF]]);


(*---------------------------------------------------------------------------
 * fun is monotonic (|- MONOTONE fun) if
 *
 *     p1 <<< p2 ==> fun p1 <<< fun p2
 *---------------------------------------------------------------------------*)
val MONOTONE = new_definition("MONOTONE",
	       (--`MONOTONE (fun:('a->bool)->('a->bool)) =
		        !p1 p2. (p1 <<< p2) ==> (fun p1 <<< fun p2)`--));


(*---------------------------------------------------------------------------
 * fun is continuous (|- CONTINUOUSF fun) if for all chains
 *
 *     c0 <<< c1 <<< ... <<< cn <<< ...
 *
 *  we have
 *
 *     fun(U cn) = U (fun cn)
 *         n       n
 *
 *  i.e.
 *
 *     CHAINF c ==> fun(\x.?n. c n x) = \x.?n. fun (c n) x
 *---------------------------------------------------------------------------*)
val CONTINUOUSF = new_definition ("CONTINUOUSF",
(--`CONTINUOUSF (fun:('a->bool)->('a->bool)) =
      !c:num->'a->bool. CHAINF c ==> (fun (SUP c) = SUP(\n.fun(c n)))`--));


val CHAINF_FUNPOW = store_thm ("CHAINF_FUNPOW",
      (--`!fun:('a->bool)->('a->bool).
                    MONOTONE fun ==> CHAINF (\n. FUNPOW n fun BOT)`--),
     REWRITE_TAC[CHAINF,BOT]
     THEN GEN_TAC
     THEN DISCH_TAC
     THEN INDUCT_TAC
     THEN BETA_TAC
     THENL [REWRITE_TAC[FUNPOW,LESS_DEF], ALL_TAC]
     THEN EVERY_ASSUM (UNDISCH_TAC o concl)
     THEN BETA_TAC
     THEN REWRITE_TAC [MONOTONE, FUNPOW]
     THEN REPEAT DISCH_TAC
     THEN RES_TAC);

val EXT_LEMMA = prove
(--`!(f:'a->'b) g. (f = g) = (!x. f x = g x)`--,
	       REPEAT GEN_TAC
               THEN EQ_TAC
               THEN REWRITE_TAC[EQ_EXT]
               THEN DISCH_TAC
               THEN ASM_REWRITE_TAC[]);

val COND_FUN = prove
(--`!p (f:'a->'b) g x. (p => f | g) x = (p => f x | g x)`--,
   REPEAT STRIP_TAC
    THEN ASM_CASES_TAC (--`p:bool`--)
    THEN ASM_REWRITE_TAC[]);

val COND_MP = prove
(--`!p x y.
     (p ==> (p => x | y) ==> x) /\ (~p ==> (p => x | y) ==> y)`--,
   REPEAT GEN_TAC
    THEN ASM_CASES_TAC (--`p:bool`--)
    THEN ASM_REWRITE_TAC[]);

val EXISTS_COND_DISJ = prove
(--`!(n:num) x y. (?n:num. ((n=0) => x | y)) = x \/ y`--,
   REPEAT GEN_TAC
    THEN EQ_TAC
    THEN REPEAT STRIP_TAC
    THENL
     [ASM_CASES_TAC (--`n=0`--)
       THEN IMP_RES_TAC COND_MP
       THEN ASM_REWRITE_TAC[],
      EXISTS_TAC (--`0`--)
       THEN REWRITE_TAC[],
      EXISTS_TAC (--`SUC 0`--)
       THEN REWRITE_TAC[NOT_SUC]]
    THEN ASM_REWRITE_TAC[]);

val EQ_DISJ = prove
(--`!x y. (x \/ y = y) = (x ==> y)`--,
   REPEAT GEN_TAC
    THEN ASM_CASES_TAC (--`x:bool`--)
    THEN ASM_CASES_TAC (--`y:bool`--)
    THEN ASM_REWRITE_TAC[]);

val SUP_CHAINF_LEMMA =
 store_thm
  ("SUP_CHAINF_LEMMA",
   (--`!(p1:'a->bool) p2. (p1 <<< p2) = (SUP(TRIV_CHAINF p1 p2) = p2)`--),
   REPEAT GEN_TAC
    THEN REWRITE_TAC[SUP,LESS_DEF,TRIV_CHAINF,EXT_LEMMA]
    THEN BETA_TAC
    THEN REWRITE_TAC[COND_FUN,EXISTS_COND_DISJ,EQ_DISJ]);

val LAMB_TRIV_CHAINF =
 store_thm
  ("LAMB_TRIV_CHAINF",
  (--`!(fun:('a->bool)->('a->bool)) p1 p2.
      (\n. fun(TRIV_CHAINF p1 p2 n)) = TRIV_CHAINF (fun p1) (fun p2)`--),
   REPEAT GEN_TAC
    THEN ONCE_REWRITE_TAC[EXT_LEMMA]
    THEN REWRITE_TAC[TRIV_CHAINF]
    THEN BETA_TAC
    THEN GEN_TAC
    THEN ASM_CASES_TAC (--`x=0`--)
    THEN ASM_REWRITE_TAC[NOT_SUC]);

val CONT_MONOTONE =
 store_thm
  ("CONT_MONOTONE",
   (--`!fun:('a->bool)->('a->bool). CONTINUOUSF fun ==> MONOTONE fun`--),
   GEN_TAC
    THEN REWRITE_TAC[CONTINUOUSF,MONOTONE]
    THEN REPEAT STRIP_TAC
    THEN IMP_RES_TAC TRIV_CHAINF_LEMMA
    THEN RES_TAC
    THEN ASSUM_LIST
          (fn(thl)=> ASSUME_TAC
                  (REWRITE_RULE
                    [LAMB_TRIV_CHAINF]
                    (hd(mapfilter SYM thl))))
    THEN REWRITE_TAC[SUP_CHAINF_LEMMA]
    THEN ONCE_ASM_REWRITE_TAC[]
    THEN REWRITE_TAC
          [EQ_MP (SPEC_ALL SUP_CHAINF_LEMMA) 
                 (ASSUME (--`(p1:'a->bool)<<<p2`--))]);


(*---------------------------------------------------------------------------
 * Proof that the limit of the iterates is a fixed point.
 *---------------------------------------------------------------------------*)

val FIX_LEMMA =
 store_thm
  ("FIX_LEMMA",
   (--`!fun:('a->bool)->('a->bool).
     CONTINUOUSF fun ==> (fun(LIM_FUNPOW fun) = LIM_FUNPOW fun)`--),
   REWRITE_TAC[LIM_FUNPOW,FUNPOW]
    THEN REPEAT STRIP_TAC
    THEN IMP_RES_TAC CONT_MONOTONE
    THEN IMP_RES_TAC CHAINF_FUNPOW
    THEN ASSUM_LIST (fn thl => ASSUME_TAC
                                  (hd(mapfilter 
                                     (EQ_MP (SPEC_ALL CONTINUOUSF)) thl)))
    THEN RES_TAC
    THEN ASM_REWRITE_TAC[]
    THEN BETA_TAC
    THEN REWRITE_TAC[SYM(SPEC_ALL(CONJUNCT2 FUNPOW))]
    THEN REWRITE_TAC[SUP]
    THEN CONV_TAC FUN_EQ_CONV
    THEN REPEAT STRIP_TAC
    THEN BETA_TAC
    THEN EQ_TAC
    THEN REPEAT STRIP_TAC
    THENL[EXISTS_TAC (--`SUC n`--), EXISTS_TAC (--`n:num`--)]
    THEN ASM_REWRITE_TAC[]
    THEN IMP_RES_THEN
          (ASSUME_TAC o BETA_RULE o SPEC_ALL)
          (fst(EQ_IMP_RULE (SPEC_ALL CHAINF)))
    THEN ASSUM_LIST
          (fn(thl)=> ASSUME_TAC
                  (hd
                   (mapfilter
                    (MATCH_MP (fst(EQ_IMP_RULE (SPEC_ALL LESS_DEF)))) thl)))
    THEN RES_TAC);

(*---------------------------------------------------------------------------
 * Proof that if fun f = f then fun^n f BOT <<< f.
 *---------------------------------------------------------------------------*)

val LEAST_FIX_LEMMA =
 store_thm
  ("LEAST_FIX_LEMMA",
   (--`!fun:('a->bool)->('a->bool).
      CONTINUOUSF fun ==> !f. (fun f = f) ==> !n. FUNPOW n fun BOT <<< f`--),
   REWRITE_TAC[BOT]
    THEN STRIP_TAC THEN STRIP_TAC THEN STRIP_TAC THEN STRIP_TAC
    THEN INDUCT_TAC
    THENL[REWRITE_TAC[FUNPOW,LESS_DEF], ALL_TAC]
    THEN REWRITE_TAC[FUNPOW]
    THEN IMP_RES_TAC CONT_MONOTONE
    THEN ASSUM_LIST(fn(thl)=> ASSUME_TAC(hd(mapfilter 
                                        (EQ_MP (SPEC_ALL MONOTONE)) thl)))
    THEN ASSUM_LIST(fn(thl)=> ONCE_REWRITE_TAC(mapfilter SYM thl))
    THEN RES_TAC);

(*---------------------------------------------------------------------------
 * Proof that the limit of the iterates is the least fixed point.
 *---------------------------------------------------------------------------*)

val LEAST_FIX_THM =
 store_thm
  ("LEAST_FIX_THM",
   (--`!fun:('a->bool)->('a->bool).
      CONTINUOUSF fun ==> !f. (fun f = f) ==> (LIM_FUNPOW fun <<< f)`--),
   REPEAT STRIP_TAC
    THEN REWRITE_TAC[LIM_FUNPOW,SUP,LESS_DEF]
    THEN GEN_TAC
    THEN BETA_TAC
    THEN REPEAT STRIP_TAC
    THEN IMP_RES_THEN (IMP_RES_TAC o REWRITE_RULE[LESS_DEF]) LEAST_FIX_LEMMA);


(*---------------------------------------------------------------------------
 * LIM_FUNPOW fun is the least fixed point of fun.
 *---------------------------------------------------------------------------*)

val LIM_FUNPOW_THM =
 store_thm
  ("LIM_FUNPOW_THM",
   (--`!fun:('a->bool)->('a->bool).
      CONTINUOUSF fun ==>
       ((fun(LIM_FUNPOW fun) = LIM_FUNPOW fun) /\
        !f. (fun f = f) ==> (LIM_FUNPOW fun <<< f))`--),
   REPEAT STRIP_TAC
    THENL
     [IMP_RES_TAC FIX_LEMMA,
      IMP_RES_TAC LEAST_FIX_THM]);


(*---------------------------------------------------------------------------
 * Proof that a least fixed point exists.
 *---------------------------------------------------------------------------*)

val FIX_EXISTS =
 store_thm
  ("FIX_EXISTS",
   (--`!fun:('a->bool)->('a->bool).
      CONTINUOUSF fun ==>
       ?f. (fun f = f) /\ !f'. (fun f' = f') ==> (f <<< f')`--),
   GEN_TAC
    THEN DISCH_TAC
    THEN EXISTS_TAC (--`LIM_FUNPOW (fun:('a->bool)->('a->bool))`--)
    THEN MATCH_MP_TAC LIM_FUNPOW_THM
    THEN FIRST_ASSUM ACCEPT_TAC);


(*---------------------------------------------------------------------------
 * Proof that FIX is the least fixed point.
 *---------------------------------------------------------------------------*)

val FIX_THM =
 store_thm
  ("FIX_THM",
   (--`!fun:('a->bool)->('a->bool).
      CONTINUOUSF fun ==>
       ((fun(FIX fun) = FIX fun) /\
        !f. (fun f = f) ==> (FIX fun <<< f))`--),
   GEN_TAC
    THEN DISCH_TAC
    THEN REWRITE_TAC[FIX]
    THEN IMP_RES_THEN (fn(thl)=> REWRITE_TAC[SELECT_RULE thl]) FIX_EXISTS);;

val ANTISYM_LEMMA =
 store_thm
  ("ANTISYM_LEMMA",
   (--`!(f:'a->bool) (g:'a->bool). (f <<< g) /\ (g <<< f) ==> (f = g)`--),
   REWRITE_TAC[LESS_DEF]
    THEN REPEAT STRIP_TAC
    THEN CONV_TAC FUN_EQ_CONV
    THEN GEN_TAC
    THEN EQ_TAC
    THEN ASM_REWRITE_TAC[]);

val FIX_LIM_FUNPOW_THM =
 store_thm
  ("FIX_LIM_FUNPOW_THM",
   (--`!fun:('a->bool)->('a->bool).
      CONTINUOUSF fun ==> (FIX fun = LIM_FUNPOW fun)`--),
   REPEAT STRIP_TAC
    THEN IMP_RES_THEN ASSUME_TAC FIX_THM
    THEN IMP_RES_TAC LIM_FUNPOW_THM
    THEN RES_TAC
    THEN IMP_RES_TAC ANTISYM_LEMMA);

(*---------------------------------------------------------------------------
 * A predicate p admits induction if:
 *
 *     p x1 /\ p x2 ... /\ p xn /\ ...  ==> p(U xn)
 *                                            n
 *---------------------------------------------------------------------------*)
val ADMITS_INDUCTION =
 new_definition
  ("ADMITS_INDUCTION",
   (--`ADMITS_INDUCTION (p:('a->bool)->bool) =
     !c. CHAINF c /\ (!n. p(c n)) ==> p(SUP c)`--));


(*---------------------------------------------------------------------------
 * If p is a Hoare_logic predicate:
 *
 *     p(f) = !s1 s2. p s1 /\ f(s1,s2) ==> q s2
 *
 *  then p admits induction.
 *---------------------------------------------------------------------------*)

val HOARE_ADMITS_LEMMA =
 store_thm
 ("HOARE_ADMITS_LEMMA",
  (--`!(p:'a->bool) (q : 'a->bool).
    ADMITS_INDUCTION(\f. !s1 s2. p s1 /\ f(s1,s2) ==> q s2)`--),
  REWRITE_TAC[ADMITS_INDUCTION,CHAINF,SUP]
   THEN BETA_TAC
   THEN BETA_TAC
   THEN REPEAT STRIP_TAC
   THEN RES_TAC);

(*---------------------------------------------------------------------------
 * Lemma: if fun is continuous and p BOT and
 *
 *       !f. p f ==> p(fun f), 
 *
 * then p is true of all the iterates fun^n BOT.
 *---------------------------------------------------------------------------*)

val SCOTT_INDUCTION_LEMMA =
 store_thm
  ("SCOTT_INDUCTION_LEMMA",
   (--`!(p:('a->bool)->bool) fun.
     CONTINUOUSF fun /\
     p BOT /\
     (!f. p f ==> p(fun f))
     ==>
     !n. p(FUNPOW n fun BOT)`--),
   REWRITE_TAC[BOT]
    THEN STRIP_TAC
    THEN STRIP_TAC
    THEN STRIP_TAC
    THEN INDUCT_TAC
    THEN REWRITE_TAC[FUNPOW]
    THEN ASM_REWRITE_TAC[]
    THEN RES_TAC);

(*---------------------------------------------------------------------------
 * Scott Induction (Computation Induction)
 *---------------------------------------------------------------------------*)

val SCOTT_INDUCTION_THM =
 store_thm
  ("SCOTT_INDUCTION_THM",
   (--`!(p:('a->bool)->bool) fun.
     ADMITS_INDUCTION p  /\
     CONTINUOUSF fun     /\
     p BOT               /\
     (!f. p f ==> p(fun f))
     ==>
     p(FIX fun)`--),
   REPEAT STRIP_TAC
    THEN IMP_RES_TAC FIX_LIM_FUNPOW_THM
    THEN ASM_REWRITE_TAC[LIM_FUNPOW]
    THEN IMP_RES_TAC SCOTT_INDUCTION_LEMMA
    THEN IMP_RES_TAC CONT_MONOTONE
    THEN IMP_RES_TAC CHAINF_FUNPOW
    THEN IMP_RES_TAC
          (hd(IMP_CANON(fst(EQ_IMP_RULE (SPEC_ALL ADMITS_INDUCTION)))))
    THEN ASSUM_LIST (IMP_RES_TAC o BETA_RULE o (el 1)));;


val _ = export_theory();
