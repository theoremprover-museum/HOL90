val path = 
  (!Globals.HOLdir)^"library/pair/theories/"^SysParams.theory_file_type^"/"

val _ = Lib.clean_directory path;

val _ = theory_path := path::(!theory_path);

new_theory "pair_thms";

use "../../src/syn.sml";
open Pair_syn;
    
use "../../src/basic.sml";
open Pair_basic;
    

val UNCURRY_DEF = definition"pair""UNCURRY_DEF";
val CURRY_DEF = definition"pair""CURRY_DEF";
val PAIR = theorem "pair""PAIR";

(* ------------------------------------------------------------------------- *)
(* CURRY_UNCURRY_THM = |- !f. CURRY(UNCURRY f) = f                           *)
(* ------------------------------------------------------------------------- *)

val CURRY_UNCURRY_THM =
    let val th1 = prove
		(--`CURRY (UNCURRY (f:'a->'b->'c)) x y = f x y`--,
		 REWRITE_TAC [UNCURRY_DEF, CURRY_DEF])
	val th2 = GEN (--`y:'b`--) th1 
	val th3 = EXT th2 
	val th4 = GEN (--`x:'a`--) th3 
	val th4 = EXT th4 
    in
	GEN (--`f:'a->'b->'c`--) th4
    end;
    
    save_thm("CURRY_UNCURRY_THM",CURRY_UNCURRY_THM);
    

(* ------------------------------------------------------------------------- *)
(* UNCURRY_CURRY_THM = |- !f. UNCURRY(CURRY f) = f                           *)
(* ------------------------------------------------------------------------- *)

val UNCURRY_CURRY_THM =
    let val th1 = prove
	(--`UNCURRY (CURRY (f:('a#'b)->'c)) (x,y) = f(x,y)`--,
	 REWRITE_TAC [CURRY_DEF, UNCURRY_DEF]) 
	val th2 = INST [{residue=(--`FST (z:'a#'b)`--),redex=(--`x:'a`--)},
			{residue=(--`SND (z:'a#'b)`--),redex=(--`y:'b`--)}] th1
	val th3 =
	    CONV_RULE (RAND_CONV (RAND_CONV (K (ISPEC(--`z:'a#'b`--) PAIR))))  th2
	val th4 = 
	    CONV_RULE(RATOR_CONV (RAND_CONV 
				  (RAND_CONV (K (ISPEC(--`z:'a#'b`--) PAIR)))))th3 
	val th5 = GEN (--`z:'a#'b`--) th4
	val th6 = EXT th5 
    in
	GEN (--`f:('a#'b)->'c`--) th6
    end;

    save_thm("UNCURRY_CURRY_THM",UNCURRY_CURRY_THM);

(* ------------------------------------------------------------------------- *)
(* CURRY_ONE_ONE_THM = |- (CURRY f = CURRY g) = (f = g)                      *)
(* ------------------------------------------------------------------------- *)
val CURRY_ONE_ONE_THM =
    let val th1 = ASSUME (--`(f:('a#'b)->'c) = g`--)
	val th2 = AP_TERM(--`CURRY:(('a#'b)->'c)->('a->'b->'c)`--) th1 
	val th3 = DISCH_ALL th2 
	val thA = ASSUME (--`(CURRY (f:('a#'b)->'c)) = (CURRY g)`--)
	val thB = AP_TERM (--`UNCURRY:('a->'b->'c)->(('a#'b)->'c)`--) thA 
	val thC = PURE_REWRITE_RULE [UNCURRY_CURRY_THM] thB 
	val thD = DISCH_ALL thC 
    in
	IMP_ANTISYM_RULE thD th3 
    end;

    save_thm("CURRY_ONE_ONE_THM",CURRY_ONE_ONE_THM);
    
(* ------------------------------------------------------------------------- *)
(* UNCURRY_ONE_ONE_THM = |- (UNCURRY f = UNCURRY g) = (f = g)                *)
(* ------------------------------------------------------------------------- *)

val UNCURRY_ONE_ONE_THM =
    let val th1 = ASSUME (--`(f:'a->'b->'c) = g`--) 
	val th2 = AP_TERM (--`UNCURRY:('a->'b->'c)->(('a#'b)->'c)`--) th1 
	val th3 = DISCH_ALL th2 
	val thA = ASSUME (--`(UNCURRY (f:'a->'b->'c)) = (UNCURRY g)`--)
	val thB = AP_TERM (--`CURRY:(('a#'b)->'c)->('a->'b->'c)`--) thA
	val thC = PURE_REWRITE_RULE [CURRY_UNCURRY_THM] thB 
	val thD = DISCH_ALL thC 
    in
	IMP_ANTISYM_RULE thD th3 
    end;

    save_thm("UNCURRY_ONE_ONE_THM",UNCURRY_ONE_ONE_THM);


(* ------------------------------------------------------------------------- *)
(* PFORALL_THM = |- !f. (!x y. f x y) = (!(x,y). f x y)                      *)
(* ------------------------------------------------------------------------- *)

val FST = theorem"pair""FST"
and SND = theorem"pair""SND";
    
val PFORALL_THM =
    prove
    (
	--`!f. (!(x:'a) (y:'b). f x y) = (!(x:'a,(y:'b)). f x y)`--
    ,
	GEN_TAC THEN
	EQ_TAC THENL
	[
	    DISCH_TAC THEN
	    (REWRITE_TAC [FORALL_DEF]) THEN
	    BETA_TAC THEN
	    (ASM_REWRITE_TAC []) THEN
	    (CONV_TAC (RAND_CONV (PALPHA_CONV (--`(x:'a,(y:'b))`--)))) THEN
	    REFL_TAC
	,
	    (CONV_TAC (RATOR_CONV (RAND_CONV (GEN_PALPHA_CONV(--`z:'a#'b`--))))) THEN
	    DISCH_TAC THEN
	    (CONV_TAC (RAND_CONV (ABS_CONV (RAND_CONV (ABS_CONV
		(RATOR_CONV (RAND_CONV (fn tm => (SYM (SPEC_ALL FST)))))))))) THEN
	    (CONV_TAC (RAND_CONV (ABS_CONV (RAND_CONV (ABS_CONV
		(RAND_CONV (fn tm => (SYM (SPEC_ALL SND)))))))))    THEN
	     (ASM_REWRITE_TAC [])
	]
    );

    save_thm("PFORALL_THM",PFORALL_THM);
    
(* ------------------------------------------------------------------------- *)
(* PEXISTS_THM = |- !f. (?x y. f x y) = (?(x,y). f x y)                      *)
(* ------------------------------------------------------------------------- *)

val PEXISTS_THM =
    prove
    (
	--`!f. (?(x:'a) (y:'b). f x y) = (?(x:'a,(y:'b)). f x y)`--
    ,
	GEN_TAC THEN
	EQ_TAC THENL
	[
	    (CONV_TAC LEFT_IMP_EXISTS_CONV) THEN
	    GEN_TAC THEN
	    (CONV_TAC LEFT_IMP_EXISTS_CONV) THEN
	    GEN_TAC THEN
	    DISCH_TAC THEN
	    (CONV_TAC (GEN_PALPHA_CONV (--`a:'a#'b`--))) THEN
	    (EXISTS_TAC (--`(x:'a,(y:'b))`--)) THEN
	    (ASM_REWRITE_TAC [FST, SND]) 
	,
	    (CONV_TAC (RATOR_CONV (RAND_CONV (GEN_PALPHA_CONV (--`a:'a#'b`--))))) THEN
	    (CONV_TAC LEFT_IMP_EXISTS_CONV) THEN
	    GEN_TAC THEN
	    DISCH_TAC THEN
	    (EXISTS_TAC (--`FST (a:'a#'b)`--)) THEN
	    (EXISTS_TAC (--`SND (a:'a#'b)`--)) THEN
	    (ASM_REWRITE_TAC [])
	]
    );

    save_thm("PEXISTS_THM",PEXISTS_THM);
    

(* ------------------------------------------------------------------------- *)
(* NOT_FORALL_THM = |- !f. ~(!x. f x) = (?x. ~f x)                   	    *)
(* ------------------------------------------------------------------------- *)

val NOT_FORALL_THM =
    let val f = (--`f:'a->bool`--)
	val x = (--`x:'a`--)
	val t = mk_comb{Rator=f,Rand=x} 
	val all = mk_forall{Bvar=x,Body=t}
	and exists = mk_exists{Bvar=x,Body=mk_neg t}
	val nott = ASSUME (mk_neg t) 
	val th1 = DISCH all (MP nott (SPEC x (ASSUME all))) 
	val imp1 = DISCH exists (CHOOSE (x, ASSUME exists) (NOT_INTRO th1)) 
	val th2 =
	    CCONTR t (MP (ASSUME(mk_neg exists)) (EXISTS(exists,x)nott)) 
	val th3 = CCONTR exists (MP (ASSUME (mk_neg all)) (GEN x th2)) 
	val imp2 = DISCH (mk_neg all) th3 
    in
	GEN f (IMP_ANTISYM_RULE imp2 imp1)
    end;

    save_thm("NOT_FORALL_THM",NOT_FORALL_THM);
    

(* ------------------------------------------------------------------------- *)
(* NOT_EXISTS_THM = |- !f. ~(?x. f x) = (!x. ~f x)                   	    *)
(* ------------------------------------------------------------------------- *)

val NOT_EXISTS_THM =
    let val f = (--`f:'a->bool`--) 
	val x = (--`x:'a`--) 
	val t = mk_comb{Rator=f,Rand=x} 
	val tm = mk_neg(mk_exists{Bvar=x,Body=t}) 
	val all = mk_forall{Bvar=x,Body=mk_neg t} 
	val asm1 = ASSUME t 
	val thm1 = MP (ASSUME tm) (EXISTS (rand tm, x) asm1) 
	val imp1 = DISCH tm (GEN x (NOT_INTRO (DISCH t thm1))) 
	val asm2 = ASSUME  all and asm3 = ASSUME (rand tm) 
	val thm2 = DISCH (rand tm) (CHOOSE (x,asm3) (MP (SPEC x asm2) asm1)) 
	val imp2 = DISCH all (NOT_INTRO thm2) 
    in
	GEN f (IMP_ANTISYM_RULE imp1 imp2)
    end;

    save_thm("NOT_EXISTS_THM",NOT_EXISTS_THM);
    

(* ------------------------------------------------------------------------- *)
(* FORALL_AND_THM |- !f g. (!x. f x /\ g x) = ((!x. f x) /\ (!x. g x))       *)
(* ------------------------------------------------------------------------- *)

val FORALL_AND_THM =
    let val f = (--`f:'a->bool`--)
	val g = (--`g:'a->bool`--)
	val x = (--`x:'a`--)
	val th1 = ASSUME (--`!x:'a. (f x) /\ (g x)`--)
	val imp1 =
	    (uncurry CONJ) (((GEN x) ## (GEN x)) (CONJ_PAIR (SPEC x th1))) 
	val th2 = ASSUME (--`(!x:'a. f x) /\ (!x:'a. g x)`--)
	val imp2 =
	    GEN x ((uncurry CONJ) (((SPEC x) ## (SPEC x)) (CONJ_PAIR th2)))
    in
	    GENL [f,g] (IMP_ANTISYM_RULE (DISCH_ALL imp1) (DISCH_ALL imp2))
    end;
    
    save_thm("FORALL_AND_THM",FORALL_AND_THM);
    

(* ------------------------------------------------------------------------- *)
(* EXISTS_OR_THM |- !f g. (?x. f x \/ g x) = ((?x. f x) \/ (?x. g x))        *)
(* ------------------------------------------------------------------------- *)

val EXISTS_OR_THM =
    let val f = (--`f:'a->bool`--)
	val g = (--`g:'a->bool`--)
	val x = (--`x:'a`--)
	val P = mk_comb{Rator=f,Rand=x}
	val Q = mk_comb{Rator=g,Rand=x}
	val tm = mk_pexists {Bvar=x,Body=mk_disj{disj1=P,disj2=Q}} 
	val ep = mk_exists{Bvar=x,Body=P}
	and eq = mk_exists{Bvar=x,Body=Q}
	val Pth = EXISTS(ep,x)(ASSUME P)
	and Qth = EXISTS(eq,x)(ASSUME Q)
	val thm1 = DISJ_CASES_UNION (ASSUME(mk_disj{disj1=P,disj2=Q})) Pth Qth
	val imp1 = DISCH tm (CHOOSE (x,ASSUME tm) thm1)
	val t1 = DISJ1 (ASSUME P) Q and t2 = DISJ2 P (ASSUME Q)
	val th1 = EXISTS(tm,x) t1 and th2 = EXISTS(tm,x) t2
	val e1 = CHOOSE (x,ASSUME ep) th1 and e2 = CHOOSE (x,ASSUME eq) th2
	val thm2 = DISJ_CASES (ASSUME(mk_disj{disj1=ep,disj2=eq})) e1 e2
	val imp2 = DISCH (mk_disj{disj1=ep,disj2=eq}) thm2 
    in
	GENL [f,g] (IMP_ANTISYM_RULE imp1 imp2)
    end;

    save_thm("EXISTS_OR_THM",EXISTS_OR_THM);
    

(* ------------------------------------------------------------------------- *)
(* LEFT_AND_FORALL_THM = |- !f Q. (!x. f x) /\ Q = (!x. f x /\ Q)            *)
(* ------------------------------------------------------------------------- *)

val LEFT_AND_FORALL_THM =
    let val x = (--`x:'a`--) 
	val f = (--`f:'a->bool`--) 
	val Q = (--`Q:bool`--) 
	val th1 = ASSUME (--`(!x:'a. f x) /\ Q`--) 
	val imp1 = GEN x ((uncurry CONJ) ((SPEC x ## I) (CONJ_PAIR th1))) 
	val th2 = ASSUME (--`!x:'a. f x /\ Q`--) 
	val imp2 = (uncurry CONJ) ((GEN x ## I) (CONJ_PAIR (SPEC x th2)))
    in
	GENL [Q,f] (IMP_ANTISYM_RULE (DISCH_ALL imp1) (DISCH_ALL imp2))
    end;

    save_thm("LEFT_AND_FORALL_THM",LEFT_AND_FORALL_THM);
    

(* ------------------------------------------------------------------------- *)
(* RIGHT_AND_FORALL_THM = |- !P g. P /\ (!x. g x) = (!x. P /\ g x)           *)
(* ------------------------------------------------------------------------- *)

val RIGHT_AND_FORALL_THM =
    let	val x = (--`x:'a`--) 
	val P = (--`P:bool`--) 
	val g = (--`g:'a->bool`--) 
	val th1 = ASSUME (--`P /\ (!x:'a. g x)`--) 
	val imp1 = GEN x ((uncurry CONJ) ((I ## SPEC x) (CONJ_PAIR th1))) 
	val th2 = ASSUME (--`!x:'a. P /\ g x`--) 
	val imp2 = (uncurry CONJ) ((I ## GEN x) (CONJ_PAIR (SPEC x th2))) 
    in
	GENL [P,g] (IMP_ANTISYM_RULE (DISCH_ALL imp1) (DISCH_ALL imp2))
    end;

    save_thm("RIGHT_AND_FORALL_THM",RIGHT_AND_FORALL_THM);
    

(* ------------------------------------------------------------------------- *)
(* LEFT_OR_EXISTS_THM = |- (?x. f x) \/ Q = (?x. f x \/ Q)                   *)
(* ------------------------------------------------------------------------- *)

val LEFT_OR_EXISTS_THM =
    let val x = (--`x:'a`--)
	val Q = (--`Q:bool`--)
	val f = (--`f:'a->bool`--)
	val P = mk_comb{Rator=f,Rand=x}
	val ep = mk_exists{Bvar=x,Body=P}
	val tm = mk_disj{disj1=ep,disj2=Q}
	val otm = mk_exists{Bvar=x,Body=mk_disj{disj1=P,disj2=Q}}
	val t1 = DISJ1 (ASSUME P) Q and t2 = DISJ2 P (ASSUME Q)
	val th1 = EXISTS(otm,x) t1 and th2 = EXISTS(otm,x) t2 
	val thm1 = DISJ_CASES (ASSUME tm) (CHOOSE(x,ASSUME ep)th1) th2
	val imp1 = DISCH tm thm1
	val Pth = EXISTS(ep,x)(ASSUME P) and Qth = ASSUME Q
	val thm2 = DISJ_CASES_UNION (ASSUME(mk_disj{disj1=P,disj2=Q})) Pth Qth 
	val imp2 = DISCH otm (CHOOSE (x,ASSUME otm) thm2) 
    in
	GENL [Q,f] (IMP_ANTISYM_RULE imp1 imp2)
    end;

    save_thm("LEFT_OR_EXISTS_THM",LEFT_OR_EXISTS_THM);
    

(* ------------------------------------------------------------------------- *)
(* RIGHT_OR_EXISTS_THM = |- P \/ (?x. g x) = (?x. P \/ g x)                  *)
(* ------------------------------------------------------------------------- *)

val RIGHT_OR_EXISTS_THM =
    let	val x = (--`x:'a`--)
	val P = (--`P:bool`--)
	val g = (--`g:'a->bool`--)
	val Q = mk_comb{Rator=g,Rand=x}
	val eq = mk_exists{Bvar=x,Body=Q}
	val tm = mk_disj{disj1=P,disj2=eq}
	val otm = mk_exists{Bvar=x,Body=mk_disj{disj1=P,disj2=Q}}
	val t1 = DISJ1 (ASSUME P) Q and t2 = DISJ2 P (ASSUME Q) 
	val th1 = EXISTS(otm,x) t1 and th2 = EXISTS(otm,x) t2 
	val thm1 = DISJ_CASES (ASSUME tm) th1 (CHOOSE(x,ASSUME eq)th2) 
	val imp1 = DISCH tm thm1 
	val Qth = EXISTS(eq,x)(ASSUME Q) and Pth = ASSUME P 
	val thm2 = DISJ_CASES_UNION (ASSUME(mk_disj{disj1=P,disj2=Q})) Pth Qth
	val imp2 = DISCH otm (CHOOSE (x,ASSUME otm)  thm2)
    in
	    GENL [P,g] (IMP_ANTISYM_RULE imp1 imp2)
    end;

    save_thm("RIGHT_OR_EXISTS_THM",RIGHT_OR_EXISTS_THM);
    
	
(* ------------------------------------------------------------------------- *)
(* BOTH_EXISTS_AND_THM = |- !P Q. (?x. P /\ Q) = (?x. P) /\ (?x. Q)          *)
(* ------------------------------------------------------------------------- *)

val BOTH_EXISTS_AND_THM =
    let	val x = (--`x:'a`--) 
	val P = (--`P:bool`--) 
	val Q = (--`Q:bool`--) 
	val t = mk_conj{conj1=P,conj2=Q} 
	val exi = mk_exists{Bvar=x,Body=t}
	val (t1,t2) = CONJ_PAIR (ASSUME t)
	val t11 = EXISTS ((mk_exists{Bvar=x,Body=P}),x) t1
	val t21 = EXISTS ((mk_exists{Bvar=x,Body=Q}),x) t2 
	val imp1 =
	    DISCH_ALL
		(CHOOSE (x, ASSUME (mk_exists{Bvar=x,Body=mk_conj{conj1=P,conj2=Q}}))
		 (CONJ t11 t21))
	val th21 = EXISTS (exi,x) (CONJ (ASSUME P) (ASSUME Q)) 
	val th22 = CHOOSE(x,ASSUME(mk_exists{Bvar=x,Body=P})) th21 
	val th23 = CHOOSE(x,ASSUME(mk_exists{Bvar=x,Body=Q})) th22 
	val (u1,u2) =
	    CONJ_PAIR (ASSUME (mk_conj{conj1=mk_exists{Bvar=x,Body=P},
				       conj2=mk_exists{Bvar=x,Body=Q}}))
	val th24 = PROVE_HYP u1 (PROVE_HYP u2 th23)
	val imp2 = DISCH_ALL th24 
    in
	GENL [P,Q] (IMP_ANTISYM_RULE imp1 imp2)
    end;

    save_thm("BOTH_EXISTS_AND_THM",BOTH_EXISTS_AND_THM);
    
(* ------------------------------------------------------------------------- *)
(* LEFT_EXISTS_AND_THM = |- !Q f. (?x. f x /\ Q) = (?x. f x) /\ Q            *)
(* ------------------------------------------------------------------------- *)

val LEFT_EXISTS_AND_THM =
    let val x = (--`x:'a`--)
	val f = (--`f:'a->bool`--)
	val P = mk_comb{Rator=f,Rand=x}
	val Q = (--`Q:bool`--)
	val t = mk_conj{conj1=P,conj2=Q}
	val exi = mk_exists{Bvar=x,Body=t}
	val (t1,t2) = CONJ_PAIR (ASSUME t)
	val t11 = EXISTS ((mk_exists{Bvar=x,Body=P}),x) t1
	val imp1 =
	    DISCH_ALL
		(CHOOSE
		 (x, ASSUME (mk_exists{Bvar=x,Body=mk_conj{conj1=P,conj2=Q}}))
		    (CONJ t11 t2)) 
	val th21 = EXISTS (exi,x) (CONJ (ASSUME P) (ASSUME Q)) 
	val th22 = CHOOSE(x,ASSUME(mk_exists{Bvar=x,Body=P})) th21 
	val (u1,u2) = CONJ_PAIR (ASSUME (mk_conj{conj1=mk_exists{Bvar=x,Body=P},
						 conj2=Q}))
	val th23 = PROVE_HYP u1 (PROVE_HYP u2 th22) 
	val imp2 = DISCH_ALL th23
    in
	GENL [Q,f] (IMP_ANTISYM_RULE imp1 imp2)
    end ;

save_thm("LEFT_EXISTS_AND_THM",LEFT_EXISTS_AND_THM);

(* ------------------------------------------------------------------------- *)
(* RIGHT_EXISTS_AND_THM = |- !P g. (?x. P /\ g x) = P /\ (?x. g x)           *)
(* ------------------------------------------------------------------------- *)

val RIGHT_EXISTS_AND_THM =
    let	val x = (--`x:'a`--) 
	val P = (--`P:bool`--) 
	val g = (--`g:'a->bool`--) 
	val Q = mk_comb{Rator=g,Rand=x} 
	val t = mk_conj{conj1=P,conj2=Q} 
	val exi = mk_exists{Bvar=x,Body=t} 
	val (t1,t2) = CONJ_PAIR (ASSUME t) 
	val t21 = EXISTS ((mk_exists{Bvar=x,Body=Q}),x) t2 
	val imp1 =
	    DISCH_ALL
		(CHOOSE
		 (x, ASSUME (mk_exists{Bvar=x,Body=mk_conj{conj1=P,conj2=Q}}))
		 (CONJ t1 t21)) 
	val th21 = EXISTS (exi,x) (CONJ (ASSUME P) (ASSUME Q)) 
	val th22 = CHOOSE(x,ASSUME(mk_exists{Bvar=x,Body=Q})) th21
	val (u1,u2) = CONJ_PAIR (ASSUME (mk_conj{conj1=P,
						 conj2=mk_exists{Bvar=x,Body=Q}}))
	val th23 = PROVE_HYP u1 (PROVE_HYP u2 th22) 
	val imp2 = DISCH_ALL th23 
    in
	GENL [P,g] (IMP_ANTISYM_RULE imp1 imp2)
    end;

    save_thm("RIGHT_EXISTS_AND_THM",RIGHT_EXISTS_AND_THM);
    

(* ------------------------------------------------------------------------- *)
(* BOTH_FORALL_OR_THM = |- !P Q. (!x. P \/ Q) = (!x. P) \/ (!x. Q)           *)
(* ------------------------------------------------------------------------- *)

val BOTH_FORALL_OR_THM =
    let val x = (--`x:'a`--) 
	val P = (--`P:bool`--) 
	val Q = (--`Q:bool`--) 
	val imp11 = DISCH_ALL (SPEC x (ASSUME (mk_forall{Bvar=x,Body=P})))
	val imp12 = DISCH_ALL (GEN x (ASSUME P)) 
	val fath = IMP_ANTISYM_RULE imp11 imp12 
	val th1 = REFL (mk_forall{Bvar=x, Body=mk_disj{disj1=P,disj2=Q}}) 
	val th2 =
	    CONV_RULE (RAND_CONV (K (INST [{residue=mk_disj{disj1=P,disj2=Q},
					    redex=P}] fath))) th1
	val th3 =
	    CONV_RULE (RAND_CONV (RATOR_CONV (RAND_CONV (K (SYM fath))))) th2 
	val th4 =
	    CONV_RULE (RAND_CONV (RAND_CONV (K 
				   (SYM (INST [{residue=Q,redex=P}] fath))))) th3 
    in
	GENL [P,Q] th4 
    end;

    save_thm("BOTH_FORALL_OR_THM",BOTH_FORALL_OR_THM);
    
(* ------------------------------------------------------------------------- *)
(* LEFT_FORALL_OR_THM = |- !Q f. (!x. f x \/ Q) = (!x. f x) \/ Q             *)
(* ------------------------------------------------------------------------- *)

val LEFT_FORALL_OR_THM =
    let	val x = (--`x:'a`--) 
	val f = (--`f:'a->bool`--) 
	val P = mk_comb{Rator=f,Rand=x} 
	val Q = (--`Q:bool`--) 
	val tm = (mk_forall{Bvar=x,Body=mk_disj{disj1=P,disj2=Q}}) 
	val thm1 = SPEC x (ASSUME tm) 
	val thm2 = CONTR P (MP (ASSUME (mk_neg Q)) (ASSUME Q)) 
	val thm3 = DISJ1 (GEN x (DISJ_CASES thm1 (ASSUME P) thm2)) Q 
	val thm4 = DISJ2 (mk_forall{Bvar=x,Body=P}) (ASSUME Q)
	val imp1 = DISCH tm (DISJ_CASES (SPEC Q EXCLUDED_MIDDLE) thm4 thm3) 
	val thm5 = SPEC x (ASSUME (mk_forall{Bvar=x,Body=P}))
	val thm6 = ASSUME Q 
	val imp2 =
	    (DISCH_ALL (GEN x (DISJ_CASES_UNION
				 (ASSUME (mk_disj{disj1=mk_forall{Bvar=x,Body=P},
						  disj2=Q}))
				 thm5
				 thm6)))
    in
	GENL [Q,f] (IMP_ANTISYM_RULE imp1 imp2)
    end;

    save_thm("LEFT_FORALL_OR_THM",LEFT_FORALL_OR_THM);
    
(* ------------------------------------------------------------------------- *)
(* RIGHT_FORALL_OR_THM = |- !P g. (!x. P \/ g x) = P \/ (!x. g x)            *)
(* ------------------------------------------------------------------------- *)

val RIGHT_FORALL_OR_THM =
    let	val x = (--`x:'a`--) 
	val P = (--`P:bool`--) 
	val g = (--`g:'a->bool`--) 
	val Q = mk_comb{Rator=g,Rand=x} 
	val tm = (mk_forall{Bvar=x,Body=mk_disj{disj1=P,disj2=Q}}) 
	val thm1 = SPEC x (ASSUME tm) 
	val thm2 = CONTR Q (MP (ASSUME (mk_neg P)) (ASSUME P)) 
	val thm3 = DISJ2 P (GEN x (DISJ_CASES thm1 thm2 (ASSUME Q))) 
	val thm4 = DISJ1 (ASSUME P) (mk_forall{Bvar=x,Body=Q})
	val imp1 = DISCH tm (DISJ_CASES (SPEC P EXCLUDED_MIDDLE) thm4 thm3) 
	val thm5 = ASSUME P 
	val thm6 = SPEC x (ASSUME (mk_forall{Bvar=x,Body=Q}))
	val imp2 =
	    (DISCH_ALL (GEN x (DISJ_CASES_UNION
				 (ASSUME (mk_disj{disj1=P,
						  disj2=mk_forall{Bvar=x,Body=Q}}))
				 thm5
				 thm6)))
    in
	    GENL [P,g] (IMP_ANTISYM_RULE imp1 imp2)
    end;

    save_thm("RIGHT_FORALL_OR_THM",RIGHT_FORALL_OR_THM);
    

(* ------------------------------------------------------------------------- *)
(* BOTH_FORALL_IMP_THM = |- (!x. P ==> Q) = ((?x.P) ==> (!x.Q))              *)
(* ------------------------------------------------------------------------- *)

val BOTH_FORALL_IMP_THM =
    let val x = (--`x:'a`--)
	val P = (--`P:bool`--) 
	val Q = (--`Q:bool`--) 
	val tm = mk_forall{Bvar=x, Body=mk_imp{ant=P,conseq= Q}}
	val asm = mk_exists{Bvar=x,Body=P} 
	val th1 = GEN x (CHOOSE(x,ASSUME asm)(UNDISCH(SPEC x (ASSUME tm)))) 
	val imp1 = DISCH tm (DISCH asm th1) 
	val cncl = rand(concl imp1) 
	val th2 = SPEC x (MP (ASSUME cncl) (EXISTS (asm,x) (ASSUME P))) 
	val imp2 = DISCH cncl (GEN x (DISCH P th2)) 
    in
	GENL [P,Q] (IMP_ANTISYM_RULE imp1 imp2) 
    end;

    save_thm("BOTH_FORALL_IMP_THM",BOTH_FORALL_IMP_THM);
    

(* ------------------------------------------------------------------------- *)
(* LEFT_FORALL_IMP_THM = |- (!x. P[x]==>Q) = ((?x.P[x]) ==> Q)               *)
(* ------------------------------------------------------------------------- *)

val LEFT_FORALL_IMP_THM =
    let	val x = (--`x:'a`--) 
	val f = (--`f:'a->bool`--) 
	val P = mk_comb{Rator=f,Rand=x} 
	val Q = (--`Q:bool`--) 
	val tm = mk_forall{Bvar=x, Body= mk_imp {ant=P,conseq=Q}} 
	val asm = mk_exists{Bvar=x,Body=P} 
	val th1 = CHOOSE(x,ASSUME asm)(UNDISCH(SPEC x (ASSUME tm))) 
	val imp1 = DISCH tm (DISCH asm th1) 
	val cncl = rand(concl imp1) 
	val th2 = MP (ASSUME cncl) (EXISTS (asm,x) (ASSUME P)) 
	val imp2 = DISCH cncl (GEN x (DISCH P th2)) 
    in
	GENL [Q,f] (IMP_ANTISYM_RULE imp1 imp2) 
    end;

    save_thm("LEFT_FORALL_IMP_THM",LEFT_FORALL_IMP_THM);
    
(* ------------------------------------------------------------------------- *)
(* RIGHT_FORALL_IMP_THM = |- (!x. P==>Q[x]) = (P ==> (!x.Q[x]))              *)
(* ------------------------------------------------------------------------- *)

val RIGHT_FORALL_IMP_THM =
    let val x = (--`x:'a`--) 
	val P = (--`P:bool`--) 
	val g = (--`g:'a->bool`--) 
	val Q = mk_comb{Rator=g,Rand=x} 
	val tm = mk_forall{Bvar=x, Body=mk_imp{ant=P,conseq=Q}} 
	val imp1 = DISCH P(GEN x(UNDISCH(SPEC x(ASSUME tm)))) 
	val cncl = concl imp1 
	val imp2 = GEN x (DISCH P(SPEC x(UNDISCH (ASSUME cncl)))) 
    in
	GENL [P,g] (IMP_ANTISYM_RULE (DISCH tm imp1) (DISCH cncl imp2)) 
    end;

    save_thm("RIGHT_FORALL_IMP_THM",RIGHT_FORALL_IMP_THM);
    

(* ------------------------------------------------------------------------- *)
(* BOTH_EXISTS_IMP_THM = |- (?x. P ==> Q) = ((!x.P) ==> (?x.Q))              *)
(* ------------------------------------------------------------------------- *)

val BOTH_EXISTS_IMP_THM =
    let val x = (--`x:'a`--) 
	val P = (--`P:bool`--) 
	val Q = (--`Q:bool`--) 
	val tm = mk_exists{Bvar=x,Body=mk_imp{ant=P,conseq=Q}} 
	val eQ = mk_exists{Bvar=x,Body=Q} 
	val aP = mk_forall{Bvar=x,Body=P} 
	val thm1 = EXISTS(eQ,x)(UNDISCH(ASSUME(mk_imp{ant=P,conseq=Q}))) 
	val thm2 = DISCH aP (PROVE_HYP (SPEC x (ASSUME aP)) thm1) 
	val imp1 = DISCH tm (CHOOSE(x,ASSUME tm) thm2) 
	val thm2 = CHOOSE(x,UNDISCH (ASSUME (rand(concl imp1)))) (ASSUME Q)
	val thm3 = DISCH P (PROVE_HYP (GEN x (ASSUME P)) thm2) 
	val imp2 = DISCH (rand(concl imp1)) (EXISTS(tm,x) thm3)
    in
	GENL [P,Q] (IMP_ANTISYM_RULE imp1 imp2)
    end;

    save_thm("BOTH_EXISTS_IMP_THM",BOTH_EXISTS_IMP_THM);
    

(* ------------------------------------------------------------------------- *)
(* LEFT_EXISTS_IMP_THM = |- (?x. P[x] ==> Q) = ((!x.P[x]) ==> Q)             *)
(* ------------------------------------------------------------------------- *)

val LEFT_EXISTS_IMP_THM =
    let	val x = (--`x:'a`--) 
	val f = (--`f:'a->bool`--) 
	val P = mk_comb{Rator=f,Rand=x} 
	val Q = (--`Q:bool`--) 
	val tm = mk_exists{Bvar=x, Body= mk_imp{ant=P,conseq=Q}} 
	val allp = mk_forall{Bvar=x,Body=P} 
	val th1 = SPEC x (ASSUME allp) 
	val thm1 = MP (ASSUME(mk_imp{ant=P,conseq=Q})) th1 
	val imp1 = DISCH tm (CHOOSE(x,ASSUME tm)(DISCH allp thm1)) 
	val otm = rand(concl imp1) 
	val thm2 = EXISTS(tm,x)(DISCH P (UNDISCH(ASSUME otm))) 
	val nex =  mk_exists{Bvar=x,Body=mk_neg P} 
	val asm1 = EXISTS (nex, x) (ASSUME (mk_neg P)) 
	val th2 = CCONTR P (MP (ASSUME (mk_neg nex)) asm1) 
	val th3 = CCONTR nex (MP (ASSUME (mk_neg allp)) (GEN x th2)) 
	val thm4 = DISCH P (CONTR Q (UNDISCH (ASSUME (mk_neg P)))) 
	val thm5 = CHOOSE(x,th3)(EXISTS(tm,x)thm4) 
	val thm6 = DISJ_CASES (SPEC allp EXCLUDED_MIDDLE) thm2 thm5 
	val imp2 = DISCH otm thm6 
    in
	GENL [Q, f] (IMP_ANTISYM_RULE imp1 imp2) 
    end;

    save_thm("LEFT_EXISTS_IMP_THM",LEFT_EXISTS_IMP_THM);
    

(* ------------------------------------------------------------------------- *)
(* RIGHT_EXISTS_IMP_THM = |- (?x. P ==> Q[x]) = (P ==> (?x.Q[x]))            *)
(* ------------------------------------------------------------------------- *)

val RIGHT_EXISTS_IMP_THM =
    let	val x = (--`x:'a`--) 
	val P = (--`P:bool`--) 
	val g = (--`g:'a->bool`--) 
	val Q = mk_comb{Rator=g,Rand=x} 
	val tm = mk_exists{Bvar=x,Body=mk_imp{ant=P,conseq=Q}} 
	val thm1 = EXISTS (mk_exists{Bvar=x,Body=Q},x)
	                   (UNDISCH(ASSUME(mk_imp{ant=P,conseq=Q})))
	val imp1 = DISCH tm (CHOOSE(x,ASSUME tm) (DISCH P thm1)) 
	val thm2 = UNDISCH (ASSUME (rand(concl imp1))) 
	val thm3 = CHOOSE (x,thm2) (EXISTS (tm,x) (DISCH P (ASSUME Q))) 
	val thm4 = EXISTS(tm,x)(DISCH P(CONTR Q(UNDISCH(ASSUME(mk_neg P))))) 
	val thm5 = DISJ_CASES (SPEC P EXCLUDED_MIDDLE) thm3 thm4 
	val imp2 = (DISCH(rand(concl imp1)) thm5) 
    in
	GENL [P,g] (IMP_ANTISYM_RULE imp1 imp2)
    end;

    save_thm("RIGHT_EXISTS_IMP_THM",RIGHT_EXISTS_IMP_THM);
    
close_theory();
export_theory();