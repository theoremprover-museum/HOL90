(*--------------------------------------------------------------------------
 * Extensional/Classical Reasoning
 *--------------------------------------------------------------------------*)

structure Classical : Classical_sig = 
struct

open Lib Type Term Thm Parse Equal Drule min bool Rewrite Resolve Tactic
open Tactics Theorems 
infix |-> ## -->;
infix THEN THENL ORELSE THENC
structure Equal = Equal

val _ = say "Developing classical/extensional higher order logic...";

val ERR = STRUCT_ERR "Classical";
val WRAP_ERR = STRUCT_WRAP "Classical";

val ETA_AX = new_axiom `!t:'a->'b. (\x. t x) = t`;

val aty = `:'a`;
val bty = `:'b`;

val ETA_CONV =
    let val t = `t:'a->'b` 
	val pth = dprove(`(\x. (t:'a->'b) x) = t`,fn () => MATCH_ACCEPT_TAC ETA_AX)  
    in fn tm =>
	let val (bv,bod) = dest_abs tm 
	    val (l,r) = dest_comb bod 
	in if r = bv andalso not (vfree_in bv l) then
	    PINST [aty |-> type_of bv, bty |-> type_of bod] [t |-> l] pth
	   else fail()
	end
    handle Fail _ => failwith "ETA_CONV"
    end;

val EQ_EXT = dprove
 (`!(f:'a->'b) g. (!x. f x = g x) ==> (f = g)`, fn () => 
  REPEAT GEN_TAC THEN 
  DISCH_THEN(MP_TAC o ABS `x:'a` o SPEC `x:'a`) THEN
  CONV_TAC(ONCE_DEPTH_CONV ETA_CONV) THEN DISCH_THEN ACCEPT_TAC);

val FUN_EQ_THM = dprove
 (`!(f:'a->'b) g.  (f = g) = (!x. f x = g x)`, fn () => 
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [DISCH_THEN SUBST1_TAC THEN GEN_TAC THEN REFL_TAC,
    MATCH_ACCEPT_TAC EQ_EXT]);

val EXT =
  let val f = `f:'a->'b` and g = `g:'a->'b`
      val pth = dprove
	  (`(!x. (f:'a->'b) x = g x) ==> (f = g)`, fn () => 
	      MATCH_ACCEPT_TAC EQ_EXT)
  in fn th =>
      let val (x,bod) = dest_forall(concl th)
	  val (l,r) = dest_eq bod
	  val (l',r') = (rator l, rator r)
	  val th1 = PINST [aty |-> type_of x, bty |-> type_of l] 
	      [f |-> l', g |-> r'] pth
      in MP th1 th
      end
    handle Fail _ => failwith "EXT"
  end;


(* ------------------------------------------------------------------------- *)
(* Indefinite descriptor (giving AC).                                        *)
(* ------------------------------------------------------------------------- *)

val select_cid = gen_constant `:('a->bool)->'a`;
val _ = parse_as_constant ("@",select_cid);

val _ = parse_as_binder "@";

(*--------------------------------------------------------------------------
 * Constructors/Destructors/Discriminators for @
 *--------------------------------------------------------------------------*)

fun mk_select(v,b) =
   let val ty = type_of v
       val select_tm = prim_mk_const(select_cid,[aty |-> ty]) 
   in mk_comb(select_tm,mk_abs (v,b))
   end
   handle Fail _ => ERR("mk_select", "incorrect type");

fun dest_select tm = 
    let val (s,tm') = dest_comb tm
    in if name_of_const s = select_cid then dest_abs tm' else raise Fail ""
    end handle Fail _ => ERR("dest_select","");

val is_select = can dest_select;

val SELECT_AX = new_axiom
 `!P (x:'a). P x ==> P($@ P)`;

(* ------------------------------------------------------------------------- *)
(* Useful for compatibility. (The old EXISTS_DEF.)                           *)
(* ------------------------------------------------------------------------- *)

val EXISTS_THM = dprove
 (`$? = \P:'a->bool. P ($@ P)`, fn () => 
  MATCH_MP_TAC EQ_EXT THEN BETA_TAC THEN X_GEN_TAC `P:'a->bool` THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM ETA_AX] THEN
  EQ_TAC THENL
   [DISCH_THEN(CHOOSE_THEN MP_TAC) THEN MATCH_ACCEPT_TAC SELECT_AX,
    DISCH_TAC THEN EXISTS_TAC `$@ P :'a` THEN POP_ASSUM ACCEPT_TAC]);

(* ------------------------------------------------------------------------- *)
(* Rules and so on for the select operator.                                  *)
(* ------------------------------------------------------------------------- *)

val SELECT_INTRO =
    let val P = `P:'a->bool` and x = `x:'a`
	val pth = lazy(fn () => SPECL [P, x] SELECT_AX) ()
    in fn th =>
	let val (f,arg) = dest_comb(concl th)
	in MP (PINST [aty |-> type_of x] [P |-> f, x |-> arg] (eval pth)) th
	end
    handle Fail _ => failwith "SELECT_INTRO"
    end;

val SELECT_RULE =
    let val P = `P:'a->bool` and x = `x:'a` 
	val pth = dprove
	    (`$? (P:'a->bool) ==> P($@ P)`, fn () => 
		DISCH_TAC THEN MATCH_MP_TAC SELECT_AX THEN
		CONV_TAC(ONCE_DEPTH_CONV ETA_CONV) THEN
		POP_ASSUM ACCEPT_TAC)
    in fn th =>
	let val abs = rand(concl th)
	    val ty = type_of(bvar abs)
	in CONV_RULE BETA_CONV (MP (PINST [aty |-> ty] [P |-> abs] pth) th)
	end
    handle Fail _ => failwith "SELECT_RULE"
    end;

fun SELECT_ELIM th1 (v,th2) =
    let val (P, SP) = dest_comb(concl th1)
	val th3 = DISCH (mk_comb(P,v)) th2
    in MP (INST [v |-> SP] th3) th1
    end
  handle Fail _ => failwith "SELECT_ELIM";

val SELECT_CONV =
    let val P = `P:'a->bool`
	val pth = dprove
	    (`P($@ P :'a) = $? P`, fn () => 
	     REWRITE_TAC[EXISTS_THM] THEN BETA_TAC THEN REFL_TAC)
    in fn tm =>
	let fun is_epsok t = is_select t andalso
	    let val (bv,bod) = dest_select t
	    in aconv tm (subst [bv |-> t] bod)
	    end
	    val pickeps = find_term is_epsok tm
	    val abs = rand pickeps
	    val ty = type_of (bvar abs)
	in CONV_RULE (LAND_CONV BETA_CONV) (PINST [aty |-> ty] [P |-> abs] pth)
	end
     handle Fail _ => failwith "SELECT_CONV"
    end;

val SELECT_REFL = dprove
 (`!x:'a. (@y. y = x) = x`, fn () => 
  GEN_TAC THEN CONV_TAC SELECT_CONV THEN
  EXISTS_TAC `x:'a` THEN REFL_TAC);

val SELECT_REFL_2 = dprove
 (`!x:'a. (@y. x = y) = x`, fn () => 
  GEN_TAC THEN CONV_TAC (ONCE_DEPTH_CONV SYM_CONV) THEN CONV_TAC SELECT_CONV THEN
  EXISTS_TAC `x:'a` THEN REFL_TAC);

val SELECT_UNIQUE = dprove
 (`!P x. (!y:'a. P y = (y = x)) ==> ($@ P = x)`, fn () => 
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM ETA_AX] THEN
  ASM_REWRITE_TAC[SELECT_REFL]);

val _ = add_implicit_rewrites [SELECT_REFL, SELECT_REFL_2];

(* ------------------------------------------------------------------------- *)
(* Derived principles of definition based on existence.                      *)
(* ------------------------------------------------------------------------- *)

val gen_specification =
  let fun specify 0 th = ([],th)
	| specify n th =
	  let val (cid,th') =
	      (I ## CONV_RULE BETA_CONV)
                 (gen_basic_definition
	  (CONV_RULE (RATOR_CONV (REWR_CONV EXISTS_THM) THENC BETA_CONV) th))
	      val (cids,th'') = specify (n-1) th'
	  in (cid::cids,th'')
	  end
  in fn n => fn th =>
    let val (asl,c) = dest_thm th
    in if not (null (free_vars c)) then
	   failwith "gen_specification: Free variables in predicate" else
       let val avs = fst(strip_exists c)
       in if n <= 0 orelse n > length avs then
           failwith "gen_specification: Unsuitable number of constants" else
         specify n th
       end
    end
  end;

fun new_specification names th =
    let val (cids,th') = gen_specification (length names) th
	val _ = app parse_as_constant (zip names cids)
    in (cids,th')
    end
  handle e => WRAP_ERR("new_specification",e);

fun simple_new_specification th =
  new_specification
    (map (fst o dest_var) (fst(strip_exists(concl th)))) th;

fun gen_type_definition th =
    let val th0 = CONV_RULE (RATOR_CONV (REWR_CONV EXISTS_THM) THENC BETA_CONV) th
	val (tycid,absid,repid,th1,th2) = gen_basic_type_definition th0
    in (tycid,absid,repid,CONJ (GEN_ALL th1)
	(GEN_ALL (CONV_RULE (LAND_CONV (TRY_CONV BETA_CONV)) th2)))
    end;
fun new_type_definition tyname (absname,repname) th =
    let val (res as (tycid,absid,repid,th)) = gen_type_definition th
    in (parse_as_type (tyname,tycid);
	parse_as_constant (absname,absid);
	parse_as_constant (repname,repid);
	res)
    end;

(* ------------------------------------------------------------------------- *)
(* Derive excluded middle (the proof is from Beeson's book).                 *)
(* ------------------------------------------------------------------------- *)

val EXCLUDED_MIDDLE = dprove
 (`!t. t \/ ~t`, fn () => 
  GEN_TAC THEN SUBGOAL_THEN
   `(((@x. (x = F) \/ (x = T) /\ t) = F) \/
     ((@x. (x = F) \/ (x = T) /\ t) = T) /\ t) /\
    (((@x. (x = T) \/ (x = F) /\ t) = T) \/
     ((@x. (x = T) \/ (x = F) /\ t) = F) /\ t)`
  MP_TAC THENL
   [CONJ_TAC THEN CONV_TAC SELECT_CONV THENL
     [EXISTS_TAC `F`, EXISTS_TAC `T`] THEN
    DISJ1_TAC THEN REFL_TAC, ALL_TAC] THEN
  DISCH_THEN STRIP_ASSUME_TAC THEN
  TRY(DISJ1_TAC THEN FIRST_ASSUM ACCEPT_TAC) THEN
  MP_TAC(ITAUT `~(T = F)`) THEN
  POP_ASSUM_LIST(PURE_ONCE_REWRITE_TAC o map SYM) THEN
  DISCH_THEN(curry op THEN DISJ2_TAC o MP_TAC) THEN
  MATCH_MP_TAC(ITAUT `(a ==> b) ==> ~b ==> ~a`) THEN
  DISCH_THEN(SUBST1_TAC o EQT_INTRO) THEN
  GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV)
   [ITAUT `a \/ (b /\ T) = b \/ (a /\ T)`] THEN
  REFL_TAC);

val BOOL_CASES_AX = dprove
 (`!t. (t = T) \/ (t = F)`, fn () => 
  GEN_TAC THEN DISJ_CASES_TAC(SPEC `t:bool` EXCLUDED_MIDDLE) THEN
  ASM_REWRITE_TAC[]);

(* ------------------------------------------------------------------------- *)
(* Classically based tactics. (See also COND_CASES_TAC later on.)            *)
(* ------------------------------------------------------------------------- *)

fun BOOL_CASES_TAC p = STRUCT_CASES_TAC (SPEC p BOOL_CASES_AX);

fun ASM_CASES_TAC t = DISJ_CASES_TAC(SPEC t EXCLUDED_MIDDLE);

(* ------------------------------------------------------------------------- *)
(* Set up a reasonable tautology checker for classical logic.                *)
(* ------------------------------------------------------------------------- *)

val TAUT =
  let fun RTAUT_TAC (asl,w) =
      let fun ok t = 
	  type_of t = bool_ty andalso can (find_term is_var) t andalso 
	  free_in t w 
      in (REPEAT(W((fn x => REWRITE_TAC[] THEN x) o BOOL_CASES_TAC o
		 hd o sort free_in o (find_terms ok) o snd)) THEN
	  REWRITE_TAC []) (asl,w) 
      end
      val TAUT_TAC = REPEAT(GEN_TAC ORELSE CONJ_TAC) THEN RTAUT_TAC 
  in fn tm => dprove(tm,fn () => TAUT_TAC)
  end;

fun TAUT_TAC (asms,gl) = 
    let val th = TAUT gl in ([],fn _ => th) end;

val TAUT_CONV = EQT_INTRO o TAUT;

val TAUT_PROVE = TAUT;

(* ------------------------------------------------------------------------- *)
(* A few useful classical tautologies.                                       *)
(* ------------------------------------------------------------------------- *)

val DE_MORGAN_THM = TAUT
  `!t1 t2. (~(t1 /\ t2) = ~t1 \/ ~t2) /\ (~(t1 \/ t2) = ~t1 /\ ~t2)`;

val NOT_CLAUSES =
  TAUT `(!t. ~ (~t) = t) /\ (~T = F) /\ (~F = T)`;

val NOT_IMP = TAUT `!t1 t2. ~(t1 ==> t2) = t1 /\ ~t2`;

val BOOL_FORALL_SPLIT = dprove(`!P. (!b. P b) = (P T /\ P F)`, fn () => 
    GEN_TAC THEN EQ_TAC THEN DISCH_TAC THEN 
    ASM_REWRITE_TAC [] THEN GEN_TAC THEN 
    BOOL_CASES_TAC `b:bool` THEN ASM_REWRITE_TAC []);

val BOOL_EXISTS_SPLIT = dprove(`!P. (?b. P b) = (P T \/ P F)`, fn () => 
    GEN_TAC THEN EQ_TAC THEN STRIP_TAC 
    THENL [BOOL_CASES_TAC `b:bool`,
	   EXISTS_TAC truth_tm,EXISTS_TAC false_tm] THEN ASM_REWRITE_TAC []);

val BOOL_SPLIT = CONJ BOOL_FORALL_SPLIT BOOL_EXISTS_SPLIT;

val _ = add_implicit_rewrites [NOT_CLAUSES];

(* ------------------------------------------------------------------------- *)
(* Some classically based rules.                                             *)
(* ------------------------------------------------------------------------- *)

val CCONTR =
    let val P = `P:bool`
	val pth = TAUT `(~P ==> F) ==> P`
    in fn tm => fn th =>
	let val tm' = mk_neg tm
	in MP (INST [P |-> tm] pth) (DISCH tm' th)
	end
    handle Fail _ => failwith "CCONTR"
    end;

val CONTRAPOS_CONV =
    let val a = `a:bool` and b = `b:bool`
	val pth = TAUT `(a ==> b) = (~b ==> ~a)`
    in fn tm =>
	let val (P,Q) = dest_imp tm
        in INST [a |-> P, b |-> Q] pth
	end
    handle Fail _ => failwith "CONTRAPOS_CONV"
    end;


(* ------------------------------------------------------------------------- *)
(* Infinite de Morgan laws.                                                  *)
(* ------------------------------------------------------------------------- *)

val NOT_EXISTS_THM = dprove
 (`!P. ~(?x:'a. P x) = (!x. ~(P x))`, fn () => 
  GEN_TAC THEN EQ_TAC THEN DISCH_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN UNDISCH_TAC`~(?x:'a. P x)` THEN
    REWRITE_TAC [] THEN EXISTS_TAC`x:'a` THEN POP_ASSUM ACCEPT_TAC,
    DISCH_THEN(CHOOSE_THEN MP_TAC) THEN ASM_REWRITE_TAC []]);

val EXISTS_NOT_THM = dprove
 (`!P. (?x:'a. ~(P x)) = ~(!x. P x)`, fn () => 
  PURE_ONCE_REWRITE_TAC[TAUT`(a = ~b) = (~a = b)`] THEN
  REWRITE_TAC ([NOT_EXISTS_THM]));

val NOT_FORALL_THM = dprove
 (`!P. ~(!x. P x) = (?x:'a. ~(P x))`, fn () => 
  MATCH_ACCEPT_TAC(GSYM EXISTS_NOT_THM));

val FORALL_NOT_THM = dprove
 (`!P. (!x. ~(P x)) = ~(?x:'a. P x)`, fn () => 
  MATCH_ACCEPT_TAC(GSYM NOT_EXISTS_THM));

(* ------------------------------------------------------------------------- *)
(* Universal quantifier and disjunction                                      *)
(* ------------------------------------------------------------------------- *)

val LEFT_FORALL_OR_THM = dprove
 (`!P Q. (!x:'a. P x \/ Q) = (!x. P x) \/ Q`, fn () => 
  REPEAT GEN_TAC THEN 
  PURE_ONCE_REWRITE_TAC[TAUT`(a = b) = (~a = ~b)`] THEN
  REWRITE_TAC ([NOT_FORALL_THM,DE_MORGAN_THM,LEFT_EXISTS_AND_THM]));

val RIGHT_FORALL_OR_THM = dprove
 (`!P Q. (!x:'a. P \/ Q x) = P \/ (!x. Q x)`, fn () => 
  REPEAT GEN_TAC THEN 
  PURE_ONCE_REWRITE_TAC[TAUT`(a = b) = (~a = ~b)`] THEN
  REWRITE_TAC ([NOT_FORALL_THM,DE_MORGAN_THM,RIGHT_EXISTS_AND_THM]));

val LEFT_OR_FORALL_THM = dprove
 (`!P Q. (!x:'a. P x) \/ Q = (!x. P x \/ Q)`, fn () => 
  MATCH_ACCEPT_TAC(GSYM LEFT_FORALL_OR_THM));

val RIGHT_OR_FORALL_THM = dprove
 (`!P Q. P \/ (!x:'a. Q x) = (!x. P \/ Q x)`, fn () => 
  MATCH_ACCEPT_TAC(GSYM RIGHT_FORALL_OR_THM));


(* ------------------------------------------------------------------------- *)
(* Implication and quantifiers.                                              *)
(* ------------------------------------------------------------------------- *)

val LEFT_IMP_FORALL_THM = dprove
 (`!P Q. ((!x:'a. P x) ==> Q) = (?x. P x ==> Q)`, fn () => 
  REPEAT GEN_TAC THEN 
  PURE_ONCE_REWRITE_TAC[TAUT`(a = b) = (~a = ~b)`] THEN
  REWRITE_TAC ([NOT_EXISTS_THM,NOT_IMP,LEFT_AND_FORALL_THM]));

val LEFT_EXISTS_IMP_THM = dprove
 (`!P Q. (?x. P x ==> Q) = ((!x:'a. P x) ==> Q)`, fn () => 
  MATCH_ACCEPT_TAC(GSYM LEFT_IMP_FORALL_THM));

val RIGHT_IMP_EXISTS_THM = dprove
 (`!P Q. (P ==> ?x:'a. Q x) = (?x:'a. P ==> Q x)`, fn () => 
  REPEAT GEN_TAC THEN 
  PURE_ONCE_REWRITE_TAC[TAUT`(a = b) = (~a = ~b)`] THEN
  REWRITE_TAC ([NOT_EXISTS_THM,NOT_IMP,RIGHT_AND_FORALL_THM]));

val RIGHT_EXISTS_IMP_THM = dprove
 (`!P Q. (?x:'a. P ==> Q x) = (P ==> ?x:'a. Q x)`, fn () => 
  MATCH_ACCEPT_TAC(GSYM RIGHT_IMP_EXISTS_THM));










(* ------------------------------------------------------------------------- 
 * The conditional.                                                          
 *    P => x | y
 * ------------------------------------------------------------------------- *)

val (cond_cid,COND_DEF) = new_simple_definition
  `COND = \t t1 t2. @x:'a. ((t = T) ==> (x = t1)) /\
                          ((t = F) ==> (x = t2))`;


fun cond_ty ty = bool_ty --> (ty  --> (ty --> ty));
fun mk_cond (cond,larm,rarm) = 
  list_mk_comb(mk_const(cond_cid,cond_ty(type_of larm)),[cond,larm,rarm])
  handle Fail _ => failwith "mk_cond";


fun dest_cond tm =
    let val (opr,[cond,l,r]) = strip_comb tm
    in if name_of_const opr = cond_cid then (cond,l,r) else raise Fail ""
    end handle Fail _ => failwith "dest_cond";

val is_cond = can dest_cond;

val COND_CLAUSES = dprove
 (`!(t1:'a) t2. ((T => t1 | t2) = t1) /\ ((F => t1 | t2) = t2)`, fn () => 
  REWRITE_TAC[COND_DEF, BETA_THM]);

val _ = add_implicit_rewrites [COND_CLAUSES];

val COND_EXPAND = dprove
 (`!b t1 t2. (b => t1 | t2) = (~b \/ t1) /\ (b \/ t2)`, fn () => 
  REWRITE_TAC[BOOL_SPLIT]);

val COND_ID = dprove
 (`!b (t:'a). (b => t | t) = t`, fn () => 
  REWRITE_TAC[BOOL_SPLIT]);

val COND_RAND = dprove
 (`!b (f:'a->'b) x y. f (b => x | y) = (b => f x | f y)`, fn () => 
  REWRITE_TAC[BOOL_SPLIT]);

val COND_RATOR = dprove
 (`!b (f:'a->'b) g x. (b => f | g)(x) = (b => f x | g x)`, fn () => 
  REWRITE_TAC[BOOL_SPLIT]);

val COND_ABS = dprove
 (`!b (f:'a->'b) g. (\x. b => f x | g x) = (b => f | g)`, fn () => 
  REWRITE_TAC[BOOL_SPLIT] THEN
  CONV_TAC(ONCE_DEPTH_CONV ETA_CONV) THEN REWRITE_TAC []);

val COND_BOOL_CLAUSES = 
    TAUT `(!b e. (b => T | e) = (b \/ e)) /\
	     (!b t. (b => t | T) = (b ==> t)) /\
             (!b e. (b => F | e) = (~b /\ e)) /\
             (!b t. (b => t | F) = (b /\ t))`;

val _ = add_implicit_rewrites [COND_BOOL_CLAUSES];



(* ------------------------------------------------------------------------- *)
(* Throw monotonicity in.                                                    *)
(* ------------------------------------------------------------------------- *)

val MONO_COND = dprove
 (`(A ==> B) /\ (C ==> D) ==> (b => A | C) ==> (b => B | D)`, fn () => 
  STRIP_TAC THEN BOOL_CASES_TAC `b:bool` THEN
  ASM_REWRITE_TAC[]);

(* ------------------------------------------------------------------------- *)
(* Tactic for splitting over an arbitrarily chosen conditional.              *)
(* ------------------------------------------------------------------------- *)

val COND_ELIM_THM = dprove
 (`(P:'a->bool) (c => x | y) = (c ==> P x) /\ (~c ==> P y)`, fn () => 
  BOOL_CASES_TAC `c:bool` THEN REWRITE_TAC[]);

val COND_ELIM_CONV = HIGHER_REWRITE_CONV[COND_ELIM_THM];

val COND_CASES_TAC =
  let val tac = 
      CONV_TAC COND_ELIM_CONV THEN CONJ_TAC THENL
      [DISCH_THEN(fn th => ASSUME_TAC th THEN SUBST1_TAC(EQT_INTRO th)),
       DISCH_THEN(fn th => ASSUME_TAC th THEN SUBST1_TAC(EQF_INTRO th))]
  in fn x => tac x handle e => WRAP_ERR("COND_CASES_TAC",e)
  end;

(* ------------------------------------------------------------------------- *)
(* Skolemization.                                                            *)
(* ------------------------------------------------------------------------- *)

val SKOLEM_THM = dprove
 (`!P. (!x:'a. ?y:'b. P x y) = (?y. !x. P x (y x))`, fn () => 
  REPEAT(STRIP_TAC ORELSE EQ_TAC) THENL
   [EXISTS_TAC `\x:'a. @y:'b. P x y` THEN GEN_TAC THEN
    BETA_TAC THEN CONV_TAC SELECT_CONV,
    EXISTS_TAC `(y:'a->'b) x`] THEN
  POP_ASSUM MATCH_ACCEPT_TAC);

(* ------------------------------------------------------------------------- *)
(* NB: this one is true intutionistically and intensionally.                 *)
(* ------------------------------------------------------------------------- *)

val UNIQUE_SKOLEM_ALT = dprove
 (`!P:'a->'b->bool. (!x. ?!y. P x y) = ?f. !x y. P x y = (f x = y)`, fn () => 
  GEN_TAC THEN REWRITE_TAC[EXISTS_UNIQUE_ALT, SKOLEM_THM]);


(* ------------------------------------------------------------------------- *)
(* and this one intuitionistically and extensionally.                        *)
(* ------------------------------------------------------------------------- *)

val UNIQUE_SKOLEM_THM = dprove
 (`!P. (!x:'a. ?!y:'b. P x y) = (?!f. !x. P x (f x))`, fn () => 
  GEN_TAC THEN REWRITE_TAC[EXISTS_UNIQUE_THM, SKOLEM_THM, FORALL_AND_THM] THEN
  EQ_TAC THEN DISCH_THEN(CONJUNCTS_THEN ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THENL
   [REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[FUN_EQ_THM] THEN
    X_GEN_TAC `x:'a` THEN FIRST_ASSUM MATCH_MP_TAC THEN
    EXISTS_TAC `x:'a` THEN ASM_REWRITE_TAC[],
    MAP_EVERY X_GEN_TAC [`x:'a`, `y1:'b`, `y2:'b`] THEN STRIP_TAC THEN
    FIRST_ASSUM(X_CHOOSE_TAC `f:'a->'b`) THEN
    SUBGOAL_THEN `(\z. (z = x) => y1 | (f:'a->'b) z) =
                  (\z. (z = x) => y2 | (f:'a->'b) z)` MP_TAC THENL
     [FIRST_ASSUM MATCH_MP_TAC THEN
      REPEAT STRIP_TAC THEN BETA_TAC THEN COND_CASES_TAC THEN
      ASM_REWRITE_TAC[],
      DISCH_THEN(MP_TAC o C AP_THM `x:'a`) THEN REWRITE_TAC[BETA_THM]]]);



(* ------------------------------------------------------------------------- 
 * Congruence Rules                                                            
 * ------------------------------------------------------------------------- *)

val IMP_CONG = 
    TAUT `(P = P') ==> (P' ==> (Q = Q')) ==> ((P ==> Q) = (P' ==> Q'))`;
    
val AND_CONG = 
    TAUT`(Q ==> (P = P')) ==> (P' ==> (Q = Q')) ==> 
            ((P /\ Q) = (P' /\ Q'))`;
    
val OR_CONG = 
    TAUT `(~Q ==> (P = P')) ==> (~P' ==> (Q = Q')) ==> 
	     ((P \/ Q) = (P' \/ Q'))`;
    
val COND_CONG = 
    TAUT `(g = g') ==> 
  	  (g' ==> (t:'a = t')) ==> 
	      (~g' ==> (e = e')) ==> 
		  ((g => t | e) = (g' => t' | e'))`;
	
(* ------------------------------------------------------------------------- *)
(* Inbuilt tautologies                                                       *)
(* ------------------------------------------------------------------------- *)


val OR_IMP_THM =  TAUT `!A B. (A = B \/ A) = (B ==> A)`;
	
val NOT_IMP = TAUT `!A B. ~(A ==> B) = A /\ ~B`;
    
val DE_MORGAN_THM = 
    TAUT `!A B. (~(A /\ B) = ~A \/ ~B) /\ (~(A \/ B) = ~A /\ ~B)`;
    

val LEFT_AND_OVER_OR = TAUT
    `!A B C. A /\ (B \/ C) = A /\ B \/ A /\ C`;
    
val RIGHT_AND_OVER_OR = TAUT
    `!A B C. (B \/ C) /\ A = B /\ A \/ C /\ A`;
    
val LEFT_OR_OVER_AND = TAUT
    `!A B C. A \/ B /\ C = (A \/ B) /\ (A \/ C)`;
    
val RIGHT_OR_OVER_AND = TAUT
    `!A B C. B /\ C \/ A = (B \/ A) /\ (C \/ A)`;
    
val IMP_DISJ_THM = TAUT
    `!A B. A ==> B = ~A \/ B`;
	
val IMP_F_EQ_F = TAUT
    `!t. t ==> F = (t = F)`;
	
val AND_IMP_INTRO = TAUT
    `!t1 t2 t3. t1 ==> t2 ==> t3 = t1 /\ t2 ==> t3`;
	
val EQ_ELIM_THM = TAUT 
    `!t1 t2. (t1 = t2) = (t1 ==> t2) /\ (t2 ==> t1)`;
	
val EQ_EXPAND = TAUT
    `!t1 t2. (t1 = t2) = ((t1 /\ t2) \/ (~t1 /\ ~t2))`;
    

(* ------------------------------------------------------------------------- *)
(* ------------------------------------------------------------------------- *)

val SELECT_THM = dprove
  (`!P. P (@x. P x) = (?(x:'a). P x)`, fn () => REWRITE_TAC [BETA_THM,EXISTS_THM]);


val theorems =
  [("ETA_AX",ETA_AX),              
   ("FUN_EQ_THM",FUN_EQ_THM),          
   ("SELECT_UNIQUE",SELECT_UNIQUE),        
   ("SELECT_THM",SELECT_THM),           
   ("SELECT_AX",SELECT_AX),
   ("SELECT_REFL",SELECT_REFL),
   ("BOOL_CASES_AX",BOOL_CASES_AX),        
   ("IMP_F_EQ_F",IMP_F_EQ_F), 
   ("NOT_IMP",NOT_IMP),    
   ("NOT_CLAUSES",NOT_CLAUSES),
   ("OR_CONG",OR_CONG),
   ("IMP_CONG",IMP_CONG),            
   ("AND_CONG",AND_CONG), 
   ("AND_IMP_INTRO",AND_IMP_INTRO),
   ("OR_IMP_THM",OR_IMP_THM),          

   ("RIGHT_OR_OVER_AND",RIGHT_OR_OVER_AND),   
   ("DE_MORGAN_THM",DE_MORGAN_THM),        
   ("RIGHT_AND_OVER_OR",RIGHT_AND_OVER_OR),
   ("LEFT_AND_OVER_OR",LEFT_AND_OVER_OR),     
   ("LEFT_OR_OVER_AND",LEFT_OR_OVER_AND), 

   ("EQ_EXPAND",EQ_EXPAND),           
   ("EQ_EXT",EQ_EXT),              
   ("EQ_ELIM_THM",EQ_ELIM_THM), 

   ("LEFT_FORALL_OR_THM",LEFT_FORALL_OR_THM),  
   ("NOT_EXISTS_THM",NOT_EXISTS_THM),      
   ("RIGHT_FORALL_OR_THM",RIGHT_FORALL_OR_THM), 
   ("EXCLUDED_MIDDLE",EXCLUDED_MIDDLE),     
   ("LEFT_OR_FORALL_THM",LEFT_OR_FORALL_THM),  
   ("RIGHT_IMP_EXISTS_THM",RIGHT_IMP_EXISTS_THM), 
   ("EXISTS_THM",EXISTS_THM),           
   ("EXISTS_NOT_THM",EXISTS_NOT_THM),       
   ("SKOLEM_THM",SKOLEM_THM),           
   ("LEFT_IMP_FORALL_THM",LEFT_IMP_FORALL_THM), 
   ("IMP_DISJ_THM",IMP_DISJ_THM),        
   ("LEFT_EXISTS_IMP_THM",LEFT_EXISTS_IMP_THM), 
   ("FORALL_NOT_THM",FORALL_NOT_THM),      
   ("NOT_FORALL_THM",NOT_FORALL_THM),      
   ("RIGHT_OR_FORALL_THM",RIGHT_OR_FORALL_THM), 
   ("UNIQUE_SKOLEM_ALT",UNIQUE_SKOLEM_ALT), 
   ("SELECT_REFL_2",SELECT_REFL_2),     
   ("RIGHT_EXISTS_IMP_THM",RIGHT_EXISTS_IMP_THM), 
   ("UNIQUE_SKOLEM_THM",UNIQUE_SKOLEM_THM),    

   ("COND_DEF",COND_DEF), 
   ("MONO_COND",MONO_COND),    
   ("COND_RATOR",COND_RATOR),           
   ("COND_EXPAND",COND_EXPAND),          
   ("COND_CLAUSES",COND_CLAUSES),        
   ("COND_RAND",COND_RAND),           
   ("COND_ELIM_THM",COND_ELIM_THM),       
   ("COND_CONG",COND_CONG), 
   ("COND_ID",COND_ID),  
   ("COND_ABS",COND_ABS)];


val _ = say "done!\n";

end (* struct *)
