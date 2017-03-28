(* ===================================================================== *)
(* FILE          : taut_thms.sml                                         *)
(* DESCRIPTION   : A bunch of tautologies. Commented code is due to Tom  *)
(*                 Melham.                                               *)
(*                                                                       *)
(* AUTHORS       : (c) Tom Melham, University of Cambridge,              *)
(*                     Konrad Slind, University of Calgary               *)
(* DATE          : September 11, 1991                                    *)
(* ===================================================================== *)


structure Taut_thms : Taut_thms_sig =
struct

structure Thm = Base_logic.Thm;
open Term_io.Parse;
open Tactical;
  infix THEN;
  infix THENL;
  infix ORELSE;

(* I use the brute-force method of truth-tables to prove the 
   following delicately-proved theorems. KLS
% --------------------------------------------------------------------- %
% OR_IMP_THM = |- !t1 t2. (t1 = t2 \/ t1) = (t2 ==> t1)	 [TFM 90.06.28]	%
% --------------------------------------------------------------------- %

let OR_IMP_THM = 
    let t1 = "t1:bool" and t2 = "t2:bool" in
    let asm1 = ASSUME "^t1 = (^t2 \/ ^t1)" and
        asm2 = EQT_INTRO(ASSUME t2) in
    let th1 = SUBST [asm2,t2] (concl asm1) asm1 in
    let th2 = TRANS th1 (CONJUNCT1 (SPEC t1 OR_CLAUSES)) in
    let imp1 = DISCH (concl asm1) (DISCH t2 (EQT_ELIM th2)) in
    let asm3 = ASSUME "^t2 ==> ^t1" and
        asm4 = ASSUME "^t2 \/ ^t1" in
    let th3 = DISJ_CASES asm4 (MP asm3 (ASSUME t2)) (ASSUME t1) in
    let th4 = DISCH (concl asm4) th3 and
        th5 = DISCH t1 (DISJ2 t2 (ASSUME t1)) in
    let imp2 = DISCH "^t2 ==> ^t1" (IMP_ANTISYM_RULE th5 th4) in
        GEN t1 (GEN t2 (IMP_ANTISYM_RULE imp1 imp2));;

% --------------------------------------------------------------------- %
% NOT_IMP = |- !t1 t2. ~(t1 ==> t2) = t1 /\ ~t2	         [TFM 90.07.09] %
% --------------------------------------------------------------------- %

let NOT_IMP = 
    let t1 = "t1:bool" and t2 = "t2:bool" in
    let asm1 = ASSUME "~ (^t1 ==> ^t2)" in
    let thm1 = SUBST [EQF_INTRO (ASSUME (mk_neg t1)),t1] (concl asm1) asm1 in
    let thm2 = CCONTR t1 (MP thm1 (DISCH "F" (CONTR t2 (ASSUME "F")))) in
    let thm3 = SUBST [EQT_INTRO (ASSUME t2),t2] (concl asm1) asm1 in
    let thm4 = NOT_INTRO(DISCH t2 (MP thm3(DISCH t1 (ADD_ASSUM t1 TRUTH)))) in
    let imp1 = DISCH (concl asm1) (CONJ thm2 thm4) in
    let conj =  ASSUME "^t1 /\ ~ ^t2" in
    let asm2,asm3 = (CONJUNCT1 conj, CONJUNCT2 conj) in
    let asm4 = ASSUME "^t1 ==> ^t2" in
    let thm5 = MP (SUBST [EQF_INTRO asm3,t2] (concl asm4) asm4) asm2 in
    let imp2 = DISCH "^t1 /\ ~ ^t2" (NOT_INTRO(DISCH "^t1 ==> ^t2" thm5)) in
        GEN t1 (GEN t2 (IMP_ANTISYM_RULE imp1 imp2));;


% --------------------------------------------------------------------- %
% DISJ_ASSOC: |- !t1 t2 t3. t1 \/ t2 \/ t3 = (t1 \/ t2) \/ t3           %
% --------------------------------------------------------------------- %

let DISJ_ASSOC = 
    let t1 = "t1:bool" and t2 = "t2:bool" and t3 = "t3:bool" in 
    let at1 = DISJ1 (DISJ1 (ASSUME t1) t2) t3 and
        at2 = DISJ1 (DISJ2 t1 (ASSUME t2)) t3 and
        at3 = DISJ2 (mk_disj(t1,t2)) (ASSUME t3) in
    let thm = DISJ_CASES (ASSUME (mk_disj(t2,t3))) at2 at3 in
    let thm1 = DISJ_CASES (ASSUME (mk_disj(t1,mk_disj(t2,t3)))) at1 thm in
    let at1 = DISJ1 (ASSUME t1) (mk_disj(t2,t3)) and
        at2 = DISJ2 t1 (DISJ1 (ASSUME t2) t3) and
        at3 = DISJ2 t1 (DISJ2 t2 (ASSUME t3)) in
    let thm = DISJ_CASES (ASSUME (mk_disj(t1,t2))) at1 at2 in
    let thm2 = DISJ_CASES (ASSUME (mk_disj(mk_disj(t1,t2),t3))) thm at3 in
    let imp1 = DISCH (mk_disj(t1,mk_disj(t2,t3))) thm1 and
        imp2 = DISCH (mk_disj(mk_disj(t1,t2),t3)) thm2 in
        GENL [t1;t2;t3] (IMP_ANTISYM_RULE imp1 imp2);;

% --------------------------------------------------------------------- %
% DISJ_SYM: |- !t1 t2. t1 \/ t2 = t2 \/ t1                   		%
% --------------------------------------------------------------------- %

let DISJ_SYM =
    let t1 = "t1:bool" and t2 = "t2:bool" in
    let th1 = DISJ1 (ASSUME t1) t2 and th2 = DISJ2 t1 (ASSUME t2) in
    let thm1 = DISJ_CASES (ASSUME(mk_disj(t2,t1))) th2 th1 in
    let th1 = DISJ1 (ASSUME t2) t1 and th2 = DISJ2 t2 (ASSUME t1) in
    let thm2 = DISJ_CASES (ASSUME(mk_disj(t1,t2))) th2 th1 in
    let imp1 = DISCH (mk_disj(t2,t1)) thm1 and
        imp2 = DISCH (mk_disj(t1,t2)) thm2 in
        GENL [t1;t2] (IMP_ANTISYM_RULE imp2 imp1);;

% --------------------------------------------------------------------- %
% DE_MORGAN_THM: 							%
%   |- !t1 t2.(~(t1 /\ t2) = ~t1 \/ ~t2) /\ (~(t1 \/ t2) = ~t1 /\ ~t2)  %
% --------------------------------------------------------------------- %

let DE_MORGAN_THM = 
    let t1 = "t1:bool" and t2 = "t2:bool" in
    let thm1 = 
        let asm1 = ASSUME "~(^t1 /\ ^t2)" in
        let cnj = MP asm1 (CONJ (ASSUME t1) (ASSUME t2)) in
        let imp1 = 
            let case1 = DISJ2 "~^t1" (NOT_INTRO(DISCH t2 cnj)) in
            let case2 = DISJ1 (ASSUME "~ ^t1") "~ ^t2" in
                DISJ_CASES (SPEC t1 EXCLUDED_MIDDLE) case1 case2 in
        let th1 = MP (ASSUME "~^t1") (CONJUNCT1 (ASSUME "^t1 /\ ^t2")) and
            th2 = MP (ASSUME "~^t2") (CONJUNCT2 (ASSUME "^t1 /\ ^t2")) in
        let imp2 = 
            let fth = DISJ_CASES (ASSUME "~^t1 \/ ~^t2") th1 th2 in
                DISCH "~^t1 \/ ~^t2" (NOT_INTRO(DISCH "^t1 /\ ^t2" fth)) in
            IMP_ANTISYM_RULE (DISCH "~(^t1 /\ ^t2)" imp1) imp2 in
    let thm2 = 
        let asm1 = ASSUME "~(^t1 \/ ^t2)" in
        let imp1 = 
            let th1 = NOT_INTRO (DISCH t1 (MP asm1 (DISJ1 (ASSUME t1) t2))) in
            let th2 = NOT_INTRO (DISCH t2 (MP asm1 (DISJ2 t1 (ASSUME t2)))) in
                DISCH "~(^t1 \/ ^t2)" (CONJ th1 th2) in
        let imp2 = 
            let asm = ASSUME "^t1 \/ ^t2" in
            let a1 = CONJUNCT1(ASSUME "~^t1 /\ ~^t2") and
                a2 = CONJUNCT2(ASSUME "~^t1 /\ ~^t2") in
            let fth = DISJ_CASES asm (UNDISCH a1) (UNDISCH a2) in
                DISCH "~^t1 /\ ~^t2" (NOT_INTRO(DISCH "^t1 \/ ^t2" fth)) in
            IMP_ANTISYM_RULE imp1 imp2 in
    GEN t1 (GEN t2 (CONJ thm1 thm2));;



(* ------------------------------------------------------------------------- *)
(* Distributive laws:							    *)
(*									    *)
(* LEFT_AND_OVER_OR |- !t1 t2 t3. t1 /\ (t2 \/ t3) = t1 /\ t2 \/ t1 /\ t3    *)
(*									    *)
(* RIGHT_AND_OVER_OR |- !t1 t2 t3. (t2 \/ t3) /\ t1 = t2 /\ t1 \/ t3 /\ t1   *)
(*									    *)
(* LEFT_OR_OVER_AND |- !t1 t2 t3. t1 \/ t2 /\ t3 = (t1 \/ t2) /\ (t1 \/ t3)  *)
(*									    *)
(* RIGHT_OR_OVER_AND |- !t1 t2 t3. t2 /\ t3 \/ t1 = (t2 \/ t1) /\ (t3 \/ t1) *)
(* ------------------------------------------------------------------------- *)

val LEFT_AND_OVER_OR = 
    let val t1 = --`t1:bool`--
        and t2 = --`t2:bool`--
        and t3 = --`t3:bool`--
        val (th1,th2) = CONJ_PAIR(ASSUME (mk_conj(t1,mk_disj(t2,t3))))
        val th3 = CONJ th1 (ASSUME t2) and th4 = CONJ th1 (ASSUME t3)
        val th5 = DISJ_CASES_UNION th2 th3 th4
        val imp1 = DISCH (mk_conj(t1,mk_disj(t2,t3))) th5
        val (th1,th2) = (I ## C DISJ1 t3) (CONJ_PAIR (ASSUME (mk_conj(t1,t2))))
        val (th3,th4) = (I ## DISJ2 t2) (CONJ_PAIR (ASSUME (mk_conj(t1,t3))))
        val th5 = CONJ th1 th2 and th6 = CONJ th3 th4
        val th6 = DISJ_CASES (ASSUME (rand(concl imp1))) th5 th6
        val imp2 = DISCH (rand(concl imp1)) th6
    in
    GEN t1 (GEN t2 (GEN t3 (IMP_ANTISYM_RULE imp1 imp2)))
    end;

val RIGHT_AND_OVER_OR = 
   let val t1 = --`t1:bool`--
       and t2 = --`t2:bool`--
       and t3 = --`t3:bool`--
       val (th1,th2) = CONJ_PAIR(ASSUME (mk_conj(mk_disj(t2,t3),t1)))
       val th3 = CONJ (ASSUME t2) th2 and th4 = CONJ (ASSUME t3) th2
       val th5 = DISJ_CASES_UNION th1 th3 th4
       val imp1 = DISCH (mk_conj(mk_disj(t2,t3),t1)) th5
       val (th1,th2) = (C DISJ1 t3 ## I) (CONJ_PAIR (ASSUME (mk_conj(t2,t1))))
       val (th3,th4) = (DISJ2 t2 ## I) (CONJ_PAIR (ASSUME (mk_conj(t3,t1))))
       val th5 = CONJ th1 th2 and th6 = CONJ th3 th4
       val th6 = DISJ_CASES (ASSUME (rand(concl imp1))) th5 th6
       val imp2 = DISCH (rand(concl imp1)) th6
   in
   GEN t1 (GEN t2 (GEN t3 (IMP_ANTISYM_RULE imp1 imp2)))
   end;
    
val LEFT_OR_OVER_AND = 
   let val t1 = --`t1:bool`--
       and t2 = --`t2:bool`--
       and t3 = --`t3:bool`--
       val th1 = ASSUME (mk_disj(t1,mk_conj(t2,t3)))
       val th2 = CONJ (DISJ1 (ASSUME t1) t2) (DISJ1 (ASSUME t1) t3)
       val (th3,th4) = CONJ_PAIR (ASSUME(mk_conj(t2,t3)))
       val th5 = CONJ (DISJ2 t1 th3) (DISJ2 t1 th4)
       val imp1 = DISCH (concl th1) (DISJ_CASES th1 th2 th5)
       val (th1,th2) = CONJ_PAIR (ASSUME (rand(concl imp1)))
       val th3 = DISJ1 (ASSUME t1) (mk_conj(t2,t3))
       val (th4,th5) = CONJ_PAIR (ASSUME (mk_conj(t2,t3)))
       val th4 = DISJ2 t1 (CONJ (ASSUME t2) (ASSUME t3))
       val th5 = DISJ_CASES th2 th3 (DISJ_CASES th1 th3 th4)
       val imp2 = DISCH (rand(concl imp1)) th5
   in
   GEN t1 (GEN t2 (GEN t3 (IMP_ANTISYM_RULE imp1 imp2)))
   end;

val RIGHT_OR_OVER_AND = 
   let val t1 = --`t1:bool`--
       and t2 = --`t2:bool`--
       and t3 = --`t3:bool`--
       val th1 = ASSUME (mk_disj(mk_conj(t2,t3),t1))
       val th2 = CONJ (DISJ2 t2 (ASSUME t1)) (DISJ2 t3 (ASSUME t1))
       val (th3,th4) = CONJ_PAIR (ASSUME(mk_conj(t2,t3)))
       val th5 = CONJ (DISJ1 th3 t1) (DISJ1 th4 t1)
       val imp1 = DISCH (concl th1) (DISJ_CASES th1 th5 th2)
       val (th1,th2) = CONJ_PAIR (ASSUME (rand(concl imp1)))
       val th3 = DISJ2 (mk_conj(t2,t3)) (ASSUME t1) 
       val (th4,th5) = CONJ_PAIR (ASSUME (mk_conj(t2,t3)))
       val th4 = DISJ1 (CONJ (ASSUME t2) (ASSUME t3)) t1
       val th5 = DISJ_CASES th2 (DISJ_CASES th1 th4 th3) th3
       val imp2 = DISCH (rand(concl imp1)) th5
   in
   GEN t1 (GEN t2 (GEN t3 (IMP_ANTISYM_RULE imp1 imp2)))
   end;


(* ---------------------------------------------------------------------*)
(* IMP_F_EQ_F							*)
(*								*)
(* |- !t. t ==> F = (t = F)					*)
(*								*)
(*				       	                   RJB 92.09.26*)
(* ---------------------------------------------------------------------*)

let IMP_F_EQ_F =
   GEN_ALL (TRANS (el 5 (CONJUNCTS (SPEC_ALL IMP_CLAUSES)))
                     (SYM (el 4 (CONJUNCTS (SPEC_ALL EQ_CLAUSES)))));;

(* ---------------------------------------------------------------------*)
(* AND_IMP_INTRO							*)
(*								*)
(* |- !t1 t2 t3. t1 ==> t2 ==> t3 = t1 /\ t2 ==> t3		*)
(*								*)
(*				       	                   RJB 92.09.26*)
(* ---------------------------------------------------------------------*)

let AND_IMP_INTRO =
   let [IMP1;IMP2;IMP3;_;IMP4] = map GEN_ALL (CONJUNCTS (SPEC_ALL IMP_CLAUSES))
   and [AND1;AND2;AND3;AND4;_] = map GEN_ALL (CONJUNCTS (SPEC_ALL AND_CLAUSES))
   in  let thTl = SPEC "t2 ==> t3" IMP1
       and thFl = SPEC "t2 ==> t3" IMP3
   in  let thTr = AP_THM (AP_TERM "$==>" (SPEC "t2:bool" AND1)) "t3:bool"
       and thFr =
          TRANS (AP_THM (AP_TERM "$==>" (SPEC "t2:bool" AND3)) "t3:bool")
                   (SPEC "t3:bool" IMP3)
   in  let thT1 = thTl TRANS (SYM thTr)
       and thF1 = thFl TRANS (SYM thFr)
   in  let tm = "t1 ==> t2 ==> t3 = t1 /\ t2 ==> t3"
   in  let thT2 = SUBST_CONV [(ASSUME "t1 = T","t1:bool")] tm tm
       and thF2 = SUBST_CONV [(ASSUME "t1 = F","t1:bool")] tm tm
   in  let thT3 = EQ_MP (SYM thT2) thT1
       and thF3 = EQ_MP (SYM thF2) thF1
   in  GEN_ALL (DISJ_CASES (SPEC "t1:bool" BOOL_CASES_AX) thT3 thF3);;

(* ---------------------------------------------------------------------*)
(* EQ_IMP_THM							*)
(*								*)
(* |- !t1 t2. (t1 = t2) = (t1 ==> t2) /\ (t2 ==> t1)		*)
(*								*)
(*				       	                   RJB 92.09.26*)
(* ---------------------------------------------------------------------*)

let EQ_IMP_THM =
   let [IMP1;IMP2;IMP3;_;IMP4] = map GEN_ALL (CONJUNCTS (SPEC_ALL IMP_CLAUSES))
   and [EQ1;EQ2;EQ3;EQ4] = map GEN_ALL (CONJUNCTS (SPEC_ALL EQ_CLAUSES))
   and [AND1;AND2;AND3;AND4;_] = map GEN_ALL (CONJUNCTS (SPEC_ALL AND_CLAUSES))
   in  let thTl = SPEC "t2:bool" EQ1
       and thFl = SPEC "t2:bool" EQ3
   in  let thTr =
          TRANS
          (MK_COMB (AP_TERM "$/\" (SPEC "t2:bool" IMP1),SPEC "t2:bool" IMP2))
          (SPEC "t2:bool" AND2)
       and thFr =
          TRANS
          (MK_COMB (AP_TERM "$/\" (SPEC "t2:bool" IMP3),SPEC "t2:bool" IMP4))
          (SPEC "~t2" AND1)
   in  let thT1 = thTl TRANS (SYM thTr)
       and thF1 = thFl TRANS (SYM thFr)
   in  let tm = "(t1 = t2) = (t1 ==> t2) /\ (t2 ==> t1)"
   in  let thT2 = SUBST_CONV [(ASSUME "t1 = T","t1:bool")] tm tm
       and thF2 = SUBST_CONV [(ASSUME "t1 = F","t1:bool")] tm tm
   in  let thT3 = EQ_MP (SYM thT2) thT1
       and thF3 = EQ_MP (SYM thF2) thF1
   in  GEN_ALL (DISJ_CASES (SPEC "t1:bool" BOOL_CASES_AX) thT3 thF3);;

(* ---------------------------------------------------------------------*)
(* EQ_EXPAND							*)
(*								*)
(* |- !t1 t2. (t1 = t2) = ((t1 /\ t2) \/ (~t1 /\ ~t2))		*)
(*								*)
(*				       	                   RJB 92.09.26*)
(* ---------------------------------------------------------------------*)

let EQ_EXPAND =
   let [NOT1;NOT2] = tl (CONJUNCTS NOT_CLAUSES)
   and [EQ1;EQ2;EQ3;EQ4] = map GEN_ALL (CONJUNCTS (SPEC_ALL EQ_CLAUSES))
   and [AND1;AND2;AND3;AND4;_] = map GEN_ALL (CONJUNCTS (SPEC_ALL AND_CLAUSES))
   and [OR1;OR2;OR3;OR4;_] = map GEN_ALL (CONJUNCTS (SPEC_ALL OR_CLAUSES))
   in  let thTl = SPEC "t2:bool" EQ1
       and thFl = SPEC "t2:bool" EQ3
   in  let thTr =
          TRANS
          (MK_COMB
              (AP_TERM "$\/" (SPEC "t2:bool" AND1),
               TRANS (AP_THM (AP_TERM "$/\" NOT1) "~t2") (SPEC "~t2" AND3)))
          (SPEC "t2:bool" OR4)
       and thFr =
          TRANS
          (MK_COMB
              (AP_TERM "$\/" (SPEC "t2:bool" AND3),
               TRANS (AP_THM (AP_TERM "$/\" NOT2) "~t2") (SPEC "~t2" AND1)))
          (SPEC "~t2" OR3)
   in  let thT1 = thTl TRANS (SYM thTr)
       and thF1 = thFl TRANS (SYM thFr)
   in  let tm = "(t1 = t2) = ((t1 /\ t2) \/ (~t1 /\ ~t2))"
   in  let thT2 = SUBST_CONV [(ASSUME "t1 = T","t1:bool")] tm tm
       and thF2 = SUBST_CONV [(ASSUME "t1 = F","t1:bool")] tm tm
   in  let thT3 = EQ_MP (SYM thT2) thT1
       and thF3 = EQ_MP (SYM thF2) thF1
   in  GEN_ALL (DISJ_CASES (SPEC "t1:bool" BOOL_CASES_AX) thT3 thF3);;

(* ---------------------------------------------------------------------*)
(* COND_RATOR							        *)
(*								        *)
(* |- !b (f:'a->'b) g x. (b => f | g) x = (b => f x | g x)	        *)
(*								        *)
(*				       	                   RJB 92.09.26 *)
(* ---------------------------------------------------------------------*)

let COND_RATOR =
   let (COND_T,COND_F) =
      (GEN_ALL # GEN_ALL) (CONJ_PAIR (SPEC_ALL COND_CLAUSES))
   in  let thTl = AP_THM (ISPECL ["f:*->**";"g:*->**"] COND_T) "x:*"
       and thFl = AP_THM (ISPECL ["f:*->**";"g:*->**"] COND_F) "x:*"
   in  let thTr = ISPECL ["(f:*->** ) x";"(g:*->** ) x"] COND_T
       and thFr = ISPECL ["(f:*->** ) x";"(g:*->** ) x"] COND_F
   in  let thT1 = thTl TRANS (SYM thTr)
       and thF1 = thFl TRANS (SYM thFr)
   in  let tm = "(b => (f:*->** ) | g) x = (b => f x | g x)"
   in  let thT2 = SUBST_CONV [(ASSUME "b = T","b:bool")] tm tm
       and thF2 = SUBST_CONV [(ASSUME "b = F","b:bool")] tm tm
   in  let thT3 = EQ_MP (SYM thT2) thT1
       and thF3 = EQ_MP (SYM thF2) thF1
   in  GEN_ALL (DISJ_CASES (SPEC "b:bool" BOOL_CASES_AX) thT3 thF3);;

(* ---------------------------------------------------------------------*)
(* COND_RAND							        *)
(*								        *)
(* |- !(f:'a->'b) b x y. f (b => x | y) = (b => f x | f y)	        *)
(*								        *)
(*				       	                   RJB 92.09.26 *)
(* ---------------------------------------------------------------------*)

let COND_RAND =
   let (COND_T,COND_F) =
      (GEN_ALL # GEN_ALL) (CONJ_PAIR (SPEC_ALL COND_CLAUSES))
   in  let thTl = AP_TERM "f:*->**" (ISPECL ["x:*";"y:*"] COND_T)
       and thFl = AP_TERM "f:*->**" (ISPECL ["x:*";"y:*"] COND_F)
   in  let thTr = ISPECL ["(f:*->** ) x";"(f:*->** ) y"] COND_T
       and thFr = ISPECL ["(f:*->** ) x";"(f:*->** ) y"] COND_F
   in  let thT1 = thTl TRANS (SYM thTr)
       and thF1 = thFl TRANS (SYM thFr)
   in  let tm = "(f:*->** ) (b => x | y) = (b => f x | f y)"
   in  let thT2 = SUBST_CONV [(ASSUME "b = T","b:bool")] tm tm
       and thF2 = SUBST_CONV [(ASSUME "b = F","b:bool")] tm tm
   in  let thT3 = EQ_MP (SYM thT2) thT1
       and thF3 = EQ_MP (SYM thF2) thF1
   in  GEN_ALL (DISJ_CASES (SPEC "b:bool" BOOL_CASES_AX) thT3 thF3);;

(* ---------------------------------------------------------------------*)
(* COND_ABS							        *)
(*								        *)
(* |- !b (f:'a->'b) g. (\x. (b => f(x) | g(x))) = (b => f | g)	        *)
(*								        *)
(*				       	                   RJB 92.09.26 *)
(* ---------------------------------------------------------------------*)

let COND_ABS =
   let th = SYM (SPECL ["b:bool";"f:*->**";"g:*->**";"x:*"] COND_RATOR)
   in  GEN_ALL ((ABS "x:*" th) TRANS (ETA_CONV "\x. (b => (f:*->** ) | g) x"));

(* ---------------------------------------------------------------------*)
(* COND_EXPAND							        *)
(*								        *)
(* |- !b t1 t2. (b => t1 | t2) = ((~b \/ t1) /\ (b \/ t2))	        *)
(*								        *)
(*				       	                   RJB 92.09.26 *)
(* ---------------------------------------------------------------------*)

let COND_EXPAND =
   let (COND_T,COND_F) =
      (GEN_ALL # GEN_ALL) (CONJ_PAIR (SPEC_ALL COND_CLAUSES))
   and [NOT1;NOT2] = tl (CONJUNCTS NOT_CLAUSES)
   and [AND1;AND2;AND3;AND4;_] = map GEN_ALL (CONJUNCTS (SPEC_ALL AND_CLAUSES))
   and [OR1;OR2;OR3;OR4;_] = map GEN_ALL (CONJUNCTS (SPEC_ALL OR_CLAUSES))
   in  let thTl = ISPECL ["t1:bool";"t2:bool"] COND_T
       and thFl = ISPECL ["t1:bool";"t2:bool"] COND_F
   in  let thTr =
          let th1 = TRANS (AP_THM (AP_TERM "$\/" NOT1) "t1:bool")
                             (SPEC "t1:bool" OR3)
          and th2 = SPEC "t2:bool" OR1
          in  TRANS (MK_COMB (AP_TERM "$/\" th1,th2)) (SPEC "t1:bool" AND2)
       and thFr =
          let th1 = TRANS (AP_THM (AP_TERM "$\/" NOT2) "t1:bool")
                             (SPEC "t1:bool" OR1)
          and th2 = SPEC "t2:bool" OR3
          in  TRANS (MK_COMB (AP_TERM "$/\" th1,th2)) (SPEC "t2:bool" AND1)
   in  let thT1 = thTl TRANS (SYM thTr)
       and thF1 = thFl TRANS (SYM thFr)
   in  let tm = "(b => t1 | t2) = ((~b \/ t1) /\ (b \/ t2))"
   in  let thT2 = SUBST_CONV [(ASSUME "b = T","b:bool")] tm tm
       and thF2 = SUBST_CONV [(ASSUME "b = F","b:bool")] tm tm
   in  let thT3 = EQ_MP (SYM thT2) thT1
       and thF3 = EQ_MP (SYM thF2) thF1
   in  GEN_ALL (DISJ_CASES (SPEC "b:bool" BOOL_CASES_AX) thT3 thF3);;

*)

fun TAUT_TAC vlist =
   Tactical.REPEAT Tactic.GEN_TAC THEN
   Tactical.MAP_EVERY Tactic.BOOL_CASES_TAC vlist THEN
   Rewrite.REWRITE_TAC[Bool.ETA_AX (* for COND_ABS *)];


val OR_IMP_THM = prove
  (--`!A B. (A = B \/ A) = (B ==> A)`--,
      TAUT_TAC [--`A:bool`--, --`B:bool`--]);

val NOT_IMP = prove
  (--`!A B. ~(A ==> B) = A /\ ~B`--,
      TAUT_TAC [--`A:bool`--, --`B:bool`--]);

val DISJ_ASSOC = prove
  (--`!A B C. A \/ (B \/ C) = (A \/ B) \/ C`--,
      TAUT_TAC [--`A:bool`--, --`B:bool`--, --`C:bool`--]);

val DISJ_SYM = prove
  (--`!A B. A \/ B = B \/ A`--,
      TAUT_TAC [--`A:bool`--, --`B:bool`--]);

val DE_MORGAN_THM = prove
  (--`!A B. (~(A /\ B) = ~A \/ ~B) /\
            (~(A \/ B) = ~A /\ ~B)`--,
      TAUT_TAC [--`(A:bool)`--, --`(B:bool)`--]);

val LEFT_AND_OVER_OR = prove
   (--`!A B C. A /\ (B \/ C) = A /\ B \/ A /\ C`--,
       TAUT_TAC [(--`A:bool`--),
                 (--`B:bool`--),
                 (--`C:bool`--)]);


val RIGHT_AND_OVER_OR = prove
  (--`!A B C. (B \/ C) /\ A = B /\ A \/ C /\ A`--,
      TAUT_TAC [(--`A:bool`--),
                (--`B:bool`--),
                (--`C:bool`--)]);

val LEFT_OR_OVER_AND = prove
   (--`!A B C. A \/ B /\ C = (A \/ B) /\ (A \/ C)`--,
       TAUT_TAC [(--`A:bool`--),
                 (--`B:bool`--),
                 (--`C:bool`--)]);

val RIGHT_OR_OVER_AND = prove
  (--`!A B C. B /\ C \/ A = (B \/ A) /\ (C \/ A)`--,
      TAUT_TAC [(--`A:bool`--),
                (--`B:bool`--),
                (--`C:bool`--)]);

val IMP_DISJ_THM = prove
   (--`!A B. A ==> B = ~A \/ B`--,
      TAUT_TAC [--`A:bool`--, --`B:bool`--]);

val IMP_F_EQ_F = prove
   (--`!t. t ==> F = (t = F)`--,
      TAUT_TAC [--`t:bool`--]);

val AND_IMP_INTRO = prove
   (--`!t1 t2 t3. t1 ==> t2 ==> t3 = t1 /\ t2 ==> t3`--,
      TAUT_TAC [--`t1:bool`--, --`t2:bool`--, --`t3:bool`--]);

val EQ_IMP_THM = prove 
   (--`!t1 t2. (t1 = t2) = (t1 ==> t2) /\ (t2 ==> t1)`--,
      TAUT_TAC [--`t1:bool`--, --`t2:bool`--]);

val EQ_EXPAND = prove
   (--`!t1 t2. (t1 = t2) = ((t1 /\ t2) \/ (~t1 /\ ~t2))`--,
      TAUT_TAC [--`t1:bool`--, --`t2:bool`--]);

val COND_RATOR = prove
   (--`!b (f:'a->'b) g x. (b => f | g) x = (b => f x | g x)`--,
      TAUT_TAC [--`b:bool`--]);

val COND_RAND = prove
   (--`!(f:'a->'b) b x y. f (b => x | y) = (b => f x | f y)`--,
      TAUT_TAC [--`b:bool`--]);

val COND_ABS = prove
   (--`!b (f:'a->'b) g. (\x. (b => f(x) | g(x))) = (b => f | g)`--,
      TAUT_TAC [--`b:bool`--]);

val COND_EXPAND = prove
   (--`!b t1 t2. (b => t1 | t2) = ((~b \/ t1) /\ (b \/ t2))`--,
      TAUT_TAC [--`b:bool`--, --`t1:bool`--, --`t2:bool`--]);

end; (* Taut_thms *)
