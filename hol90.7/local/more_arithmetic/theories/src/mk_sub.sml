
(*===========================================================================*)
(*                                                                           *)
(*   FILE:         mk_sub.sml                                                *)
(*   EDITOR:       Paul Curzon                                               *)
(*   DATE:         July 1991                                                 *)
(*   DESCRIPTION : Theorems dealing with substraction 	   	             *)
(*                                                                           *)
(*===========================================================================*)


(*================================  HISTORY  ================================*)
(*									     *)
(*   This file is based on the theories of 				     *)
(*                                                                           *)
(*   Richard J.Boulton							     *)
(*   Rachel Cardell-Oliver						     *)
(*   Paul Curzon							     *)
(*   Elsa L Gunter							     *)
(*   Wim Ploegaerts							     *)
(*                                                                           *)
(*===========================================================================*)
(*===========================================================================*)
(*                                                                           *)
(*  DEPENDANCIES :                                                           *)
(*                                                                           *)
(*      suc                                 for theorems about SUC           *)
(*      add                                 for theorems about addition      *)
(*      zero_ineq                           for theorems about 0             *)
(*      ineq_conv                           for ineq conversions             *)
(*                                                                           *)
(*===========================================================================*)

(*
val path = 
   (!Globals.HOLdir)^"library/more_arithmetic/theories/"^Globals.theory_file_type^"/"
*)

val path = 
   "../"^Globals.theory_file_type^"/"

val _ = theory_path := path::(!theory_path);


local
fun delete_theory name = 
    System.system("/bin/rm -f "^name^".thms "^name^".holsig")
in
  val _ = delete_theory (path^"sub")
end;


new_theory "sub";

new_parent "add";
new_parent "zero_ineq";


local
fun use_lib_code s =
(*   let val p = (!Globals.HOLdir)^"library/more_arithmetic/src/" *)
   let val p = "../../src/" 
   in  use (p^s^".sig"); 
       use (p^s^".sml")
   end;
in
   val _ =   use_lib_code "ineq_conv"
end;
open Ineq_conv;



val NOT_EQ_0 = theorem "zero_ineq" "NOT_EQ_0";
val SUC_0 = theorem "suc" "SUC_0";
val ADD_MONO_LESS = theorem "add" "ADD_MONO_LESS";
val LESS_LESS_MONO = theorem "add" "LESS_LESS_MONO";
val ADDL_GREATER_EQ = theorem "add" "ADDL_GREATER_EQ";

val NOT_LESS_0 = theorem "prim_rec" "NOT_LESS_0";
val SUB_MONO_EQ = theorem "arithmetic" "SUB_MONO_EQ";
val PRE = theorem "prim_rec" "PRE";
val SUB = definition "arithmetic" "SUB";
val LESS_SUC_NOT = theorem "arithmetic" "LESS_SUC_NOT";
val ADD_CLAUSES = theorem "arithmetic" "ADD_CLAUSES";
val LESS_MONO_ADD_EQ = theorem "arithmetic" "LESS_MONO_ADD_EQ";
val SUB_ADD = theorem "arithmetic" "SUB_ADD";
val ADD_SYM = theorem "arithmetic" "ADD_SYM";
val SUB_LESS_EQ = theorem "arithmetic" "SUB_LESS_EQ";
val LESS_IMP_LESS_OR_EQ = theorem "arithmetic" "LESS_IMP_LESS_OR_EQ";
val SUB_0 = theorem "arithmetic" "SUB_0";
val SUB_EQ_0 = theorem "arithmetic" "SUB_EQ_0";
val NOT_LESS = theorem "arithmetic" "NOT_LESS";
val ADD = definition "arithmetic" "ADD";
val GREATER_EQ = theorem "arithmetic" "GREATER_EQ";
val LESS_EQ_MONO_ADD_EQ = theorem "arithmetic" "LESS_EQ_MONO_ADD_EQ";
val LESS_EQ_ANTISYM = theorem "arithmetic" "LESS_EQ_ANTISYM";
val ADD1 = theorem "arithmetic" "ADD1";
val LESS_THM = theorem "prim_rec" "LESS_THM";
val LESS_OR_EQ = definition "arithmetic" "LESS_OR_EQ";
val SUC_SUB1 = theorem "arithmetic" "SUC_SUB1";
val LESS_SUC = theorem "prim_rec" "LESS_SUC";
val PRE_SUB1 = theorem "arithmetic" "PRE_SUB1";
val LESS_REFL = theorem "prim_rec" "LESS_REFL";
val LESS_0 = theorem "prim_rec" "LESS_0";
val LESS_MONO_EQ = theorem "arithmetic" "LESS_MONO_EQ";
val LESS_OR = theorem "arithmetic" "LESS_OR";
val SUB_PLUS = theorem "arithmetic" "SUB_PLUS";
val ADD_SUB = theorem "arithmetic" "ADD_SUB";
val LESS_MONO_ADD = theorem "arithmetic" "LESS_MONO_ADD";
val GREATER = definition "arithmetic" "GREATER";
val NOT_LESS_EQUAL = theorem "arithmetic" "NOT_LESS_EQUAL";
val LESS_ANTISYM = theorem "arithmetic" "LESS_ANTISYM";
val LESS_EQ_ADD = theorem "arithmetic" "LESS_EQ_ADD";
val LESS_EQ_LESS_TRANS = theorem "arithmetic" "LESS_EQ_LESS_TRANS";
val LESS_EQ_TRANS = theorem "arithmetic" "LESS_EQ_TRANS";
val SUB_LESS_OR = theorem "arithmetic" "SUB_LESS_OR";
val OR_LESS = theorem "arithmetic" "OR_LESS";
val ZERO_LESS_EQ = theorem "arithmetic" "ZERO_LESS_EQ";
val LESS_EQ_MONO = theorem "arithmetic" "LESS_EQ_MONO";
val EQ_MONO_ADD_EQ = theorem "arithmetic" "EQ_MONO_ADD_EQ";
val ADD_ASSOC = theorem "arithmetic" "ADD_ASSOC";
val ADD_EQ_SUB = theorem "arithmetic" "ADD_EQ_SUB";
val LESS_0_CASES = theorem "arithmetic" "LESS_0_CASES";
val LESS_EQ_REFL = theorem "arithmetic" "LESS_EQ_REFL";

(*===========================================================================*)
(*									     *)
(* 		     Theorems dealing with subtraction			     *)
(*									     *)
(*===========================================================================*)

(*<WP>*)
val SUB_SUC_PRE_SUB = store_thm (
  "SUB_SUC_PRE_SUB",
  (--`! n m . (0 < n) ==> (n - (SUC m) = (PRE n) - m)`--),
  INDUCT_TAC THEN
  REWRITE_TAC [NOT_LESS_0,SUB_MONO_EQ,PRE]
);

(*--------------------------------------------------------------------------*)

(*<WP>*)
val ADD_SUC = SYM (el 4 (CONJUNCTS ADD_CLAUSES));

(*<WP>*)
val SUB_SUC = store_thm (
  "SUB_SUC",
   (--`! k m .  (m < k ) ==> ( k - m = SUC (k - SUC m) ) `--),
  REPEAT GEN_TAC THEN
  SUBST_TAC [SYM (SPECL [(--`k:num`--),(--`m:num`--)] SUB_MONO_EQ)] THEN
  DISCH_THEN (fn thm =>  
               let val thm' = MATCH_MP  LESS_SUC_NOT thm in
               ACCEPT_TAC (REWRITE_RULE [thm'] 
                      (SPECL [(--`k:num`--),(--`SUC m`--)] (CONJUNCT2 SUB)))
               end)
);

(*--------------------------------------------------------------------------*)

(*<ELG>*)
val SUB_LESS_TO_LESS_ADDR = store_thm("SUB_LESS_TO_LESS_ADDR",
(--`!m n p.((p<=m)==>(((m-p)<n)=(m<(n+p))))`--),
((REPEAT GEN_TAC) THEN
 DISCH_TAC THEN
 (REWRITE_TAC
  [(SYM(SPECL[(--`m-p`--),(--`n:num`--),(--`p:num`--)]LESS_MONO_ADD_EQ)),
   (UNDISCH_ALL(SPECL[(--`m:num`--),(--`p:num`--)]SUB_ADD))])));

(*SUB_LESS_TO_LESS_ADDR = 
 |- !m:num n:num p:num. p <= m ==> ((m - p) < n = m < (n + p))*)

(*--------------------------------------------------------------------------*)

(*<ELG>*)

val SUB_LESS_TO_LESS_ADDL = store_thm("SUB_LESS_TO_LESS_ADDL",
(--`!m n p.((n<=m)==>(((m-n)<p)=(m<(n+p))))`--),
((REPEAT GEN_TAC) THEN
 (PURE_ONCE_REWRITE_TAC[ADD_SYM]) THEN
 (ACCEPT_TAC (SPECL[(--`m:num`--),(--`p:num`--),(--`n:num`--)]SUB_LESS_TO_LESS_ADDR))));


(*SUB_LESS_TO_LESS_ADDL = 
 |- !m:num n:num p:num. n <= m ==> ((m - n) < p = m < (n + p))*)
(*--------------------------------------------------------------------------*)

(*<ELG>*)

(* This theorem could be strengthened, see SUB_LEFT_LESS     [RJB 92.09.29] *)
val LESS_SUB_TO_ADDR_LESS = store_thm("LESS_SUB_TO_ADDR_LESS",
(--`!m n p.((p<=m)==>((n<(m-p))=(n+p)<m))`--),
((REPEAT GEN_TAC) THEN
 DISCH_TAC THEN
 (REWRITE_TAC
  [(SYM(SPECL[(--`n:num`--),(--`m-p`--),(--`p:num`--)]LESS_MONO_ADD_EQ)),
   (UNDISCH_ALL(SPECL[(--`m:num`--),(--`p:num`--)] SUB_ADD))])));

(*LESS_SUB_TO_ADDR_LESS = 
 |- !m:num n:num p:num. p <= m ==> (n < (m - p) = (n + p) < m)*)


(*--------------------------------------------------------------------------*)

(*<ELG>*)
val LESS_SUB_TO_ADDL_LESS = store_thm("LESS_SUB_TO_ADDL_LESS",
(--`!m n p.((n<=m)==>((p<(m-n))=((n+p)<m)))`--),
((REPEAT GEN_TAC) THEN
 (PURE_ONCE_REWRITE_TAC[ADD_SYM]) THEN
 (ACCEPT_TAC (SPECL[(--`m:num`--),(--`p:num`--),(--`n:num`--)]LESS_SUB_TO_ADDR_LESS))));

(*LESS_SUB_TO_ADDL_LESS = 
 |- !m:num n:num p:num. n <= m ==> (p < (m - n) = (n + p) < m)*)

(*--------------------------------------------------------------------------*)

(*<PC>*)

val SUC_SUB = store_thm ("SUC_SUB",
(--`!m n.(((m<n)==>(((SUC m)-n)=0))/\(~(m<n)==>(((SUC m)-n)=SUC(m-n))))`--),
((REPEAT GEN_TAC) THEN
 (ASM_CASES_TAC (--`m<n`--)) THEN
 (ASM_REWRITE_TAC[SUB])));


(*SUC_SUB = 
 |- !m:num n:num.
     (m < n ==> ((SUC m) - n = 0)) /\
     (~m < n ==> ((SUC m) - n = SUC(m - n)))*)


(*---------------------------------------------------------------------------*)

(*<WP>*)

val LESS_SUB_BOUND = prove
  ((--`!k l . (k < l) ==> ((l - k) <= l)`--),
   REWRITE_TAC[SUB_LESS_EQ]
);

val SUB_SUB_ID = store_thm (
  "SUB_SUB_ID",
  (--`!k l . (l < k) ==> (k - (k - l) = l)`--),
  REPEAT GEN_TAC THEN 
  DISCH_THEN (fn thm =>
      CONV_TAC ((NUM_EQ_PLUS_CONV (--`k-l`--) ) THENC
                (RAND_CONV (ONCE_DEPTH_CONV (REWR_CONV ADD_SYM)))) THEN
      MAP_EVERY  SUBST1_TAC  (map (fn t => MATCH_MP SUB_ADD t)
                     [MATCH_MP LESS_SUB_BOUND thm,
                      MATCH_MP LESS_IMP_LESS_OR_EQ thm])) THEN
  REFL_TAC
);

(*---------------------------------------------------------------------------*)

(*<WP>*)
val LESS_SUB_IMP_INV = store_thm (
  "LESS_SUB_IMP_INV",
  (--`!k l . (0 < k - l) ==> (l < k)`--),
  REPEAT GEN_TAC THEN CONV_TAC CONTRAPOS_CONV THEN 
  REWRITE_TAC [NOT_LESS,GSYM SUB_EQ_0,SUB_0]
);

(*===========================================================================*)
(*									     *)
(* 				Simplications				     *)
(*									     *)
(*===========================================================================*)

(*<ELG>*)

val LESS_EQ_ADD_SUB1 =store_thm ("LESS_EQ_ADD_SUB1",
(--`!m n p.((p <= n) ==> (m+(n-p)=(m+n)-p))`--),
((REPEAT GEN_TAC) THEN (SPEC_TAC ((--`m:num`--), (--`m:num`--))) THEN INDUCT_TAC THENL
 [(REWRITE_TAC [(CONJUNCT1 ADD)]),
  ((REWRITE_TAC [(CONJUNCT2 ADD)]) THEN
   DISCH_TAC THEN
   (ASSUME_TAC (SPECL [(--`p:num`--),(--`n:num`--),(--`m:num`--)]
                      ADDL_GREATER_EQ)) THEN
   (ASSUME_TAC (snd(EQ_IMP_RULE
                 (SPECL [(--`m+n`--),(--`p:num`--)] NOT_LESS)))) THEN
   RES_TAC THEN RES_TAC THEN
   (ASM_REWRITE_TAC [(UNDISCH_ALL(CONJUNCT2(SPECL[(--`m+n`--),(--`p:num`--)]
                     SUC_SUB)))])
  )]));

(*LESS_EQ_ADD_SUB1 =
      |- !m:num n:num p:num. p <= n ==> (m + (n - p) = (m + n) - p)*)


(*--------------------------------------------------------------------------*)

(*<ELG>*)

val LESS_EQ_SUB_ADD=store_thm ("LESS_EQ_SUB_ADD",
(--`!m n p. p <= m ==> ((m-p)+n = (m+n)-p)`--),
((REPEAT GEN_TAC) THEN
 (PURE_ONCE_REWRITE_TAC[ADD_SYM]) THEN
 (ACCEPT_TAC (SPECL[(--`n:num`--),(--`m:num`--),(--`p:num`--)]LESS_EQ_ADD_SUB1))));

(*LESS_EQ_SUB_ADD =
    |- !m:num n:num p:num. p <= m ==> ((m - p) + n = (m + n) - p)*)

(*===========================================================================*)
(*                                                                           *)
(*   AUTHOR:       Paul Curzon                                               *)
(*   DATE:         June 1991                                                 *)
(*                                                                           *)
(*===========================================================================*)

(* See also SUB_LESS_TO_LESS_ADDL and SUB_LESS_TO_LESS_ADDR *)

val GREATER_EQ_SUB_LESS_TO_ADD = store_thm (
  "GREATER_EQ_SUB_LESS_TO_ADD",
  (--`!n m p. (p >= n) ==> (((p - n) < m) = (p < (n + m)))`--),
 (REWRITE_TAC
    [SYM (SPEC (--`n:num`--) 
        (SPEC (--`m:num`--) (SPEC (--`p - n`--) LESS_MONO_ADD_EQ)))]) THEN
 (REPEAT STRIP_TAC) THEN
 (POP_ASSUM (fn th => ASSUME_TAC
    (MP  (SPEC (--`n:num`--) (SPEC (--`p:num`--) SUB_ADD)) 
          (REWRITE_RULE[SPEC (--`n:num`--) (SPEC (--`p:num`--) GREATER_EQ)]
                       th)))) THEN
 (SUBST_TAC[SPEC_ALL ADD_SYM]) THEN
 (ASM_REWRITE_TAC[]));

(*========================================================================== *)
val SUB_GREATER_EQ_ADD = store_thm (
  "SUB_GREATER_EQ_ADD",
  (--`!n m p. (p >= n) ==> (((p - n) >= m) = (p >= (n + m)))`--),
 (REWRITE_TAC[
      SYM (SPEC (--`n:num`--) (SPEC (--`p-n`--) (SPEC (--`m:num`--) 
           (REWRITE_RULE[GSYM GREATER_EQ] LESS_EQ_MONO_ADD_EQ))))]) THEN
 (REPEAT STRIP_TAC) THEN
 (POP_ASSUM (fn th => ASSUME_TAC
     (MP  (SPEC (--`n:num`--) (SPEC (--`p:num`--) SUB_ADD)) 
          (REWRITE_RULE[SPEC (--`n:num`--) (SPEC (--`p:num`--) GREATER_EQ)]
                       th)))) THEN
 (SUBST_TAC[(SPEC_ALL ADD_SYM)]) THEN
 (ASM_REWRITE_TAC[]));



(*===========================================================================*)
(* |- !n m p. n <= p ==> (m <= (p - n) = (n + m) <= p) *)


val SUB_LE_ADD =  save_thm("SUB_LE_ADD",
         REWRITE_RULE[GREATER_EQ] SUB_GREATER_EQ_ADD);
(*========================================================================== *)
val NOT_SUB_0 = store_thm ("NOT_SUB_0",
   (--`!m n . m < n ==> ~(n - m = 0)`--),
 (REWRITE_TAC[SUB_EQ_0]) THEN
 (REPEAT STRIP_TAC) THEN
 (IMP_RES_TAC LESS_EQ_ANTISYM));

(*===========================================================================*)
val  NOT_0_SUB = store_thm( "NOT_0_SUB",
    (--`! m n  . (~ (m - n = 0)) ==> ~ (m = 0)`--),
 (REPEAT STRIP_TAC) THEN
 (CONTR_TAC 
     (REWRITE_RULE [ASSUME (--`m = 0`--), SUB_0]
                   (ASSUME (--`~(m - n = 0)`--)) ))
);


(* ==========================================================================*)
(* see also PRE_K_K *)

val SUB_1_LESS = store_thm("SUB_1_LESS",
     (--`! m n . ((~ (m = 0)) /\ (m < SUC n)) ==> ((m - 1) < n)`--),

 (REPEAT STRIP_TAC) THEN
 (REWRITE_TAC[
      (ONCE_REWRITE_RULE[ADD_SYM]
           (REWRITE_RULE [ADD1] (ASSUME (--`m < SUC n`--)))),
      MATCH_MP (SPECL[(--`1`--),(--`n:num`--)] GREATER_EQ_SUB_LESS_TO_ADD)
               (MATCH_MP NOT_EQ_0 (ASSUME (--`~ (m = 0)`--)))]));

(* ==========================================================================*)
val  SUB_1_LESS_EQ = store_thm("SUB_1_LESS_EQ",
   (--`! m n. (m < n) ==> ((n - 1) >= m)`--),

 GEN_TAC THEN
 INDUCT_TAC THENL
 [
 (REWRITE_TAC[SUB_0,GREATER_EQ,LESS_IMP_LESS_OR_EQ]),

 (REPEAT STRIP_TAC) THEN
 (REWRITE_TAC[SUC_SUB1,GREATER_EQ,LESS_OR_EQ]) THEN
 (DISJ_CASES_TAC (REWRITE_RULE[LESS_THM](ASSUME (--`m < SUC n`--)) )) THEN
 (ASM_REWRITE_TAC[])]);


(*========================================================================== *)
val ADD_LESS_EQ_SUB = save_thm("ADD_LESS_EQ_SUB",
   GSYM (REWRITE_RULE[GREATER_EQ] SUB_GREATER_EQ_ADD));


(*===========================================================================*)
(*                                                                           *)
(* AUTHOR        : R.J.Boulton                                               *)
(* DATE          : 1990                                                      *)
(*                                                                           *)
(*===========================================================================*)



val PRE_SUB_SUC = store_thm("PRE_SUB_SUC",
  (--`!m n. (m < n) ==> (PRE (n - m) = (n - (SUC m)))`--),
   GEN_TAC THEN
   INDUCT_TAC THENL
   [REWRITE_TAC [SUB_0,PRE],
    STRIP_TAC THEN
    REWRITE_TAC [SUB_MONO_EQ] THEN
    REWRITE_TAC [SUB] THEN
    IMP_RES_TAC (REWRITE_RULE [] (CONTRAPOS (SPEC_ALL LESS_SUC_NOT))) THEN
    ASM_REWRITE_TAC [PRE]]);

(*===========================================================================*)
(*                                                                           *)
(* AUTHOR        : Rachel Cardell-Oliver                                     *)
(* DATE          : 1990                                                      *)
(*                                                                           *)
(*===========================================================================*)


val LESS_PRE = store_thm("LESS_PRE",
 (--`!i m:num. ( i < (m-1) ) ==> (i < m)`--),
 GEN_TAC THEN INDUCT_TAC THEN
 REWRITE_TAC[SUB_0,NOT_LESS_0,SYM (SPEC_ALL PRE_SUB1),PRE,LESS_SUC]);



val PRE_LESS_LESS_SUC = store_thm( "PRE_LESS_LESS_SUC",
 (--`!i:num. !m:num.  ( i<(m-1)  /\  0<m ) ==> (i+1)<m `--) ,
 GEN_TAC THEN INDUCT_TAC THEN
 REWRITE_TAC[LESS_REFL,LESS_0,SYM(SPEC_ALL PRE_SUB1),
               SYM(SPEC_ALL ADD1),PRE,LESS_MONO_EQ] );

val SUB_PRE_SUB_1 = 
store_thm(
  "SUB_PRE_SUB_1",
  (--`!a b:num.(0<b) ==> (((a-(PRE b))-1) = (a-b))`--),
  REPEAT STRIP_TAC THEN
  REWRITE_TAC [(SYM (SPEC_ALL SUB_PLUS)),PRE_SUB1] THEN
  IMP_RES_TAC LESS_OR THEN
  POP_ASSUM (ASSUME_TAC o (REWRITE_RULE [SYM SUC_0])) THEN
  IMP_RES_TAC SUB_ADD THEN
  ASM_REWRITE_TAC[] );


(*less_sub_imp_sum_less --> LESS_SUB_IMP_SUM_LESS PC*)
val LESS_SUB_IMP_SUM_LESS = store_thm("LESS_SUB_IMP_SUM_LESS",
 (--`!i:num. !m:num.  ( i<(m-1)  /\  1<m ) ==> (i+1)<m `--) ,
  REPEAT STRIP_TAC THEN
  ASSUME_TAC
      (SPECL [(--`i:num`--),(--`m-1`--),(--`1`--)] LESS_MONO_ADD_EQ) THEN
  IMP_RES_TAC LESS_IMP_LESS_OR_EQ THEN
  IMP_RES_TAC SUB_ADD THEN
  POP_ASSUM(fn thm => ONCE_REWRITE_TAC[SYM thm]) THEN
  ASM_REWRITE_TAC[]  );


val ADD_SUB_SYM = save_thm("ADD_SUB_SYM",
    ONCE_REWRITE_RULE[ADD_SYM] ADD_SUB);

val SUB_ADD_SELF = store_thm("SUB_ADD_SELF",
  (--`!m n. ~(m<n) ==> ( ((m-n)+n)=m )`--) ,
   REWRITE_TAC[NOT_LESS,SUB_ADD]  );




val SMALLER_SUM = store_thm("SMALLER_SUM",
  (--`!m n p. (m<p /\ n<p) ==> ~( ((m+n)-p) > m)`--),
  REPEAT STRIP_TAC THEN
  POP_ASSUM (ASSUME_TAC o (REWRITE_RULE [GREATER])) THEN
  ASM_CASES_TAC (--`(m+n)<=p`--) THENL
  [ POP_ASSUM (ASSUME_TAC o (REWRITE_RULE [GSYM SUB_EQ_0])) THEN
    UNDISCH_TAC (--`m < ((m + n) - p)`--) THEN ASM_REWRITE_TAC[NOT_LESS_0] ,

    POP_ASSUM(ASSUME_TAC o (REWRITE_RULE [NOT_LESS_EQUAL])) THEN
    IMP_RES_TAC (SPEC (--`p:num`--) (SPEC (--`(m+n)-p`--) (SPEC (--`m:num`--) 
      LESS_MONO_ADD))) THEN
    POP_ASSUM(fn thm => MP_TAC thm) THEN
    IMP_RES_TAC
       (SPEC (--`m+n`--) (SPEC (--`p:num`--) LESS_IMP_LESS_OR_EQ)) THEN
    IMP_RES_TAC (SPEC (--`p:num`--) (SPEC (--`m+n`--) SUB_ADD)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    POP_ASSUM (ASSUME_TAC o (REWRITE_RULE [ADD_MONO_LESS])) THEN
    UNDISCH_TAC (--`n<p`--) THEN
    UNDISCH_TAC (--`p<n`--) THEN
    REWRITE_TAC [IMP_DISJ_THM,NOT_CLAUSES,
        (SYM (CONJUNCT1 (SPEC_ALL DE_MORGAN_THM))),LESS_ANTISYM] ] );




val NOT_LESS_SUB = store_thm("NOT_LESS_SUB",
  (--`!m n. ~( m < (m-n) )`--)  ,
   REPEAT GEN_TAC THEN
   ASM_CASES_TAC (--`m<=n`--) THENL
   [ POP_ASSUM(fn thm =>
                   REWRITE_TAC[REWRITE_RULE[GSYM SUB_EQ_0]thm,NOT_LESS_0]),
     POP_ASSUM(ASSUME_TAC o REWRITE_RULE[NOT_LESS_EQUAL]) THEN
     IMP_RES_TAC LESS_IMP_LESS_OR_EQ THEN
     IMP_RES_TAC SUB_ADD THEN
     REWRITE_TAC[NOT_LESS] THEN
     ONCE_REWRITE_TAC[GSYM(SPECL[(--`m-n`--),(--`m:num`--),(--`n:num`--)]
                      LESS_EQ_MONO_ADD_EQ)]
     THEN ASM_REWRITE_TAC[LESS_EQ_ADD] ] );



val SUB_BOTH_SIDES = store_thm("SUB_BOTH_SIDES",
  (--`!m n p. (m=n) ==> ( (m-p)=(n-p) )`--),
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] );

val SUB_LESS_BOTH_SIDES = store_thm("SUB_LESS_BOTH_SIDES",
  (--`!m n p. ((p<=m) /\ (m<n)) ==> ( (m-p) < (n-p) )`--),
  REPEAT STRIP_TAC THEN
  IMP_RES_TAC SUB_ADD THEN
  ASM_REWRITE_TAC[
    SYM(SPEC (--`p:num`--)
           (SPEC (--`n-p`--) (SPEC (--`m-p`--) LESS_MONO_ADD_EQ)))] THEN
  IMP_RES_TAC LESS_EQ_LESS_TRANS THEN
  IMP_RES_TAC LESS_IMP_LESS_OR_EQ THEN
  IMP_RES_TAC SUB_ADD THEN
  ASM_REWRITE_TAC[] );


val LESS_TWICE_IMP_LESS_SUB =store_thm("LESS_TWICE_IMP_LESS_SUB",
  (--`!a:num. !b:num. !m:num.
     ( a < m /\ b < m /\ m<=(a+b) ) ==> ( ((a+b)-m) < m )`--) ,
   REPEAT STRIP_TAC THEN
   (ACCEPT_TAC
    (REWRITE_RULE [ADD_SUB_SYM]
     (MATCH_MP SUB_LESS_BOTH_SIDES
      (CONJ (ASSUME(--`m <= (a + b)`--))
         (MATCH_MP LESS_LESS_MONO 
            (CONJ (ASSUME(--`a < m`--))  (ASSUME(--`b < m`--)) ))))))
);



val SUB_LESS_EQ_SUB_SUC = store_thm("SUB_LESS_EQ_SUB_SUC",
 (--`!a b c n:num. 0<c /\  a<=(b-n) ==> ( (a-c) <= (b-SUC n) )`--),
REPEAT INDUCT_TAC THEN 
(let val th1 = (REWRITE_RULE [SYM (SPEC_ALL NOT_LESS_EQUAL)] LESS_0) in
  ASM_REWRITE_TAC[LESS_REFL,SUB_0,th1,LESS_0]end) THEN  
ASM_REWRITE_TAC[SUB_MONO_EQ,LESS_EQ_MONO,SUB_0,ZERO_LESS_EQ] THEN
STRIP_TAC THEN
(let val th2 = (REWRITE_RULE [NOT_LESS] NOT_LESS_SUB) in
  ASSUME_TAC (SPECL [(--`a:num`--),(--`c:num`--)] th2) end) THEN
IMP_RES_TAC LESS_EQ_TRANS THEN
IMP_RES_TAC OR_LESS THEN
IMP_RES_TAC SUB_LESS_OR THEN 
POP_ASSUM (ASSUME_TAC o REWRITE_RULE 
   [SYM (SPEC_ALL SUB_PLUS),SYM(SPEC_ALL ADD1)]) THEN
IMP_RES_TAC LESS_EQ_TRANS );


val SUB_EQ_SUB_ADD_SUB = store_thm("SUB_EQ_SUB_ADD_SUB",
  (--`!a b c. ( (a<=b) /\ (b<=c) )  ==> ( (c-a) = ( (c-b)+(b-a) ))`--),
  REPEAT STRIP_TAC THEN
  REWRITE_TAC 
    [(SYM (SPECL [(--`c-a`--),(--`(c-b)+(b-a)`--),(--`a:num`--)] EQ_MONO_ADD_EQ))] THEN
  IMP_RES_TAC LESS_EQ_TRANS THEN
  IMP_RES_TAC SUB_ADD THEN
  ASM_REWRITE_TAC [(SYM (SPEC_ALL ADD_ASSOC))]  );


val ADD_EQ_IMP_SUB_EQ =store_thm("ADD_EQ_IMP_SUB_EQ",
  (--`!a b c:num. (a=(b+c)) ==> ((a-b)=c)`--),
  ONCE_REWRITE_TAC[EQ_SYM_EQ] THEN
  REPEAT STRIP_TAC THEN
  MP_TAC (SPECL [(--`b:num`--),(--`c:num`--)] LESS_EQ_ADD) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN
  MP_TAC (SPECL [(--`c:num`--),(--`b:num`--),(--`a:num`--)] ADD_EQ_SUB) THEN
  ONCE_REWRITE_TAC[ADD_SYM] THEN
  ASM_REWRITE_TAC[] );


val SUB_GREATER_0 = store_thm("SUB_GREATER_0", 
  (--`!a b:num. a<b ==> ( (b-a)>0 )`--),
  REPEAT STRIP_TAC THEN
  POP_ASSUM (ASSUME_TAC o (REWRITE_RULE [
            (SYM (SPEC_ALL NOT_LESS_EQUAL))])) THEN
  DISJ_CASES_TAC (SPECL [(--`b-a`--)] LESS_0_CASES) THENL
  [ POP_ASSUM (ASSUME_TAC o ((REWRITE_RULE [SUB_EQ_0]) o SYM)) THEN 
    UNDISCH_TAC (--`b<=a`--) THEN
    ASM_REWRITE_TAC[] ,
    ASM_REWRITE_TAC[GREATER] ] );
 
val LESS_EQ_SUB_1 = store_thm("LESS_EQ_SUB_1",
  (--`!a b.  a<=b ==> ((a-1) <= (b-1))`--) ,
   REPEAT STRIP_TAC THEN
   POP_ASSUM (DISJ_CASES_TAC o (REWRITE_RULE [LESS_OR_EQ])) THENL
   [ IMP_RES_TAC SUB_LESS_OR THEN
     ASSUME_TAC 
       (REWRITE_RULE [NOT_LESS] (SPECL [(--`a:num`--),(--`1`--)] NOT_LESS_SUB)) THEN
     IMP_RES_TAC LESS_EQ_TRANS ,
     ASM_REWRITE_TAC[LESS_EQ_REFL] ] );


val SUB_LESS_EQ_SUB1  = store_thm("SUB_LESS_EQ_SUB1",
  (--`!x:num. x>0 ==> (!a:num. (a-x) <= (a-1))`--) ,
  REPEAT STRIP_TAC THEN
  POP_ASSUM (ASSUME_TAC o (REWRITE_RULE [GREATER])) THEN
  IMP_RES_TAC (SPECL [(--`a:num`--),(--`a:num`--),(--`x:num`--),(--`0`--)] SUB_LESS_EQ_SUB_SUC) THEN
  POP_ASSUM (ASSUME_TAC o 
     (REWRITE_RULE [SUB_0,LESS_EQ_REFL,(SYM SUC_0)])) THEN
  ASM_REWRITE_TAC[] );


export_theory();
close_theory();
