
(*===========================================================================*)
(*                                                                           *)
(*   FILE:         mk_add.sml                                                *)
(*   EDITOR:       Paul Curzon                                               *)
(*   DATE:         July 1991                                                 *)
(*   DESCRIPTION   : Theorems about addition      		             *)
(*                                                                           *)
(*===========================================================================*)


(*============================  HISTORY  ====================================*)
(*									     *)
(*   This file is based on the theories of 				     *)
(*                                                                           *)
(*   Rachel Cardell-Oliver						     *)
(*   Paul Curzon							     *)
(*   Elsa L Gunter							     *)
(*   Philippe Leveilley							     *)
(*   Wim Ploegaerts							     *)
(*                                                                           *)
(*===========================================================================*)

(*===========================================================================*)
(*                                                                           *)
(*  DEPENDANCIES :                                                           *)
(*                                                                           *)
(*      suc                                 for theorems about SUC           *)
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
  val _ = delete_theory (path^"add")
end;


new_theory "add";

new_parent "suc";

local
fun use_lib_code s =
(*   let val p = (!Globals.HOLdir)^"library/more_arithmetic/src/" *)
   let val p = "../../src/" 
   in  compile (p^s^".sig"); 
       compile (p^s^".sml")
   end;
in
  val _ =  use_lib_code "ineq_conv"
end;
open Ineq_conv;

val GREATER_EQ = theorem "arithmetic" "GREATER_EQ";
val GREATER_OR_EQ = definition "arithmetic" "GREATER_OR_EQ";
val GREATER = definition "arithmetic" "GREATER";
val ADD1 = theorem "arithmetic" "ADD1";
val LESS_EQ = theorem "arithmetic" "LESS_EQ";
val ADD_SYM = theorem "arithmetic" "ADD_SYM";
val LESS_EQ_MONO_ADD_EQ = theorem "arithmetic" "LESS_EQ_MONO_ADD_EQ";
val ADD = definition "arithmetic" "ADD";
val ZERO_LESS_EQ = theorem "arithmetic" "ZERO_LESS_EQ";
val ADD_ASSOC = theorem "arithmetic" "ADD_ASSOC";
val LESS_EQ_ADD = theorem "arithmetic" "LESS_EQ_ADD";
val LESS_TRANS = theorem "arithmetic" "LESS_TRANS";
val LESS_EQ_TRANS = theorem "arithmetic" "LESS_EQ_TRANS";
val LESS_SUC = theorem "prim_rec" "LESS_SUC";
val ADD_CLAUSES = theorem "arithmetic" "ADD_CLAUSES";
val NOT_LESS_0 = theorem "prim_rec" "NOT_LESS_0";
val NOT_LESS = theorem "arithmetic" "NOT_LESS";
val LESS_EQ_LESS_EQ_MONO = theorem "arithmetic" "LESS_EQ_LESS_EQ_MONO";
val LESS_MONO_ADD_EQ = theorem "arithmetic" "LESS_MONO_ADD_EQ";
val LESS_MONO_ADD = theorem "arithmetic" "LESS_MONO_ADD";
val LESS_OR_EQ = definition "arithmetic" "LESS_OR_EQ";
val LESS_REFL = theorem "prim_rec" "LESS_REFL";
val LESS_0 = theorem "prim_rec" "LESS_0";
val SUC_ID = theorem "prim_rec" "SUC_ID";
val LESS_NOT_EQ = theorem "prim_rec" "LESS_NOT_EQ";
val INV_SUC_EQ = theorem "prim_rec" "INV_SUC_EQ";
val LESS_EQ_LESS_TRANS = theorem "arithmetic" "LESS_EQ_LESS_TRANS";
val LESS_SUC_REFL = theorem "prim_rec" "LESS_SUC_REFL";
val LESS_IMP_LESS_OR_EQ = theorem "arithmetic" "LESS_IMP_LESS_OR_EQ";
val LESS_ADD_SUC = theorem "arithmetic" "LESS_ADD_SUC";

val SUC_0 = theorem "suc" "SUC_0";

(*--------------------------------------------------------------------------*)

(*<PL>*)
val LESS_LESS_EQ =
    store_thm ("LESS_LESS_EQ",
    	       (--`!a b. (a < b) = ((a + 1) <= b)`--),
	       REWRITE_TAC [SYM (SPEC_ALL ADD1), LESS_EQ]);


(*--------------------------------------------------------------------------*)

(*<PL>*)
val ADD_SUC_0 =
save_thm ("ADD_SUC_0",
	  (CONV_RULE (DEPTH_CONV num_CONV))
	  (REWRITE_RULE [SPECL [(--`m:num`--),(--`1`--)] ADD_SYM] ADD1));
(*--------------------------------------------------------------------------*)

(*<PL>*)
val LESS_EQ_MONO_ADD_EQ0 =
    save_thm ("LESS_EQ_MONO_ADD_EQ0",
	      GEN_ALL (SYM (SUBS [SPECL [(--`m:num`--),(--`p:num`--)] ADD_SYM,
                                  SPECL [(--`n:num`--),(--`p:num`--)] ADD_SYM]
                                 (SPEC_ALL LESS_EQ_MONO_ADD_EQ))));

(*--------------------------------------------------------------------------*)

(*<PL>*)
val LESS_EQ_MONO_ADD_EQ1 =
    save_thm ("LESS_EQ_MONO_ADD_EQ1",
	      GEN_ALL (REWRITE_RULE [ADD]
	                            (SPECL [(--`m:num`--),(--`0:num`--),(--`p:num`--)]
	                                   LESS_EQ_MONO_ADD_EQ)));


(*--------------------------------------------------------------------------*)

(*<PL>*)
val LESS_EQ_ADD1 =
    save_thm ("LESS_EQ_ADD1",
	      GEN_ALL (REWRITE_RULE [ADD,ZERO_LESS_EQ]
	                            (SPECL [(--`0:num`--),(--`n:num`--),(--`p:num`--)]
	                                   LESS_EQ_MONO_ADD_EQ)));

(*--------------------------------------------------------------------------*)

(*<PL>*)
val ADD_SYM_ASSOC =
    store_thm ("ADD_SYM_ASSOC",
	       (--`! a b c. a + (b + c) = b + (a + c)`--),
	       REPEAT GEN_TAC THEN
	       REWRITE_TAC [ADD_ASSOC] THEN
	       SUBST_TAC [SPECL [(--`a:num`--),(--`b:num`--)] ADD_SYM] THEN
	       REWRITE_TAC []);
(*--------------------------------------------------------------------------*)

(*<PL>*)
val LESS_EQ_SPLIT =
    save_thm ("LESS_EQ_SPLIT",
      GEN_ALL(
       (let val asm_thm = ASSUME (--`(m + n) <= p`--)
	in
	  (DISCH_ALL
	   (CONJ
	    (MP (SPECL [(--`n:num`--),(--`m+n`--),(--`p:num`--)] LESS_EQ_TRANS)
       		(CONJ (SUBS [SPECL [(--`n:num`--),(--`m:num`--)] ADD_SYM]
		            (SPECL [(--`n:num`--),(--`m:num`--)] LESS_EQ_ADD))
                      asm_thm))
	    (MP (SPECL [(--`m:num`--),(--`m+n`--),(--`p:num`--)] LESS_EQ_TRANS)
                (CONJ (SPEC_ALL LESS_EQ_ADD) asm_thm)) ))
        end)));
       
(*===========================================================================*)
(*									     *)
(* 			 inequalities in assumptions			     *)
(*									     *)
(*===========================================================================*)


(*<ELG>*)
val ADDL_GREATER = store_thm ("ADDL_GREATER",
(--`!m n p.m<n==>m<(p+n)`--),
(GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN DISCH_TAC THEN
 (ASM_REWRITE_TAC (CONJUNCTS ADD_CLAUSES)) THEN
 RES_TAC THEN
 (ASM_REWRITE_TAC[(UNDISCH_ALL(SPECL [(--`m:num`--),(--`(p+n)`--)] LESS_SUC))])));

(*ADDL_GREATER = |- !m:num n:num p:num. m < n ==> m < (p + n)*)

(*--------------------------------------------------------------------------*)

(*<ELG>*)
val ADDL_GREATER_EQ = store_thm ("ADDL_GREATER_EQ",
(--`!m n p. m <= n ==> m <= p+n`--),
((REPEAT GEN_TAC) THEN DISCH_TAC THEN
 (ASSUME_TAC (REWRITE_RULE [(CONJUNCT1(CONJUNCT2 ADD_CLAUSES))]
  (SPECL [(--`m:num`--),(--`0`--),(--`n:num`--),(--`p:num`--)]
        LESS_EQ_LESS_EQ_MONO))) THEN
 (ASSUME_TAC (REWRITE_RULE [(SPECL [(--`m:num`--),(--`n:num`--)] NOT_LESS)]
  (SPEC (--`p:num`--) NOT_LESS_0))) THEN RES_TAC THEN
 (SUBST_TAC [(SPECL [(--`p:num`--),(--`n:num`--)] ADD_SYM)]) THEN
 (FIRST_ASSUM ACCEPT_TAC)));

(*ADDL_GREATER_EQ = |- !m:num n:num p:num. m <= n ==> m <= (p + n)*)

(*--------------------------------------------------------------------------*)

(*<ELG>*)
val ADDR_GREATER = save_thm("ADDR_GREATER",
    PURE_ONCE_REWRITE_RULE[ADD_SYM]ADDL_GREATER);

(*ADDR_GREATER = |- !m:num n:num p:num. m < n ==> m < (n + p)*)


(*--------------------------------------------------------------------------*)

(*<ELG>*)
val ADDR_GREATER_EQ = save_thm("ADDR_GREATER_EQ",
    PURE_ONCE_REWRITE_RULE[ADD_SYM]ADDL_GREATER_EQ);

(*ADDR_GREATER_EQ = |- !m:num n:num p:num. m <= n ==> m <= (n + p)*)


(*--------------------------------------------------------------------------*)

(*<WP>*)
val LESS_LESS_MONO = store_thm ("LESS_LESS_MONO",
  (--`!m n p q . ((m < p) /\ (n < q)) ==> ((m + n) < (p + q))`--),
  REPEAT GEN_TAC THEN
  DISCH_THEN (fn t => 
    let val [t1,t2] = CONJUNCTS t in
      ASSUME_TAC (CONV_RULE (NUM_LESS_PLUS_CONV (--`q:num`--)) t1) THEN
      ASSUME_TAC 
      (SPEC (--`m:num`--) 
       (GEN_ALL 
	(CONV_RULE ((NUM_LESS_PLUS_CONV (--`r:num`--)) THENC
		    (ONCE_DEPTH_CONV (REWR_CONV ADD_SYM))) t2)))end)
      THEN
      IMP_RES_TAC LESS_TRANS
);


(*<WP>*) 
val LESS_LESS_EQ_MONO = store_thm (
  "LESS_LESS_EQ_MONO",
   (--`(!m n p q . ((m < p) /\ (n <= q)) ==> ((m + n) < (p + q))) /\ 
    (!m n p q . ((m <= p) /\ (n < q)) ==> ((m + n) < (p + q)))`--),
  REWRITE_TAC [LESS_OR_EQ,DE_MORGAN_THM] THEN REPEAT STRIP_TAC THEN
  IMP_RES_TAC LESS_LESS_MONO THEN
  FIRST_ASSUM (fn t => (SUBST_TAC [t] handle ? => NO_TAC)) THEN
  ((REWRITE_TAC [LESS_MONO_ADD_EQ] THEN
    FIRST_ASSUM ACCEPT_TAC) ORELSE
   (ONCE_REWRITE_TAC [ADD_SYM] THEN
    REWRITE_TAC [LESS_MONO_ADD_EQ] THEN 
    FIRST_ASSUM ACCEPT_TAC))
);



(*--------------------------------------------------------------------------*)

(*<WP>*)
val ADD_EQ_LESS_IMP_LESS = store_thm (
  "ADD_EQ_LESS_IMP_LESS",
  (--` !n m k l . ((k + m = l + n) /\ (k < l)) ==> (n < m)`--),
  REPEAT GEN_TAC THEN 
  ASM_CASES_TAC (--`n < m`--) THEN
  POP_ASSUM (fn t => 
        REWRITE_TAC [t] THEN
        DISCH_THEN (fn thm => 
          let val [t1,t2] = CONJUNCTS thm in
           MP_TAC
              (MATCH_MP (CONJUNCT1 LESS_LESS_EQ_MONO)
                (CONJ t2 (REWRITE_RULE [NOT_LESS] t))) THEN
           REWRITE_TAC [t1,LESS_REFL]
          end))
);







(*===========================================================================*)
(*                                                                           *)
(*   AUTHOR:       Paul Curzon                                               *)
(*   DATE:         June 1991                                                 *)
(*                                                                           *)
(*===========================================================================*)



(*===========================================================================*)

val LESS_ADD_ASSOC = save_thm("LESS_ADD_ASSOC",
  (GEN_ALL (REWRITE_RULE
     [SYM (SPEC (--`d:num`--) 
            (SPEC (--`c:num`--) (SPEC (--`b:num`--) ADD_ASSOC)))]
      (SPEC (--`d:num`--)
         (SPEC (--`b+c`--) (SPEC (--`a:num`--)  ADDR_GREATER))))));

(* LESS_ADD_ASSOC |- !a b c d. a < (b + c) ==> a < (b + (c + d)) *)
(*===========================================================================*)
(* |- !m n p. p >= (m + n) ==> p >= m /\ p >= n *)

val GREATER_EQ_SPLIT = save_thm("GREATER_EQ_SPLIT",
    REWRITE_RULE [GSYM GREATER_EQ] LESS_EQ_SPLIT);

(*===========================================================================*)

val LESS_TRANS_ADD = store_thm("LESS_TRANS_ADD",
(--`!m n p q. 
   (m < n + p) /\ (p < q) ==> (m < n + q)`--),

 (REPEAT STRIP_TAC) THEN
 (IMP_RES_TAC  LESS_MONO_ADD) THEN
 (REWRITE_TAC[
  MATCH_MP (SPECL[(--`m:num`--),(--`n+p`--), (--`n+q`--)]LESS_TRANS)
  (CONJ (ASSUME (--`m < n + p`--))
        (ONCE_REWRITE_RULE[ADD_SYM]
           (SPEC (--`n:num`--) (ASSUME (--`!p'. (p + p') < (q + p')`--)))))]));


(*===========================================================================*)
(*                                                                           *)
(* AUTHOR        : Rachel Cardell-Oliver                                     *)
(* DATE          : 1990                                                      *)
(*                                                                           *)
(*===========================================================================*)


val ADD_GREATER_EQ = 
store_thm(
  "ADD_GREATER_EQ",
  (--`!m n. (m+n) >= m`--),
  ASM_REWRITE_TAC[GREATER_OR_EQ,GREATER] THEN
  ONCE_REWRITE_TAC[EQ_SYM_EQ] THEN
  ASM_REWRITE_TAC[(SYM (SPEC_ALL LESS_OR_EQ)),LESS_EQ_ADD] );


val ADD_MONO_LESS = store_thm("ADD_MONO_LESS",
  (--`!m n p. (m+p) < (m+n) = (p<n)`--),
  REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC [ADD_SYM] THEN
  ONCE_REWRITE_TAC [LESS_MONO_ADD_EQ] THEN
  REWRITE_TAC[] );


(*not_1_even --> NOT_1_TWICE  PC*)

val NOT_1_TWICE =
store_thm(
 "NOT_1_TWICE",
 (--`!n:num. ~(1 = n+n )`--) ,
 INDUCT_TAC THENL
  [ REWRITE_TAC[ADD_CLAUSES,SUC_0,SUC_ID] ,
    REWRITE_TAC[ADD,SUC_0,INV_SUC_EQ,ADD_CLAUSES] THEN
    ASSUME_TAC (SPEC (--`n+n`--) LESS_0) THEN
    IMP_RES_TAC LESS_NOT_EQ ]);

val SUM_LESS = store_thm( "SUM_LESS",
  (--`!m n p. (m+n)<p ==> ( m<p /\ n<p )`--),
  REPEAT STRIP_TAC THENL
   [ ASSUME_TAC (SPEC_ALL LESS_EQ_ADD) THEN
     IMP_RES_TAC LESS_EQ_LESS_TRANS ,
     ASSUME_TAC (SPEC (--`m:num`--) (SPEC (--`n:num`--) LESS_EQ_ADD)) THEN
     POP_ASSUM( ASSUME_TAC o (ONCE_REWRITE_RULE[ADD_SYM]) ) THEN
     IMP_RES_TAC LESS_EQ_LESS_TRANS ]);



val  NOT_LESS_IMP_LESS_EQ_ADD1 =store_thm(
  "NOT_LESS_IMP_LESS_EQ_ADD1" ,
  (--`!a:num. !b:num. ~(a<b) ==> b<=(a+1)`--) , 
  REWRITE_TAC [NOT_LESS, SYM( SPEC_ALL ADD1)] THEN
  REPEAT STRIP_TAC THEN
  ASSUME_TAC (SPEC (--`a:num`--) LESS_SUC_REFL) THEN
  IMP_RES_TAC LESS_IMP_LESS_OR_EQ THEN
  IMP_RES_TAC LESS_EQ_TRANS );


val NOT_ADD_LESS = store_thm("NOT_ADD_LESS",
  (--`!m n. ~((m+n)<n)`--),
  REWRITE_TAC[NOT_LESS,ONCE_REWRITE_RULE[ADD_SYM]LESS_EQ_ADD] );

val ADD_EQ_LESS_EQ = store_thm("ADD_EQ_LESS_EQ",
  (--`!m n p. ((m+n)=p) ==> (m<=p)`--),
  REPEAT STRIP_TAC THEN POP_ASSUM(ASSUME_TAC o SYM) THEN
  ASM_REWRITE_TAC[LESS_EQ_ADD] );

val SUC_LESS_N_LESS = store_thm("SUC_LESS_N_LESS",
   (--`!m n.(m+1) < n ==> m < n`--),
   REPEAT STRIP_TAC THEN 
   ASSUME_TAC(SPECL [(--`m:num`--)] (REWRITE_RULE[ADD1]LESS_SUC_REFL)) THEN
   IMP_RES_TAC LESS_TRANS );

 
(*-------------------------------------------------------------------*)
(* An extra theorem by PC  *)

val  LESS_ADD1 =  store_thm("LESS_ADD1",
 (--`!a . a < (a + 1)`--),
 (REWRITE_TAC[SPECL[ (--`m:num`--), (--`0`--)] LESS_ADD_SUC, SUC_0]));

export_theory();
close_theory();
