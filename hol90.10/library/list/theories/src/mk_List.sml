(* ===================================================================== *)
(* FILE          : mk_list_thms.sml                                      *)
(* DESCRIPTION   : Theorems about lists. Translated from hol88.          *)
(*                                                                       *)
(* AUTHOR        : (c) Tom Melham, University of Cambridge               *)
(* DATE          : 86.11.24                                              *)
(* TRANSLATOR    : Konrad Slind, University of Calgary                   *)
(* DATE          : September 15, 1991                                    *)
(* HISTORY       : 22 March 1991                                         *)
(*                 Extended by Paul Curzon, University of Cambridge      *)
(*                 to maintain consistency with Wai Wongs HOL88 theory   *)
(*                                                                       *)
(*                 October'94 (KLS) minor rearrangements for             *)
(*                 library-ification of lists.                           *)
(* ===================================================================== *)

val path = 
   (!Globals.HOLdir)^"library/list/theories/"^SysParams.theory_file_type^"/"
val _ = theory_path := path::(!theory_path);

load_theory "operator";

new_theory "List";

(* fetch the axiom for lists.						*)
val list_Axiom = theorem "list" "list_Axiom";

(* abbreviation for list definitions - from src/3/list_conv.sml         *)
fun new_list_rec_definition (name,tm) =
  new_recursive_definition
           {name=name,rec_axiom=list_Axiom,def=tm,fixity=Prefix};

(* Permutation of universal quantifications				*)

fun chk_var vl v = (is_var v andalso (mem v vl)) ;

val FORALL_PERM_CONV = 
  let val forall_perm_rule = 
              fn tms => fn thm => GENL tms (SPEC_ALL thm)
  in
   fn tms => fn tm =>
     let val (vs,body) =  strip_forall tm
     in if (all (chk_var vs) tms)
        then let val vs' = tms @ (subtract vs tms)
                 val th1 = DISCH_ALL (forall_perm_rule vs' (ASSUME tm))
                 val th2 = DISCH_ALL (forall_perm_rule vs
                                        (ASSUME(list_mk_forall(vs',body))))
             in IMP_ANTISYM_RULE th1 th2
             end
        else raise HOL_ERR{origin_structure = "",
                           origin_function = "FORALL_PERM_CONV", 
                           message = "not all variables are quantified"}
     end
  end;

val FORALL_PERM_TAC = 
  fn tms => fn (asm,gl) =>
    CONV_TAC (FORALL_PERM_CONV tms) (asm,gl);



(* Fetch a few theorems from prim_rec.th				*)

val INV_SUC_EQ =  theorem "prim_rec" "INV_SUC_EQ";
val LESS_REFL =  theorem "prim_rec" "LESS_REFL";
val SUC_LESS =  theorem "prim_rec" "SUC_LESS";
val NOT_LESS_0 =  theorem "prim_rec" "NOT_LESS_0";
val LESS_MONO =  theorem "prim_rec" "LESS_MONO";
val LESS_SUC_REFL =  theorem "prim_rec" "LESS_SUC_REFL";
val LESS_SUC =  theorem "prim_rec" "LESS_SUC";
val LESS_THM =  theorem "prim_rec" "LESS_THM";
val LESS_SUC_IMP =  theorem "prim_rec" "LESS_SUC_IMP";
val LESS_0 =  theorem "prim_rec" "LESS_0";
val EQ_LESS =  theorem "prim_rec" "EQ_LESS";
val SUC_ID =  theorem "prim_rec" "SUC_ID";
val NOT_LESS_EQ =  theorem "prim_rec" "NOT_LESS_EQ";
val LESS_NOT_EQ =  theorem "prim_rec" "LESS_NOT_EQ";
val LESS_SUC_SUC =  theorem "prim_rec" "LESS_SUC_SUC";
val PRE =  theorem "prim_rec" "PRE";
val num_Axiom =   theorem "prim_rec" "num_Axiom";

(* Fetch a few things from arithmetic.th				*)

val LESS_OR_EQ =   definition "arithmetic" "LESS_OR_EQ";
val ADD =   definition "arithmetic" "ADD";
val SUB =   definition "arithmetic" "SUB";
val ADD_SUC =   theorem "arithmetic" "ADD_SUC";
val ADD_CLAUSES =   theorem "arithmetic" "ADD_CLAUSES";
val ADD_SYM =   theorem "arithmetic" "ADD_SYM";
val LESS_MONO_EQ =   theorem "arithmetic" "LESS_MONO_EQ";
val SUC_SUB1 =   theorem "arithmetic" "SUC_SUB1";
val LESS_ADD =   theorem "arithmetic" "LESS_ADD";
val SUB_0 =   theorem "arithmetic" "SUB_0";
val LESS_TRANS =   theorem "arithmetic" "LESS_TRANS";
val ADD1 =   theorem "arithmetic" "ADD1";
val ADD_0 =   theorem "arithmetic" "ADD_0";
val LESS_ANTISYM =   theorem "arithmetic" "LESS_ANTISYM";
val LESS_LESS_SUC =   theorem "arithmetic" "LESS_LESS_SUC";
val LESS_SUC_EQ_COR =   theorem "arithmetic" "LESS_SUC_EQ_COR";
val LESS_OR =   theorem "arithmetic" "LESS_OR";
val OR_LESS =   theorem "arithmetic" "OR_LESS";
val LESS_EQ =   theorem "arithmetic" "LESS_EQ";
val LESS_NOT_SUC =   theorem "arithmetic" "LESS_NOT_SUC";
val LESS_EQ_ANTISYM =   theorem "arithmetic" "LESS_EQ_ANTISYM";
val LESS_EQ_ADD =   theorem "arithmetic" "LESS_EQ_ADD";
val NOT_LESS =   theorem "arithmetic" "NOT_LESS";
val SUB_EQ_0 =   theorem "arithmetic" "SUB_EQ_0";
val ADD_ASSOC =   theorem "arithmetic" "ADD_ASSOC";
val SUB_ADD =   theorem "arithmetic" "SUB_ADD";
val ADD_EQ_0 =   theorem "arithmetic" "ADD_EQ_0";
val ADD_INV_0_EQ =   theorem "arithmetic" "ADD_INV_0_EQ";
val LESS_SUC_NOT =   theorem "arithmetic" "LESS_SUC_NOT";
val LESS_MONO_ADD =   theorem "arithmetic" "LESS_MONO_ADD";
val LESS_MONO_ADD_EQ =   theorem "arithmetic" "LESS_MONO_ADD_EQ";
val EQ_MONO_ADD_EQ =   theorem "arithmetic" "EQ_MONO_ADD_EQ";
val LESS_EQ_MONO_ADD_EQ =   theorem "arithmetic" "LESS_EQ_MONO_ADD_EQ";
val LESS_EQ_TRANS =   theorem "arithmetic" "LESS_EQ_TRANS";
val LESS_EQ_LESS_EQ_MONO =   theorem "arithmetic" "LESS_EQ_LESS_EQ_MONO";
val LESS_EQ_REFL =   theorem "arithmetic" "LESS_EQ_REFL";
val LESS_IMP_LESS_OR_EQ =   theorem "arithmetic" "LESS_IMP_LESS_OR_EQ";
val LESS_MONO_MULT =   theorem "arithmetic" "LESS_MONO_MULT";
val LESS_0_CASES =   theorem "arithmetic" "LESS_0_CASES";
val ZERO_LESS_EQ =   theorem "arithmetic" "ZERO_LESS_EQ";
val LESS_EQ_MONO =   theorem "arithmetic" "LESS_EQ_MONO";
val LESS_OR_EQ_ADD =   theorem "arithmetic" "LESS_OR_EQ_ADD";
val SUC_NOT =   theorem "arithmetic" "SUC_NOT";
val SUB_MONO_EQ =   theorem "arithmetic" "SUB_MONO_EQ";
val SUB_LESS_EQ =   theorem "arithmetic" "SUB_LESS_EQ";
val LESS_EQUAL_ANTISYM =   theorem "arithmetic" "LESS_EQUAL_ANTISYM";
val SUB_LESS_0 =   theorem "arithmetic" "SUB_LESS_0";
val SUB_LESS_OR =   theorem "arithmetic" "SUB_LESS_OR";
val LESS_ADD_SUC =   theorem "arithmetic" "LESS_ADD_SUC";
val LESS_SUB_ADD_LESS =   theorem "arithmetic" "LESS_SUB_ADD_LESS";
val ADD_SUB =   theorem "arithmetic" "ADD_SUB";
val LESS_EQ_ADD_SUB =   theorem "arithmetic" "LESS_EQ_ADD_SUB";
val SUB_EQUAL_0 =   theorem "arithmetic" "SUB_EQUAL_0";
val LESS_EQ_SUB_LESS =   theorem "arithmetic" "LESS_EQ_SUB_LESS";
val NOT_SUC_LESS_EQ =   theorem "arithmetic" "NOT_SUC_LESS_EQ";
val SUB_SUB =   theorem "arithmetic" "SUB_SUB";
val LESS_IMP_LESS_ADD =   theorem "arithmetic" "LESS_IMP_LESS_ADD";
val LESS_EQ_IMP_LESS_SUC =   theorem "arithmetic" "LESS_EQ_IMP_LESS_SUC";
val SUB_LESS_EQ_ADD =   theorem "arithmetic" "SUB_LESS_EQ_ADD";
val LESS_LESS_CASES =   theorem "arithmetic" "LESS_LESS_CASES";
val LESS_EQ_0 =   theorem "arithmetic" "LESS_EQ_0";
val EQ_LESS_EQ =   theorem "arithmetic" "EQ_LESS_EQ";
val ADD_MONO_LESS_EQ =   theorem "arithmetic" "ADD_MONO_LESS_EQ";
val NOT_SUC_LESS_EQ_0 =   theorem "arithmetic" "NOT_SUC_LESS_EQ_0";
val PRE_SUC_EQ =   theorem "arithmetic" "PRE_SUC_EQ";
val NOT_LEQ =   theorem "arithmetic" "NOT_LEQ";
val NOT_NUM_EQ =   theorem "arithmetic" "NOT_NUM_EQ";
val NOT_GREATER =   theorem "arithmetic" "NOT_GREATER";
val NOT_GREATER_EQ =   theorem "arithmetic" "NOT_GREATER_EQ";
val SUC_ONE_ADD =   theorem "arithmetic" "SUC_ONE_ADD";
val SUC_ADD_SYM =   theorem "arithmetic" "SUC_ADD_SYM";
val NOT_SUC_ADD_LESS_EQ =   theorem "arithmetic" "NOT_SUC_ADD_LESS_EQ";
val MULT_LESS_EQ_SUC =   theorem "arithmetic" "MULT_LESS_EQ_SUC";
val PRE_SUB1 =   theorem "arithmetic" "PRE_SUB1";
val SUB_PLUS =   theorem "arithmetic" "SUB_PLUS";
val GREATER_EQ =   theorem "arithmetic" "GREATER_EQ";

(* Fetch a few things from num.th					*)

val INV_SUC = theorem "num" "INV_SUC";
val NOT_SUC = theorem "num" "NOT_SUC";
val INDUCTION = theorem "num" "INDUCTION";

(* Fetch a few definitions and theorems from "operator".		*)

val ASSOC_DEF =  definition "operator" "ASSOC_DEF";
val COMM_DEF =  definition "operator" "COMM_DEF";
val FCOMM_DEF =  definition "operator" "FCOMM_DEF";
val RIGHT_ID_DEF =  definition "operator" "RIGHT_ID_DEF";
val LEFT_ID_DEF =  definition "operator" "LEFT_ID_DEF";
val MONOID_DEF =  definition "operator" "MONOID_DEF";
val ASSOC_CONJ =  theorem "operator" "ASSOC_CONJ";
val ASSOC_DISJ =  theorem "operator" "ASSOC_DISJ";
val FCOMM_ASSOC =  theorem "operator" "FCOMM_ASSOC";

(* Fetch a few definitions and theorems from combin.th			*)

val o_DEF = definition "combin" "o_DEF";
val o_THM = theorem "combin" "o_THM";
val I_THM = theorem "combin" "I_THM";

val UNCURRY_DEF = definition "pair" "UNCURRY_DEF";

(* List induction							*)
(* |- P NIL /\ (!l. P l ==> !x. P(CONS x l)) ==> (!x. P x) 		*)
val list_INDUCT = store_thm("list_INDUCT",
 --`!P. P [] /\ (!l. P l ==> !x:'a. P(CONS x l)) ==> (!l. P l)`--,
 REWRITE_TAC[theorem "list" "list_INDUCT"]);

(* Create a tactic.							*)
val LIST_INDUCT_TAC = INDUCT_THEN list_INDUCT ASSUME_TAC;

val prove_cases_thm = Rec_type_support.prove_cases_thm;
val prove_constructors_one_one = Rec_type_support.prove_constructors_one_one;
val prove_constructors_distinct =
             Rec_type_support.prove_constructors_distinct;

val num_CONV = Num_conv.num_CONV;

(* --------------------------------------------------------------------- *)
(* Definitions of NULL, HD and TL.					 *)
(* --------------------------------------------------------------------- *)

val NULL_DEF = store_thm("NULL_DEF", 
--`((NULL:'a list -> bool) [] = T) /\ 
   !(x:'a) l. NULL (CONS x l) = F`--,
 REWRITE_TAC[definition"list" "NULL_DEF"]);
 
val HD = store_thm("HD",   --`!(x:'a) l. HD (CONS x l) = x`--,
   REWRITE_TAC[definition"list" "HD"]);

val TL = store_thm("TL",   --`!(x:'a) l. TL (CONS x l) = l`--,
   REWRITE_TAC[definition"list" "TL"]);




(*----------------------------------------------------------------*)
(*- Alternative list constructor---adding element to the tail end-*)
(*----------------------------------------------------------------*)


val SNOC = new_list_rec_definition ("SNOC",
 (--`(!x.      SNOC (x:'a) ([]:'a list) = [x]) /\
     (!x x' l. SNOC (x:'a) (CONS x' l) = CONS x' (SNOC x l))`--));




(*-------------------------------------------------------------- *)
(* Reductions	    	    	    				 *)
(* Spec:    	    	    	    				 *)
(*	FOLDR f [x0;x1;...;xn-1] e = f(x0,f(x1,...f(xn-1,e)...)) *)
(*	FOLDL f e [x0;x1;...;xn-1] = f(...f(f(e,x0),x1),...xn-1) *)
(*-------------------------------------------------------------- *)
val FOLDR = new_list_rec_definition("FOLDR",
    (--`(!f e. FOLDR (f:'a->'b->'b) e [] = e) /\
     (!f e x l. FOLDR f e (CONS x l) = f x (FOLDR f e l))`--));

val FOLDL = new_list_rec_definition("FOLDL",
    (--`(!f e. FOLDL (f:'b->'a->'b) e [] = e) /\
     (!f e x l. FOLDL f e (CONS x l) = FOLDL f (f e x) l)`--));



(*--------------------------------------------------------------*)
(* Filter   	    	    	    				*)
(* Spec:    	    	    	    				*)
(* 	FILTER P [x0; ...; xn-1] = [...;xi;...]			*)
(* 	  where P xi holds for all xi in the resulting list	*)
(*--------------------------------------------------------------*)
val FILTER = new_list_rec_definition("FILTER",
    (--`(!P. FILTER P [] = []) /\
     (!(P:'a->bool) x l. FILTER P (CONS x l) =
	(P x => CONS x (FILTER P l) | FILTER P l))`--));




(*--------------------------------------------------------------*)
(* Cumulation 	    	    	    				*)
(*--------------------------------------------------------------*)
val SCANL = new_list_rec_definition("SCANL",
    (--`(!f e. SCANL (f:'b->'a->'b) e [] = [e]) /\
        (!f e x l. SCANL f e (CONS x l) = CONS e (SCANL f (f e x) l))`--));

val SCANR = new_list_rec_definition("SCANR",
    (--`(!f e. SCANR (f:'a->'b->'b) e [] = [e]) /\
        (!f e x l. SCANR (f:'a->'b->'b) e (CONS x l) =
     	   CONS (f x (HD (SCANR f e l))) (SCANR f e l))`--));


(*--------------------------------------------------------------*)
(* Reverse  	    	    	    				*)
(*--------------------------------------------------------------*)
val REVERSE = new_list_rec_definition ("REVERSE",
 (--`(REVERSE [] = []) /\
  (!x l. REVERSE (CONS (x:'a) l) = SNOC x (REVERSE l))`--));


(*--------------------------------------------------------------*)
(* Concatenation of two lists 	    				*)
(* Spec:    	    	    	    				*)
(*   APPEND [x0;...;xn-1] [x'0;...;x'm-1] =			*)
(*  	 [x0;...;xn-1;x'0;...;x'm-1] 				*)
(*--------------------------------------------------------------*)

val APPEND = store_thm("APPEND", 
  --`(!l:'a list.    APPEND [] l = l) /\
     (!l1 l2 (x:'a). APPEND (CONS x l1) l2 = CONS x (APPEND l1 l2))`--,
  REWRITE_TAC[definition"list" "APPEND"]);

(*--------------------------------------------------------------*)
(* Concatenation of a list of lists   				*)
(* Spec:    	    	    	    				*)
(*	FLAT [[x00;...;x0n-1];...;[xp-10;...;xp-1n-1]] =	*)
(*		[x00;...;x0n-1;...;xp-10;...;xp-1n-1]		*)
(*--------------------------------------------------------------*)

val FLAT = store_thm("FLAT", 
 --`((FLAT:'a list list -> 'a list) [] = []) /\ 
    (!(x:'a list) l. FLAT (CONS x l) = APPEND x (FLAT l))`--,
 REWRITE_TAC[definition"list" "FLAT"]);

(*--------------------------------------------------------------*)
(* Concatenation of a list of lists   				*)
(* Spec:    	    	    	    				*)
(*  LENGTH [x0;...;xn-1] = n	    				*)
(*--------------------------------------------------------------*)

val LENGTH = store_thm("LENGTH", 
 --`(           LENGTH ([]:'a list) = 0) /\ 
    (!(x:'a) l. LENGTH (CONS x l) = SUC (LENGTH l))`--,
 REWRITE_TAC[definition "list" "LENGTH"]);

(*--------------------------------------------------------------*)
(* Apply a function to all elements of a list 			*)
(* Spec:    	    	    	    				*)
(*  MAP f [x0;...;xn-1] = [f x0;...; f xn-1]			*)
(*--------------------------------------------------------------*)

val MAP = store_thm("MAP", 
 --`(!(f:'a -> 'b). MAP f [] = []) /\ 
    (!f (x:'a) l. MAP f (CONS x l) = CONS ((f x):'b) (MAP f l))`--,
 REWRITE_TAC[definition "list" "MAP"]);

(* ---------------------------------------------------------------------*)
(* Definition of a function 						*)
(*									*)
(*   MAP2 : ('a -> 'b -> 'c) -> 'a list ->  'b list ->  'c list		*)
(* 									*)
(* for mapping a curried binary function down a pair of lists:		*)
(* 									*)
(* |- (!f. MAP2 f[][] = []) /\						*)
(*   (!f x1 l1 x2 l2.							*)
(*      MAP2 f(CONS x1 l1)(CONS x2 l2) = CONS(f x1 x2)(MAP2 f 11 l2))	*)
(* 									*)
(* [TFM 92.04.21]							*)
(* ---------------------------------------------------------------------*)

val MAP2 = store_thm("MAP2", 
 --`(!(f:'a->'b->'c). MAP2 f [] [] = []) /\
    (!(f:'a->'b->'c) x1 l1 x2 l2.
       MAP2 f(CONS x1 l1)(CONS x2 l2) = CONS(f x1 x2)(MAP2 f l1 l2))`--,
 REWRITE_TAC[definition "list" "MAP2"]);

(*--------------------------------------------------------------*)
(* Predicates	    	    	    				*)
(* Spec:    	    	    	    				*)
(*   ALL_EL P [x0;...;xn-1] = T, iff P xi = T for i=0,...,n-1   *)
(* 			      F, otherwise			*)
(*--------------------------------------------------------------*)
(* Same as "EVERY" in "list" theory *)
val ALL_EL = new_recursive_definition
      {name = "ALL_EL",
       fixity = Prefix, 
       rec_axiom = list_Axiom,
       def = --`(!P:'a->bool. ALL_EL P NIL = T)  /\
                (!P x l. ALL_EL P (CONS x l) = (P x /\ ALL_EL P l))`--};


(*--------------------------------------------------------------*)
(* Spec:    	    	    	    				*)
(*   SOME_EL P [x0;...;xn-1] = T, iff P xi = T for some i       *)
(*			       F, otherwise			*)
(*--------------------------------------------------------------*)

val SOME_EL = new_list_rec_definition("SOME_EL",
    (--`(!P. SOME_EL P [] = F) /\
     (!(P:'a->bool) x l. SOME_EL P (CONS x l) = P x \/ (SOME_EL P l))`--));


(*--------------------------------------------------------------*)
(* Spec:    	    	    	    				*)
(*   IS_EL x [x0;...;xn-1] = T, iff ?xi. x = xi for i=0,...,n-1 *)
(*  	    	    	      F, otherwise			*)
(*--------------------------------------------------------------*)
val IS_EL_DEF = new_definition("IS_EL_DEF",
    (--`!(x:'a) l. IS_EL x l = SOME_EL ($= x) l`--));

val AND_EL_DEF = new_definition("AND_EL_DEF",
    (--`AND_EL = ALL_EL I`--));

val OR_EL_DEF = new_definition("OR_EL_DEF",
    (--`OR_EL = SOME_EL I`--));

(*--------------------------------------------------------------*)
(* Segments 	    	    	    				*)
(* Spec:    	    	    	    				*)
(*	FIRSTN m [x0;...;xn-1] = [x0;...;xm-1]			*)
(*	BUTFIRSTN m [x0;...;xn-1] = [xm;...;xn-1]		*)
(*	LASTN m [x0;...;xn-1] = [xn-m;...;xn-1]			*)
(*	BUTLASTN m [x0;...;xn-1] = [x0;...;xn-m]		*)
(*	BUTLAST [x0;...;xn-1] = [x0;...;xn-2]			*)
(*	LAST [x0;...;xn-1] = [xn-1] 				*)
(*--------------------------------------------------------------*)

val FIRSTN =
    let val thm1 = prove_rec_fn_exists num_Axiom
    	(--`(firstn 0 (l:'a list) = []) /\
         (firstn (SUC k) l = CONS (HD l) (firstn k (TL l)))`--)
    val thm = prove(
       (--`?firstn. (!l:'a list. firstn 0 l = []) /\
         (!n x (l:'a list). firstn (SUC n) (CONS x l) = CONS x (firstn n l))`--),
    	STRIP_ASSUME_TAC thm1 THEN EXISTS_TAC (--`firstn:num->('a)list->('a)list`--)
    	THEN ASM_REWRITE_TAC[HD,TL])
   in
    new_specification{name = "FIRSTN",
                      sat_thm = thm,
                      consts =  [{const_name = "FIRSTN", fixity = Prefix}]
                     }
   end;

val BUTFIRSTN =
    let val thm2 = prove_rec_fn_exists num_Axiom
    	(--`(butfirstn 0 (l:'a list) = l) /\
         (butfirstn (SUC k) l = butfirstn k (TL l))`--)
    val thm = prove(
       (--`?butfirstn. (!l:'a list. butfirstn 0 l = l) /\
         (!n x (l:'a list). butfirstn (SUC n) (CONS x l) = butfirstn n l)`--),
    	STRIP_ASSUME_TAC thm2 THEN EXISTS_TAC (--`butfirstn:num->('a)list->('a)list`--)
    	THEN ASM_REWRITE_TAC[HD,TL])
   in
    new_specification{name = "BUTFIRSTN",
                      sat_thm = thm,
                      consts =  [{const_name = "BUTFIRSTN", fixity = Prefix}]
                     }
   end;

(*----------------------------------------------------------------*)
(*- Segment  	    	    	    				-*)
(*- Spec:    	    	    	    				-*)
(*- 	SEG m k [x0,...xk,...xk+m-1,...,xn] = [xk,...,xk+m-1]   -*)
(*----------------------------------------------------------------*)
val SEG = 
    let val SEG_exists = prove(
    (--`?SEG. (!k (l:'a list). SEG 0 k l = []) /\
       (!m x l. SEG (SUC m) 0 (CONS x l) = CONS x (SEG m 0 l)) /\
       (!m k x l. SEG (SUC m) (SUC k) (CONS x l) = SEG (SUC m) k l)`--),
    EXISTS_TAC (--`\m k (l:'a list). (FIRSTN:num -> 'a list -> 'a list) m
    	((BUTFIRSTN:num -> 'a list -> 'a list) k l)`--)
    THEN BETA_TAC THEN REWRITE_TAC[FIRSTN,BUTFIRSTN])
    in
    new_specification{name = "SEG",
                      sat_thm = SEG_exists,
                      consts =  [{const_name = "SEG", fixity = Prefix}]
                     }
    end;

(*----------------------------------------------------------------*)
(*- LAST and BUTLAST is analogous to HD and TL at the end of list-*)
(*----------------------------------------------------------------*)
val LAST_DEF = new_definition("LAST_DEF",
    (--`!l:'a list. LAST l = HD (SEG 1 (PRE(LENGTH l)) l)`--));

val BUTLAST_DEF = new_definition("BUTLAST_DEF",
    (--`!l:'a list. BUTLAST l = SEG (PRE(LENGTH l)) 0 l`--));

val LENGTH_SNOC = prove(
    (--`!(x:'a) l. LENGTH (SNOC x l) = SUC (LENGTH l)`--),
    GEN_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC [LENGTH,SNOC]);

val LAST =     (* (--`!(x:'a) l. LAST (SNOC x l) = x`--), *)
    let val lem = prove(
    (--`!x (l:'a list).  (SEG 1 (PRE(LENGTH (SNOC x l))) (SNOC x l)) = [x]`--),
    GEN_TAC THEN PURE_ONCE_REWRITE_TAC[LENGTH_SNOC]
    THEN PURE_ONCE_REWRITE_TAC[PRE]
    THEN CONV_TAC (ONCE_DEPTH_CONV num_CONV)
    THEN LIST_INDUCT_TAC
    THEN PURE_ONCE_REWRITE_TAC[LENGTH] THEN REWRITE_TAC[SNOC,SEG]
    THEN FIRST_ASSUM ACCEPT_TAC)
    in
    GEN_ALL(REWRITE_RULE[lem,HD](SPEC (--`SNOC (x:'a) l`--) LAST_DEF))
    end;

val BUTLAST =     (* (--`!x l. BUTLAST (SNOC x l) = l`--), *)
    let val lem = prove(
    (--`!x:'a. !l. SEG (PRE(LENGTH (SNOC x l))) 0 (SNOC x l) = l`--),
    GEN_TAC THEN PURE_ONCE_REWRITE_TAC[LENGTH_SNOC]
    THEN PURE_ONCE_REWRITE_TAC[PRE]
    THEN LIST_INDUCT_TAC
    THEN PURE_ONCE_REWRITE_TAC[LENGTH] THEN ASM_REWRITE_TAC[SNOC,SEG])
    in
    GEN_ALL(REWRITE_RULE[lem](SPEC (--`SNOC (x:'a) l`--) BUTLAST_DEF))
    end;

val LASTN =
    let val thm1 = prove_rec_fn_exists num_Axiom
        (--`(lastn 0 (l:('a)list) = []) /\
    	 (lastn (SUC n) l = SNOC (LAST l) (lastn n (BUTLAST l)))`--)
    val thm = prove(
    	(--`?lastn. (!l:'a list. lastn 0 l = []) /\
    	 (!n (x:'a) l. lastn (SUC n) (SNOC x l) = SNOC x (lastn n l))`--),
    	STRIP_ASSUME_TAC thm1 THEN EXISTS_TAC (--`lastn:num->('a)list->('a)list`--)
    	THEN ASM_REWRITE_TAC[LAST,BUTLAST])
   in
    new_specification{name = "LASTN",
                      sat_thm = thm,
                      consts =  [{const_name = "LASTN", fixity = Prefix}]
                     }
   end;

val BUTLASTN = 
    let val thm1 = prove_rec_fn_exists num_Axiom
    	(--`(butlastn 0 l = (l:('a)list)) /\
         (butlastn (SUC n) l = butlastn n (BUTLAST l))`--)
    val thm = prove(
    	(--`?butlastn. (!l:'a list. butlastn 0 l = l) /\
    	 (!n (x:'a) l. butlastn (SUC n) (SNOC x l) = butlastn n l)`--),
    	STRIP_ASSUME_TAC thm1 THEN EXISTS_TAC (--`butlastn:num->('a)list->('a)list`--)
    	THEN ASM_REWRITE_TAC[BUTLAST])
    in
    new_specification{name = "BUTLASTN",
                      sat_thm = thm,
                      consts =  [{const_name = "BUTLASTN", fixity = Prefix}]
                     }
    end;

(*--------------------------------------------------------------*)
(* Index of elements	    	    				*)
(* Spec:    	    	    	    				*)
(*	EL k [x0;...xk;...;xn-1] = xk				*)
(*	ELL k [xn-1;...xk;...;x0] = xk				*)
(*--------------------------------------------------------------*)


val EL = store_thm("EL", 
--`(!l:'a list. EL 0 l = HD l) /\
   (!n (l:'a list). EL (SUC n) l = EL n (TL l))`--,
  REWRITE_TAC[definition "list" "EL"]);

val ELL = new_recursive_definition
      {name = "ELL",
       fixity = Prefix, 
       rec_axiom = num_Axiom,
       def = --`(!l:'a list. ELL 0 (l:'a list) = LAST l) /\
                (!l:'a list. ELL (SUC n) l = ELL n (BUTLAST l))`--};


(*--------------------------------------------------------------*)
(* Predicates between lists 	    				*)
(* Spec:    	    	    	    				*)
(*	IS_PREFIX l1 l2 = T, iff ?l. l1 = APPEND l2 l		*)
(*	IS_SUFFIX l1 l2 = T, iff ?l. l1 = APPEND l l2		*)
(*	IS_SUBLIST l1 l2 = T, 	    				*)
(*  	    	    iff ?l l'. l1 = APPEND l (APPEND l2 l')	*)
(*  	    	    	    	    				*)
(*	SPLITP P [x0;...xk;...;xn-1] =				*)
(*  	     ([x0;...;x(k-1)],[xk;...;xn-1])			*)
(*		where P xi = F for all i < k and P xk = T	*)
(*  	    	    	    	    				*)
(*	PREFIX P [x0;...xk;...;xn-1] = [x0;...xk-1]		*)
(*		where P xk = F and P xi = T for i = 0,...,k-1	*)
(*	SUFFIX P [x0;...xk;...;xn-1] = [xk+1;...xn-1]		*)
(*		where P xk = F and P xi = T for i = k+1,...,n-1 *)
(*--------------------------------------------------------------*)

val IS_PREFIX =
    let val lemma = prove(
       (--`?fn. (!l:'a list. fn l [] = T) /\
    	(!x (l:'a list). fn [] (CONS x l) = F) /\
        (!(x1:'a) l1 (x2:'a) l2  . fn (CONS x1 l1) (CONS x2 l2) =
	    (x1 = x2) /\ (fn l1 l2))`--),
        let val th = prove_rec_fn_exists list_Axiom
    	    (--`(fn l [] = T) /\
    	     (fn (l:'a list) (CONS x t) = 
    	    	((NULL l) => F | (((HD l) = x) /\ (fn (TL l) t))))`--)
        in
    	STRIP_ASSUME_TAC th THEN EXISTS_TAC (--`fn:'a list -> 'a list -> bool`--)
    	THEN ASM_REWRITE_TAC[HD,TL,NULL_DEF]
        end)
   in
    new_specification
        {consts = [{const_name = "IS_PREFIX", fixity = Prefix}],
         name = "IS_PREFIX",
         sat_thm = lemma
        }
   end;


(*---------------------------------------------------------------*)

val REVERSE_SNOC = prove((--`!(x:'a) l. REVERSE (SNOC x l) = CONS x (REVERSE l)`--),
    GEN_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[SNOC,REVERSE]);

val REVERSE_REVERSE = prove((--`!l:('a)list. REVERSE (REVERSE l) = l`--),
    LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[REVERSE,REVERSE_SNOC]);

val forall_REVERSE = TAC_PROOF(([],
    (--`!P. (!l:('a)list. P(REVERSE l)) = (!l. P l)`--)),
    GEN_TAC THEN EQ_TAC THEN DISCH_TAC THEN GEN_TAC
    THEN POP_ASSUM (ACCEPT_TAC o (REWRITE_RULE[REVERSE_REVERSE]
     o (SPEC (--`REVERSE l:('a)list`--)))));

val f_REVERSE_lemma = TAC_PROOF (([],
    (--`!f1 f2.
    ((\x. (f1:('a)list->'b) (REVERSE x)) = (\x. f2 (REVERSE x))) = (f1 = f2)`--)),
    REPEAT GEN_TAC THEN EQ_TAC THEN DISCH_TAC THENL[
      POP_ASSUM (fn x => ACCEPT_TAC (EXT (REWRITE_RULE[REVERSE_REVERSE]
      (GEN (--`x:('a)list`--) (BETA_RULE (AP_THM x (--`REVERSE (x:('a)list)`--))))))),
      ASM_REWRITE_TAC[]]);


val SNOC_Axiom = prove(
 (--`!(e:'b) (f:'b -> ('a -> (('a)list -> 'b))).
  ?! fn1. (fn1[] = e) /\ (!x l. fn1(SNOC x l) = f(fn1 l)x l)`--),

 let val  lemma =  CONV_RULE (EXISTS_UNIQUE_CONV)
       (REWRITE_RULE[REVERSE_REVERSE] (BETA_RULE (SPECL
    	 [(--`e:'b`--),(--`(\ft x l. f ft x (REVERSE l)):'b -> ('a -> (('a)list -> 'b))`--)]
        (PURE_ONCE_REWRITE_RULE
    	 [SYM (CONJUNCT1 REVERSE),
    	  PURE_ONCE_REWRITE_RULE[SYM (SPEC_ALL REVERSE_SNOC)]
    	   (BETA_RULE (SPEC (--`\l:('a)list.fn1(CONS x l) =
    	    	       (f:'b -> ('a -> (('a)list -> 'b)))(fn1 l)x l`--)
    	     (CONV_RULE (ONCE_DEPTH_CONV SYM_CONV) forall_REVERSE)))]
    	    list_Axiom))))
 in
    REPEAT GEN_TAC THEN CONV_TAC EXISTS_UNIQUE_CONV
    THEN STRIP_ASSUME_TAC lemma THEN CONJ_TAC THENL
    [
      EXISTS_TAC (--`(fn1:('a)list->'b) o REVERSE`--)
      THEN REWRITE_TAC[o_DEF] THEN BETA_TAC THEN ASM_REWRITE_TAC[],

      REPEAT GEN_TAC THEN POP_ASSUM (ACCEPT_TAC o SPEC_ALL o
    	REWRITE_RULE[REVERSE_REVERSE,f_REVERSE_lemma] o
        BETA_RULE o REWRITE_RULE[o_DEF] o
        SPECL [(--`(fn1' o REVERSE):('a)list->'b`--),(--`(fn1'' o REVERSE):('a)list->'b`--)])
     ]
  end);

val IS_SUFFIX =
    let val LENGTH_SNOC = prove((--`!(x:'a) l. LENGTH (SNOC x l) = SUC (LENGTH l)`--),
        GEN_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC [LENGTH,SNOC])
    val NOT_NULL_SNOC = prove((--`!(x:'a) l. ~NULL(SNOC x l)`--),
        GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[SNOC,NULL_DEF])
    val LAST = (* (--`!(x:'a) l. LAST (SNOC x l) = x`--), *)
        let val lem = prove(
    	    (--`!x (l:'a list). (SEG 1 (PRE(LENGTH (SNOC x l))) (SNOC x l)) = [x]`--),
    	    GEN_TAC THEN PURE_ONCE_REWRITE_TAC[LENGTH_SNOC]
    	    THEN PURE_ONCE_REWRITE_TAC[PRE]
    	    THEN CONV_TAC (ONCE_DEPTH_CONV num_CONV)
    	    THEN LIST_INDUCT_TAC
    	    THEN PURE_ONCE_REWRITE_TAC[LENGTH] THEN REWRITE_TAC[SNOC,SEG]
    	    THEN FIRST_ASSUM ACCEPT_TAC)
       in
        GEN_ALL(REWRITE_RULE[lem,HD](SPEC (--`SNOC (x:'a) l`--) LAST_DEF))
       end
    val BUTLAST = (* (--`!x l. BUTLAST (SNOC x l) = l`--), *)
        let val lem = prove(
    	    (--`!x:'a. !l. SEG (PRE(LENGTH (SNOC x l))) 0 (SNOC x l) = l`--),
    	    GEN_TAC THEN PURE_ONCE_REWRITE_TAC[LENGTH_SNOC]
    	    THEN PURE_ONCE_REWRITE_TAC[PRE] THEN LIST_INDUCT_TAC
    	    THEN PURE_ONCE_REWRITE_TAC[LENGTH]
    	    THEN ASM_REWRITE_TAC[SNOC,SEG])
       in
        GEN_ALL(REWRITE_RULE[lem](SPEC (--`SNOC (x:'a) l`--) BUTLAST_DEF))
       end
    val lemma = prove(
       (--`?fn. (!l. fn l [] = T) /\
    	(!(x:'a) l. fn [] (SNOC x l) = F) /\
    	(!(x1:'a) l1 (x2:'a) l2. fn (SNOC x1 l1) (SNOC x2 l2) =
	    (x1 = x2) /\ (fn l1 l2))`--),
    	let val th = prove_rec_fn_exists SNOC_Axiom
    	    (--`(fn l [] = T) /\
    	     (fn l (SNOC (x:'a) t) =
    	    	((NULL l) => F | ((LAST l) = x) /\ (fn (BUTLAST l) t)))`--)
       in
    	STRIP_ASSUME_TAC th THEN EXISTS_TAC (--`fn:'a list -> 'a list -> bool`--)
    	THEN ASM_REWRITE_TAC[BUTLAST,LAST,NULL_DEF,NOT_NULL_SNOC]
      end)
    in
    new_specification
        {consts = [{const_name = "IS_SUFFIX", fixity = Prefix}],
         name = "IS_SUFFIX",
         sat_thm = lemma
        }
    end;

val IS_SUBLIST =
    let val lemma = prove(
        (--`?fn. (!l:'a list. fn l [] = T) /\
    	  (!(x:'a) l. fn [] (CONS x l) = F) /\
          (!x1 l1 x2 l2. fn (CONS x1 l1) (CONS x2 l2) =
    	   ((x1 = x2) /\ (IS_PREFIX l1 l2)) \/ (fn l1 (CONS x2 l2)))`--),
    	let val th = prove_rec_fn_exists list_Axiom
    	    (--`(fn [] (l:'a list) = (NULL l => T | F)) /\
    	     (fn (CONS x t) l =
    	    	((NULL l) => T |
    	    	 (((x = (HD l)) /\ (IS_PREFIX t (TL l))) \/ (fn t l))))`--)
        in
    	STRIP_ASSUME_TAC th THEN EXISTS_TAC (--`fn:'a list -> 'a list -> bool`--)
    	THEN ASM_REWRITE_TAC[HD,TL,NULL_DEF]
    	THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[HD,TL,NULL_DEF]
        end)
    in
    new_specification
        {consts = [{const_name = "IS_SUBLIST", fixity = Prefix}],
         name = "IS_SUBLIST",
         sat_thm = lemma
        }
    end;

val SPLITP = new_recursive_definition
      {name = "SPLITP",
       fixity = Prefix, 
       rec_axiom = list_Axiom,
       def = --`(!P. SPLITP P [] = ([],[])) /\
                (!P x l. SPLITP P (CONS (x:'a) l) =
    	          (P x => ([], CONS x l) |
    	            ((CONS x (FST(SPLITP P l))), (SND (SPLITP P l)))))`--};

val PREFIX_DEF = new_definition("PREFIX_DEF",
    (--`PREFIX P (l:'a list) = FST (SPLITP ($~ o P) l)`--));

val SUFFIX_DEF = new_definition("SUFFIX_DEF",
    (--`!P (l:'a list). SUFFIX P l = FOLDL (\l' x. P x => SNOC x l' | []) [] l`--));

(*--------------------------------------------------------------*)
(* List of pairs    	    	    				*)
(* Spec:    	    	    	    				*)
(*  ZIP([x0;...;xn-1],[y0;...;yn-1]) = [(x0,y0;...;(xn-1,yn-1)] *)
(*  UNZIP[(x0,y0;...;(xn-1,yn-1)]=([x0;...;xn-1],[y0;...;yn-1]) *)
(*  UNZIP_FST [(x0,y0;...;(xn-1,yn-1)] = [x0;...;xn-1]		*)
(*  UNZIP_SND [(x0,y0;...;(xn-1,yn-1)] = [y0;...;yn-1] 		*)
(*--------------------------------------------------------------*)

val ZIP = 
    let val lemma = prove(
    (--`?ZIP. (ZIP ([], []) = []) /\
       (!(x1:'a) l1 (x2:'b) l2.
	ZIP ((CONS x1 l1), (CONS x2 l2)) = CONS (x1,x2)(ZIP (l1, l2)))`--),
    let val th = prove_rec_fn_exists list_Axiom
        (--`(fn [] l = []) /\
         (fn (CONS (x:'a) l') (l:'b list) =
                           CONS (x, (HD l)) (fn  l' (TL l)))`--)
        in
    STRIP_ASSUME_TAC th
    THEN EXISTS_TAC
           (--`UNCURRY (fn:('a)list -> (('b)list -> ('a # 'b)list))`--)
    THEN ASM_REWRITE_TAC[definition "pair" "UNCURRY_DEF",HD,TL]
     end)
    in
    new_specification
        {consts = [{const_name = "ZIP", fixity = Prefix}],
         name = "ZIP",
         sat_thm = lemma
        }
    end;

val UNZIP = new_list_rec_definition("UNZIP",
    (--`(UNZIP [] = ([], [])) /\
     (!x l. UNZIP (CONS (x:'a # 'b) l) = 
	(CONS (FST x) (FST (UNZIP l)),
         CONS (SND x) (SND (UNZIP l))))`--));



val UNZIP_FST_DEF = new_definition("UNZIP_FST_DEF",
    (--`!l:('a#'b)list. UNZIP_FST l = FST(UNZIP l)`--));

val UNZIP_SND_DEF = new_definition("UNZIP_SND_DEF",
    (--`!l:('a#'b)list. UNZIP_SND l = SND(UNZIP l)`--));




(*--------------------------------------------------------------*)
(* List of natural numbers    	    	    			*)
(* Spec:    	    	    	    				*)
(*  SUM [x0;...;xn-1] = x0 + ... + xn-1				*)
(*--------------------------------------------------------------*)

val SUM = store_thm("SUM", 
--`(SUM [] = 0) /\ (!x l. SUM (CONS x l) = x + SUM l)`--,
 REWRITE_TAC[definition "list" "SUM"]);

(*--------------------------------------------------------------*)
(* List generator    	    	    				*)
(* Spec:    	    	    	    				*)
(*  GENLIST f n = [f 0;...; f(n-1)] 				*)
(*  REPLICATE n x = [x;....;x] (n repeate elements)             *)
(*--------------------------------------------------------------*)

val GENLIST = new_recursive_definition
      {name = "GENLIST",
       fixity = Prefix,
       rec_axiom =  num_Axiom,
       def = --`(GENLIST (f:num->'a) 0 = []) /\
                (GENLIST f (SUC n) = SNOC (f n) (GENLIST f n))`--};

val REPLICATE = new_recursive_definition
      {name = "REPLICATE",
       fixity = Prefix,
       rec_axiom =  num_Axiom,
       def = --`(REPLICATE 0 (x:'a) = []) /\
                (REPLICATE (SUC n) x = CONS x (REPLICATE n x))`--};


(* ---------------------------------------------------------------------
 * Theorems from the basic list theory.
 ************************************************************************)

val NULL = store_thm ("NULL",
 --`NULL (NIL :'a list) /\ (!x l. ~NULL(CONS (x:'a) l))`--,
   REWRITE_TAC [theorem "list" "NULL"]);


val list_CASES = store_thm ("list_CASES", 
 --`!l:'a list. (l = []) \/ (?l' x. l = CONS x l')`--,
   REWRITE_TAC[theorem "list" "list_CASES"]);


val CONS_11 = store_thm("CONS_11", 
 --`!(x:'a) l x' l'. (CONS x l = CONS x' l') = (x = x') /\ (l = l')`--,
 REWRITE_TAC[theorem "list" "CONS_11"]);


val NOT_NIL_CONS = store_thm("NOT_NIL_CONS", 
 --`!(x:'a) l. ~([] = CONS x l)`--,
 REWRITE_TAC[theorem "list" "NOT_NIL_CONS"]);


(* !x l. ~(CONS x l = [])   *)
val NOT_CONS_NIL = save_thm("NOT_CONS_NIL",
   CONV_RULE(ONCE_DEPTH_CONV SYM_CONV) NOT_NIL_CONS);


val LIST_NOT_EQ = store_thm("LIST_NOT_EQ",
 --`!l1 l2. ~(l1 = l2) ==> !x1:'a. !x2. ~(CONS x1 l1 = CONS x2 l2)`--,
 REWRITE_TAC[theorem "list" "LIST_NOT_EQ"]);


val NOT_EQ_LIST = store_thm("NOT_EQ_LIST",
 --`!x1:'a. !x2. ~(x1 = x2) ==> !l1 l2. ~(CONS x1 l1 = CONS x2 l2)`--,
 REWRITE_TAC[theorem "list" "NOT_EQ_LIST"]);


val EQ_LIST = store_thm("EQ_LIST",
 --`!x1:'a.!x2.(x1=x2) ==> !l1 l2. (l1 = l2) ==> (CONS x1 l1 = CONS x2 l2)`--,
 REWRITE_TAC[theorem "list" "EQ_LIST"]);

(*    CONS |- !l. ~(NULL l) ==> (CONS (HD l) (TL l) = l) *)
val CONS = save_thm("CONS", theorem "list" "CONS");

(* APPEND_ASSOC |- !l1 l2 l3.APPEND l1(APPEND l2 l3) = APPEND(APPEND l1 l2)3 *)
val APPEND_ASSOC = save_thm("APPEND_ASSOC", theorem "list" "APPEND_ASSOC");

(*  LENGTH_APPEND |- !l1 l2. LENGTH (APPEND l1 l2) = LENGTH l1 + LENGTH l2 *)
val LENGTH_APPEND = save_thm("LENGTH_APPEND", theorem "list" "LENGTH_APPEND");

(* MAP_APPEND |- !f l1 l2. MAP f(APPEND l1 l2) = APPEND(MAP f l1) (MAP f l2) *)
val MAP_APPEND = save_thm("MAP_APPEND", theorem "list" "MAP_APPEND");

(*    LENGTH_MAP |- !l f. LENGTH (MAP f l) = LENGTH l *)
val LENGTH_MAP = save_thm("LENGTH_MAP", theorem "list" "LENGTH_MAP");

(* Deleted by Paul Curzon, for some reason 
 * (*    EVERY_EL |- !l P. EVERY P l = (!n. n < LENGTH l ==> P (EL n l)) *)
 * val EVERY_EL = save_thm("EVERY_EL", theorem "list" "EVERY_EL");
 * 
 * (*    EVERY_CONJ |- !l. EVERY (\x. P x /\ Q x) l = EVERY P l /\ EVERY Q l *)
 * val EVERY_CONJ = save_thm("EVERY_CONJ", theorem "list" "EVERY_CONJ");
 *****************************************************************************)

(*    LENGTH_NIL |- !l. (LENGTH l = 0) = l = [] *)
val LENGTH_NIL = save_thm("LENGTH_NIL", theorem "list" "LENGTH_NIL");

val LENGTH_CONS = store_thm("LENGTH_CONS",
 --`!l n. (LENGTH l = SUC n) = 
          ?x:'a. ?l'. (LENGTH l' = n) /\ (l = CONS x l')`--, 
 REWRITE_TAC[theorem "list" "LENGTH_CONS"]);

(*
val LENGTH_EQ_SUC = store_thm("LENGTH_EQ_SUC",
 --`!(P:'a list->bool)  (n:num). 
      (!l. (LENGTH l = SUC n) ==> P l) =  
      (!l. (LENGTH l = n) ==> (\l. !x:'a. P (CONS x l)) l)`--,
    CONV_TAC (ONCE_DEPTH_CONV BETA_CONV) THEN
    REPEAT GEN_TAC THEN EQ_TAC THENL
    [REPEAT STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
     ASM_REWRITE_TAC [LENGTH],
     DISCH_TAC THEN
     INDUCT_THEN list_INDUCT STRIP_ASSUME_TAC THENL
     [REWRITE_TAC [LENGTH,NOT_NIL_CONS,NOT_EQ_SYM(SPEC_ALL NOT_SUC)],
      ASM_REWRITE_TAC [LENGTH,INV_SUC_EQ,CONS_11] THEN
      REPEAT STRIP_TAC THEN RES_THEN MATCH_ACCEPT_TAC]]);
*)

(* val LENGTH_EQ_CONS = save_thm("LENGTH_EQ_CONS", 
                              theorem "list" "LENGTH_EQ_CONS");
*)

(*    LENGTH_EQ_NIL |- !P. (!l. (LENGTH l = 0) ==> P l) = P [] *)
val LENGTH_EQ_NIL = save_thm("LENGTH_EQ_NIL", theorem "list" "LENGTH_EQ_NIL");



(* Added by PC 11 May 94 *)
val LENGTH_MAP2 = store_thm("LENGTH_MAP2",
    (--`!l1 l2. (LENGTH l1 = LENGTH l2) ==>
     (!f:'a->'b->'c. (LENGTH(MAP2 f l1 l2) = LENGTH l1) /\
      (LENGTH(MAP2 f l1 l2) = LENGTH l2))`--),
    LIST_INDUCT_TAC THENL[
      LIST_INDUCT_TAC THENL[
    	DISCH_TAC THEN PURE_ONCE_REWRITE_TAC[MAP2]
    	THEN REWRITE_TAC[LENGTH],
    	GEN_TAC THEN PURE_ONCE_REWRITE_TAC[LENGTH]
    	THEN REWRITE_TAC[SUC_NOT]],
      GEN_TAC THEN LIST_INDUCT_TAC THENL[
    	PURE_ONCE_REWRITE_TAC[LENGTH] THEN REWRITE_TAC[NOT_SUC],
    	GEN_TAC THEN PURE_ONCE_REWRITE_TAC[MAP2]
    	THEN PURE_ONCE_REWRITE_TAC[LENGTH]
    	THEN PURE_ONCE_REWRITE_TAC[INV_SUC_EQ]
    	THEN DISCH_TAC THEN RES_THEN ASSUME_TAC THEN GEN_TAC
    	THEN CONJ_TAC THEN FIRST_ASSUM MATCH_ACCEPT_TAC]]);

(*-==============================================================-*)
(*- More Theorems about lists	    	    			 -*)
(*-==============================================================-*)

val NULL_EQ_NIL = store_thm ("NULL_EQ_NIL",
    (--`!l:('a)list .  NULL l = (l = [])`--),
    GEN_TAC THEN STRUCT_CASES_TAC (SPEC_ALL list_CASES)
    THEN REWRITE_TAC [NULL,NOT_CONS_NIL]);

val LENGTH_EQ = store_thm ("LENGTH_EQ",
    (--`! (x:'a list) y. (x = y) ==> (LENGTH x = LENGTH y)`--),
    REPEAT GEN_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC []);

val LENGTH_NOT_NULL = store_thm("LENGTH_NOT_NULL",
    (--`!(l:('a)list). (0 < LENGTH l) = (~(NULL l))`--),
    LIST_INDUCT_TAC THENL[
      REWRITE_TAC [LENGTH,NULL,NOT_LESS_0],
      REWRITE_TAC [LENGTH,NULL,LESS_0]]);

val REVERSE_SNOC = store_thm("REVERSE_SNOC",
    (--`!(x:'a) l. REVERSE (SNOC x l) = CONS x (REVERSE l)`--),
    GEN_TAC THEN LIST_INDUCT_TAC
    THEN ASM_REWRITE_TAC[SNOC,REVERSE]);

val REVERSE_REVERSE = store_thm ("REVERSE_REVERSE",
    (--`!l:('a)list. REVERSE (REVERSE l) = l`--),
    LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[REVERSE,REVERSE_SNOC]);

val forall_REVERSE = TAC_PROOF(([],
    (--`!P. (!l:('a)list. P(REVERSE l)) = (!l. P l)`--)),
    GEN_TAC THEN EQ_TAC THEN DISCH_TAC THEN GEN_TAC
    THEN POP_ASSUM (ACCEPT_TAC o (REWRITE_RULE[REVERSE_REVERSE]
     o (SPEC (--`REVERSE l:('a)list`--)))));

val f_REVERSE_lemma = TAC_PROOF (([],
    (--`!f1 f2.
    ((\x. (f1:('a)list->'b) (REVERSE x)) = (\x. f2 (REVERSE x))) = (f1 = f2)`--)),
    REPEAT GEN_TAC THEN EQ_TAC THEN DISCH_TAC THENL[
      POP_ASSUM (fn x => ACCEPT_TAC (EXT (REWRITE_RULE[REVERSE_REVERSE]
      (GEN (--`x:('a)list`--) (BETA_RULE (AP_THM x (--`REVERSE (x:('a)list)`--))))))),
      ASM_REWRITE_TAC[]]);

val SNOC_Axiom = store_thm("SNOC_Axiom",
 (--`!(e:'b) (f:'b -> ('a -> (('a)list -> 'b))).
  ?! fn1. (fn1[] = e) /\ (!x l. fn1(SNOC x l) = f(fn1 l)x l)`--),

 let val  lemma =  CONV_RULE (EXISTS_UNIQUE_CONV)
       (REWRITE_RULE[REVERSE_REVERSE] (BETA_RULE (SPECL
    	 [(--`e:'b`--),(--`(\ft x l. f ft x (REVERSE l)):'b -> ('a -> (('a)list -> 'b))`--)]
        (PURE_ONCE_REWRITE_RULE
    	 [SYM (CONJUNCT1 REVERSE),
    	  PURE_ONCE_REWRITE_RULE[SYM (SPEC_ALL REVERSE_SNOC)]
    	   (BETA_RULE (SPEC (--`\l:('a)list.fn1(CONS x l) =
    	    	       (f:'b -> ('a -> (('a)list -> 'b)))(fn1 l)x l`--)
    	     (CONV_RULE (ONCE_DEPTH_CONV SYM_CONV) forall_REVERSE)))]
    	    list_Axiom))))
 in
    REPEAT GEN_TAC THEN CONV_TAC EXISTS_UNIQUE_CONV
    THEN STRIP_ASSUME_TAC lemma THEN CONJ_TAC THENL
    [
      EXISTS_TAC (--`(fn1:('a)list->'b) o REVERSE`--)
      THEN REWRITE_TAC[o_DEF] THEN BETA_TAC THEN ASM_REWRITE_TAC[],

      REPEAT GEN_TAC THEN POP_ASSUM (ACCEPT_TAC o SPEC_ALL o
    	REWRITE_RULE[REVERSE_REVERSE,f_REVERSE_lemma] o
        BETA_RULE o REWRITE_RULE[o_DEF] o
        SPECL [(--`(fn1' o REVERSE):('a)list->'b`--),(--`(fn1'' o REVERSE):('a)list->'b`--)])
     ]
  end);

val SNOC_INDUCT = save_thm("SNOC_INDUCT", prove_induction_thm SNOC_Axiom);
val SNOC_CASES =  save_thm("SNOC_CASES",prove_cases_thm SNOC_INDUCT);

val LENGTH_SNOC = store_thm("LENGTH_SNOC",
    (--`!(x:'a) l. LENGTH (SNOC x l) = SUC (LENGTH l)`--),
    GEN_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC [LENGTH,SNOC]);

val NOT_NULL_SNOC = prove(
    (--`!(x:'a) l. ~NULL(SNOC x l)`--),
    GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[SNOC,NULL]);

(* NOT_NIL_SNOC = |- !x l. ~([] = SNOC x l) *)
val NOT_NIL_SNOC = store_thm("NOT_NIL_SNOC",
    (--`!(x:'a) l. ~([] = SNOC x l)`--),
   REWRITE_TAC [prove_constructors_distinct SNOC_Axiom]);

(* NOT_SNOC_NIL = |- !x l. ~(SNOC x l = []) *)
val NOT_SNOC_NIL = save_thm("NOT_SNOC_NIL",
    GSYM NOT_NIL_SNOC);

val SNOC_11 =  save_thm("SNOC_11",prove_constructors_one_one SNOC_Axiom);

val SNOC_EQ_LENGTH_EQ = store_thm ("SNOC_EQ_LENGTH_EQ",
    (--`!x1 (l1:('a)list) x2 l2.
         ((SNOC x1 l1) = (SNOC x2 l2)) ==> (LENGTH l1 = LENGTH l2)`--),
    REPEAT STRIP_TAC THEN RULE_ASSUM_TAC (AP_TERM (--`LENGTH:('a)list -> num`--))
    THEN RULE_ASSUM_TAC(REWRITE_RULE [LENGTH_SNOC,LENGTH,EQ_MONO_ADD_EQ,ADD1])
    THEN FIRST_ASSUM ACCEPT_TAC);

val SNOC_REVERSE_CONS = store_thm ("SNOC_REVERSE_CONS",
   (--`!(x:'a) l. (SNOC x l) = REVERSE (CONS x (REVERSE l))`--),
  let val th =
    GEN_ALL (REWRITE_RULE [REVERSE_REVERSE]
     (AP_TERM (--`REVERSE:('a)list -> ('a)list`--) (SPEC_ALL REVERSE_SNOC)))
  in
    REWRITE_TAC[th]
  end);

val SNOC_APPEND = store_thm("SNOC_APPEND",
   (--`!x (l:('a) list). SNOC x l = APPEND l [x]`--),
   GEN_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC [SNOC,APPEND]);

val MAP_SNOC  = store_thm("MAP_SNOC",
    (--`!(f:'a->'b) x (l:'a list). MAP f(SNOC x l) = SNOC(f x)(MAP f l)`--),
     (REWRITE_TAC [SNOC_APPEND,MAP_APPEND,MAP]));

val FOLDR_SNOC = store_thm("FOLDR_SNOC",
    (--`!(f:'a->'b->'b) e x l. FOLDR f e (SNOC x l) = FOLDR f (f x e) l`--),
    REPEAT (FILTER_GEN_TAC (--`l:'a list`--))
    THEN LIST_INDUCT_TAC THEN REWRITE_TAC[SNOC,FOLDR]
    THEN REPEAT GEN_TAC THEN ASM_REWRITE_TAC[]);

val FOLDL_SNOC = store_thm("FOLDL_SNOC",
    (--`!(f:'b->'a->'b) e x l. FOLDL f e (SNOC x l) = f (FOLDL f e l) x`--),
    let val lem = prove(
        (--`!l (f:'b->'a->'b) e x. FOLDL f e (SNOC x l) = f (FOLDL f e l) x`--),
    	LIST_INDUCT_TAC THEN REWRITE_TAC[SNOC,FOLDL]
        THEN REPEAT GEN_TAC THEN ASM_REWRITE_TAC[])
   in
    MATCH_ACCEPT_TAC lem
   end);

val SNOC_INDUCT_TAC = INDUCT_THEN SNOC_INDUCT ASSUME_TAC;

val FOLDR_FOLDL = store_thm("FOLDR_FOLDL",
    (--`!(f:'a->'a->'a) e. MONOID f e ==> !l. FOLDR f e l = FOLDL f e l`--),
    REPEAT GEN_TAC
    THEN REWRITE_TAC[MONOID_DEF,ASSOC_DEF,LEFT_ID_DEF,RIGHT_ID_DEF]
    THEN STRIP_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[FOLDL, FOLDR]
    THEN FIRST_ASSUM SUBST1_TAC THEN GEN_TAC
    THEN SPEC_TAC ((--`l:'a list`--),(--`l:'a list`--)) THEN SNOC_INDUCT_TAC THENL[
      ASM_REWRITE_TAC[FOLDL],
      PURE_ONCE_REWRITE_TAC[FOLDL_SNOC] THEN GEN_TAC
      THEN ASM_REWRITE_TAC[]]);

val LENGTH_FOLDR = store_thm("LENGTH_FOLDR",
    (--`!l:'a list. LENGTH l = FOLDR (\x l'. SUC l') 0 l`--),
    LIST_INDUCT_TAC THEN REWRITE_TAC[LENGTH,FOLDR]
    THEN CONV_TAC (ONCE_DEPTH_CONV BETA_CONV)
    THEN ASM_REWRITE_TAC[]);

val LENGTH_FOLDL = store_thm("LENGTH_FOLDL",
    (--`!l:'a list. LENGTH l = FOLDL (\l' x. SUC l') 0 l`--),
    SNOC_INDUCT_TAC THEN REWRITE_TAC[LENGTH_SNOC,FOLDL_SNOC] THENL[
      REWRITE_TAC[LENGTH,FOLDL],
      CONV_TAC (ONCE_DEPTH_CONV BETA_CONV)
      THEN CONV_TAC (ONCE_DEPTH_CONV BETA_CONV)
      THEN ASM_REWRITE_TAC[]]);

val MAP_FOLDR = store_thm("MAP_FOLDR",
    (--`!(f:'a->'b) l. MAP f l = FOLDR (\x l'. CONS (f x) l') [] l`--),
    GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[MAP,FOLDR]
    THEN GEN_TAC THEN CONV_TAC (DEPTH_CONV BETA_CONV)
    THEN ASM_REWRITE_TAC[]);

val MAP_FOLDL = store_thm("MAP_FOLDL",
    (--`!(f:'a->'b) l. MAP f l = FOLDL (\l' x. SNOC (f x) l') [] l`--),
    GEN_TAC THEN SNOC_INDUCT_TAC THEN REWRITE_TAC[MAP_SNOC,FOLDL_SNOC] THENL[
      REWRITE_TAC[FOLDL,MAP],
      FIRST_ASSUM (SUBST1_TAC o SYM) THEN CONV_TAC (DEPTH_CONV BETA_CONV)
      THEN GEN_TAC THEN REFL_TAC]);

val MAP_o = store_thm("MAP_o",
    (--`!f:'b->'c. !g:'a->'b.  MAP (f o g) = (MAP f) o (MAP g)`--),
    REPEAT GEN_TAC THEN CONV_TAC FUN_EQ_CONV
    THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC [MAP,o_THM]);

val MAP_MAP_o = store_thm("MAP_MAP_o",
    (--`!(f:'b->'c) (g:'a->'b) l. MAP f (MAP g l) = MAP (f o g) l`--),
    REPEAT GEN_TAC THEN REWRITE_TAC [MAP_o,o_DEF]
    THEN BETA_TAC THEN REFL_TAC);

val FILTER_FOLDR = store_thm("FILTER_FOLDR",
    (--`!P (l:'a list). FILTER P l = FOLDR (\x l'. P x => CONS x l' | l') [] l`--),
    GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[FILTER,FOLDR]
    THEN CONV_TAC (DEPTH_CONV BETA_CONV) THEN ASM_REWRITE_TAC[]);

val FILTER_SNOC = store_thm("FILTER_SNOC",
    (--`!P (x:'a) l. FILTER P (SNOC x l) = 
    	(P x => SNOC x (FILTER P l) | FILTER P l)`--),
    GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC
    THEN REWRITE_TAC[FILTER,SNOC]
    THEN GEN_TAC THEN REPEAT COND_CASES_TAC
    THEN ASM_REWRITE_TAC[SNOC]);

val FILTER_FOLDL = store_thm("FILTER_FOLDL",
    (--`!P (l:'a list). FILTER P l = FOLDL (\l' x. P x => SNOC x l' | l') [] l`--),
    GEN_TAC THEN SNOC_INDUCT_TAC THENL[
      REWRITE_TAC[FILTER,FOLDL],
      REWRITE_TAC[FILTER_SNOC,FOLDL_SNOC]
      THEN CONV_TAC (DEPTH_CONV BETA_CONV) THEN ASM_REWRITE_TAC[]]);

val FILTER_COMM = store_thm("FILTER_COMM",
    (--`!f1 f2 (l:'a list). FILTER f1 (FILTER f2 l) = FILTER f2 (FILTER f1 l)`--),
    GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[FILTER]
    THEN GEN_TAC THEN REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[FILTER]);

val FILTER_IDEM = store_thm("FILTER_IDEM",
    (--`!f (l:'a list). FILTER f (FILTER f l) = FILTER f l`--),
    GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[FILTER]
    THEN GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[FILTER]);

val FILTER_MAP = store_thm("FILTER_MAP",
    (--`!f1 (f2:'a->'b) (l:'a list).
     FILTER f1 (MAP f2 l) = MAP f2 (FILTER (f1 o f2) l)`--),
    GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[FILTER,MAP]
    THEN GEN_TAC THEN PURE_ONCE_REWRITE_TAC[o_THM]
    THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[FILTER,MAP]);

(*- 18 Nov. 93 -*)
val LENGTH_SEG = store_thm("LENGTH_SEG",
    (--`!n k (l:'a list). ((n + k) <= (LENGTH l)) ==> (LENGTH (SEG n k l) = n)`--),
    REPEAT INDUCT_TAC THENL[
      REWRITE_TAC[SEG,LENGTH],
      REWRITE_TAC[SEG,LENGTH],
      LIST_INDUCT_TAC THENL[
    	REWRITE_TAC[LENGTH,ADD_0,LESS_OR_EQ,NOT_SUC,NOT_LESS_0],
        REWRITE_TAC[SEG,LENGTH,ADD,LESS_EQ_MONO,INV_SUC_EQ] 
    	THEN FIRST_ASSUM (MATCH_ACCEPT_TAC o (SPEC (--`0`--)))],
      LIST_INDUCT_TAC THENL[
    	REWRITE_TAC[LENGTH,ADD,LESS_OR_EQ,NOT_SUC,NOT_LESS_0],
        REWRITE_TAC[LENGTH,SEG,(GSYM ADD_SUC),LESS_EQ_MONO]
    	THEN FIRST_ASSUM MATCH_ACCEPT_TAC]]);

val APPEND_NIL = store_thm("APPEND_NIL",
    (--`(!l:('a)list . APPEND l [] = l) /\ (!l:('a)list . APPEND [] l = l)`--),
    CONJ_TAC THENL
       [LIST_INDUCT_TAC,ALL_TAC] THEN ASM_REWRITE_TAC [APPEND]);

val APPEND_SNOC = store_thm("APPEND_SNOC",
    (--`!l1 (x:'a) l2. APPEND l1 (SNOC x l2) = SNOC x (APPEND l1 l2)`--),
    LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[APPEND,SNOC]);

val REVERSE_APPEND = store_thm ("REVERSE_APPEND",
    (--`!(l1:('a)list) l2.
     REVERSE (APPEND l1 l2) = (APPEND (REVERSE l2) (REVERSE l1))`--),
    LIST_INDUCT_TAC
    THEN ASM_REWRITE_TAC[APPEND,APPEND_NIL,REVERSE,APPEND_SNOC]);

val APPEND_FOLDR = store_thm("APPEND_FOLDR",
    (--`!(l1:'a list) l2. APPEND l1 l2  = FOLDR CONS l2 l1`--),
    LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[APPEND,FOLDR]);

val APPEND_FOLDL = store_thm("APPEND_FOLDL",
    (--`!(l1:'a list) l2. APPEND l1 l2  = FOLDL (\l' x. SNOC x l') l1 l2`--),
    GEN_TAC THEN SNOC_INDUCT_TAC THENL[
     REWRITE_TAC[APPEND_NIL,FOLDL],
     ASM_REWRITE_TAC[APPEND_SNOC,FOLDL_SNOC] THEN GEN_TAC
     THEN CONV_TAC (DEPTH_CONV BETA_CONV) THEN REFL_TAC]);

val FOLDR_APPEND = store_thm("FOLDR_APPEND",
    (--`!(f:'a->'b->'b) e l1 l2.
     FOLDR f e (APPEND l1 l2) = FOLDR f (FOLDR f e l2) l1`--),
    FORALL_PERM_TAC[(--`l2:'a list`--)] THEN SNOC_INDUCT_TAC THENL[
      REWRITE_TAC[APPEND_NIL,FOLDR],
      REWRITE_TAC[APPEND_SNOC,FOLDR_SNOC] THEN REPEAT GEN_TAC
      THEN FIRST_ASSUM MATCH_ACCEPT_TAC]);

val FOLDL_APPEND = store_thm("FOLDL_APPEND",
    (--`!(f:'a->'b->'a) e l1 l2.
     FOLDL f e (APPEND l1 l2) = FOLDL f (FOLDL f e l1) l2`--),
    FORALL_PERM_TAC[(--`l1:'b list`--)] THEN LIST_INDUCT_TAC
    THEN REWRITE_TAC[APPEND,FOLDL] THEN REPEAT GEN_TAC
    THEN FIRST_ASSUM MATCH_ACCEPT_TAC);


val CONS_APPEND = store_thm("CONS_APPEND",
    (--`!(x:'a) l. CONS x l = APPEND [x] l`--),
    GEN_TAC THEN SNOC_INDUCT_TAC THENL[
      REWRITE_TAC[APPEND_NIL],
      ASM_REWRITE_TAC[APPEND_SNOC,(GSYM(CONJUNCT2 SNOC))]]);

val ASSOC_APPEND = store_thm ("ASSOC_APPEND",
    (--`ASSOC (APPEND:'a list -> 'a list -> 'a list)`--),
    REWRITE_TAC[ASSOC_DEF,APPEND_ASSOC]);

val RIGHT_ID_APPEND_NIL = prove(
    (--`RIGHT_ID APPEND ([]:'a list)`--),
    REWRITE_TAC[RIGHT_ID_DEF,APPEND,APPEND_NIL]);

val LEFT_ID_APPEND_NIL = prove(
    (--`LEFT_ID APPEND ([]:'a list)`--),
    REWRITE_TAC[LEFT_ID_DEF,APPEND,APPEND_NIL]);

val MONOID_APPEND_NIL = store_thm ("MONOID_APPEND_NIL",
    (--`MONOID APPEND ([]:'a list)`--),
    REWRITE_TAC[MONOID_DEF,APPEND,APPEND_NIL,APPEND_ASSOC,
            LEFT_ID_DEF,ASSOC_DEF,RIGHT_ID_DEF]);

val APPEND_LENGTH_EQ = store_thm("APPEND_LENGTH_EQ",
 (--`!l1 l1'. (LENGTH l1 = LENGTH l1') ==>
     !l2 l2':'a list. (LENGTH l2 = LENGTH l2') ==>
     ((APPEND l1 l2 = APPEND l1' l2') = ((l1 = l1') /\ (l2 = l2')))`--),
    let val APPEND_11 = prove(
    	(--`!(x:'a list) (y:'a list) (z:'a list).
    	 ((APPEND x y) = (APPEND x z)) = (y = z)`--),
    	LIST_INDUCT_TAC THEN ASM_REWRITE_TAC [APPEND,CONS_11])
    and EQ_LENGTH_INDUCT_TAC =
    	LIST_INDUCT_TAC THENL[
         LIST_INDUCT_TAC THENL[ 
    	  REPEAT (CONV_TAC FORALL_IMP_CONV) THEN DISCH_THEN (fn t => ALL_TAC),
          REWRITE_TAC[LENGTH,SUC_NOT]],
    	 GEN_TAC THEN LIST_INDUCT_TAC
    	 THEN REWRITE_TAC[LENGTH,NOT_SUC,INV_SUC_EQ]
     	 THEN GEN_TAC THEN REPEAT (CONV_TAC FORALL_IMP_CONV) THEN DISCH_TAC]
    in
    EQ_LENGTH_INDUCT_TAC THEN REWRITE_TAC[APPEND]
    THEN EQ_LENGTH_INDUCT_TAC THEN REWRITE_TAC[APPEND_11,CONS_11,APPEND_NIL]
    THEN FIRST_ASSUM (fn t => ASSUME_TAC
      (MATCH_MP t (ASSUME(--`LENGTH (l1:'a list) = LENGTH (l1':'a list)`--))))
    THEN POP_ASSUM (ASSUME_TAC o (REWRITE_RULE[LENGTH,INV_SUC_EQ]) o
    (SPECL[(--`CONS x'' l2:'a list`--),(--`CONS x''' l2':'a list`--)]))
(* **list_Axiom** variable dependancy *)
(*     (SPECL[(--`CONS h'' l2:'a list`--),(--`CONS h''' l2':'a list`--)])) *)
    THEN POP_ASSUM (fn t1 => FIRST_ASSUM (fn t2 =>  SUBST1_TAC (MP t1 t2)))
    THEN REWRITE_TAC[CONS_11,CONJ_ASSOC]
    end);

val FILTER_APPEND = store_thm("FILTER_APPEND",
    (--`!f l1 (l2:'a list).
     FILTER f (APPEND l1 l2) = APPEND (FILTER f l1) (FILTER f l2)`--),
    GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[FILTER,APPEND]
    THEN REPEAT GEN_TAC THEN COND_CASES_TAC
    THEN ASM_REWRITE_TAC[APPEND]);

val FLAT_SNOC = store_thm("FLAT_SNOC",
    (--`!(x:'a list) l. FLAT (SNOC x l) = APPEND (FLAT l) x`--),
    GEN_TAC THEN LIST_INDUCT_TAC
    THEN ASM_REWRITE_TAC[FLAT,SNOC,APPEND,APPEND_NIL,APPEND_ASSOC]);

val FLAT_FOLDR = store_thm("FLAT_FOLDR",
    (--`!l:'a list list. FLAT l = FOLDR APPEND [] l`--),
    LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[FLAT,FOLDR]);

val FLAT_FOLDL = store_thm("FLAT_FOLDL",
    (--`!l:'a list list. FLAT l = FOLDL APPEND [] l`--),
    SNOC_INDUCT_TAC THENL[
      REWRITE_TAC[FLAT,FOLDL],
      ASM_REWRITE_TAC[FLAT_SNOC,FOLDL_SNOC]]);

val LENGTH_FLAT = store_thm("LENGTH_FLAT",
    (--`!l:'a list list. LENGTH(FLAT l) = SUM (MAP LENGTH l)`--),
    LIST_INDUCT_TAC THEN REWRITE_TAC[FLAT] THENL[
      REWRITE_TAC[LENGTH,MAP,SUM],
      ASM_REWRITE_TAC[LENGTH_APPEND,MAP,SUM]]);

val REVERSE_FOLDR = store_thm("REVERSE_FOLDR",
    (--`!l:'a list. REVERSE l = FOLDR SNOC [] l`--),
    LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[REVERSE,FOLDR]);

val REVERSE_FOLDL = store_thm("REVERSE_FOLDL",
    (--`!l:'a list. REVERSE l = FOLDL (\l' x. CONS x l') [] l`--),
    SNOC_INDUCT_TAC THENL[
      REWRITE_TAC[REVERSE,FOLDL],
      REWRITE_TAC[REVERSE_SNOC,FOLDL_SNOC]
      THEN CONV_TAC (DEPTH_CONV BETA_CONV) THEN ASM_REWRITE_TAC[]]);

val LENGTH_REVERSE = store_thm("LENGTH_REVERSE",
    (--`!l:('a)list. LENGTH (REVERSE l) = LENGTH l`--),
    LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[LENGTH,REVERSE,LENGTH_SNOC]);

val REVERSE_EQ_NIL = store_thm("REVERSE_EQ_NIL",
    (--`!l:'a list. (REVERSE l = []) = (l = [])`--),
    LIST_INDUCT_TAC THEN REWRITE_TAC[REVERSE,NOT_CONS_NIL,NOT_SNOC_NIL]);

val ALL_EL_SNOC = store_thm("ALL_EL_SNOC",
    (--`!P (x:'a) l. ALL_EL P (SNOC x l) = ALL_EL P l /\ P x`--),
    GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC
    THEN ASM_REWRITE_TAC[SNOC,ALL_EL,CONJ_ASSOC]);

val ALL_EL_CONJ = store_thm("ALL_EL_CONJ",
     (--`!P Q l. ALL_EL (\x:'a. P x /\ Q x) l = (ALL_EL P l /\ ALL_EL Q l)`--),
     GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC
     THEN ASM_REWRITE_TAC [ALL_EL] THEN BETA_TAC
     THEN REPEAT (STRIP_TAC ORELSE EQ_TAC) THEN FIRST_ASSUM ACCEPT_TAC);

val ALL_EL_MAP = store_thm("ALL_EL_MAP",
    (--`!P (f:'a->'b) l. ALL_EL P (MAP f l) = ALL_EL (P o f) l`--),
    GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC
    THEN REWRITE_TAC [ALL_EL,MAP] THEN ASM_REWRITE_TAC [o_DEF]
    THEN BETA_TAC THEN REWRITE_TAC[]);

val ALL_EL_APPEND = store_thm("ALL_EL_APPEND",
    (--`!P (l1:('a)list) l2.
     (ALL_EL P (APPEND l1 l2)) = ((ALL_EL P l1) /\ (ALL_EL P l2))`--),
   GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC [APPEND,ALL_EL]
   THEN ASM_REWRITE_TAC [] THEN REWRITE_TAC [CONJ_ASSOC]);

val SOME_EL_SNOC = store_thm("SOME_EL_SNOC",
    (--`!P (x:'a) l. SOME_EL P (SNOC x l) = P x \/ (SOME_EL P l)`--),
    GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC
    THEN ASM_REWRITE_TAC[SNOC,SOME_EL] THEN GEN_TAC
    THEN PURE_ONCE_REWRITE_TAC[DISJ_ASSOC]
    THEN CONV_TAC ((RAND_CONV o RATOR_CONV o ONCE_DEPTH_CONV)
     (REWR_CONV DISJ_SYM)) THEN REFL_TAC);

val NOT_ALL_EL_SOME_EL = store_thm("NOT_ALL_EL_SOME_EL",
    (--`!P (l:'a list). ~(ALL_EL P l) = SOME_EL ($~ o P) l`--),
    GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[ALL_EL,SOME_EL]
    THEN GEN_TAC THEN PURE_ONCE_REWRITE_TAC[DE_MORGAN_THM,o_THM]
    THEN FIRST_ASSUM SUBST1_TAC THEN REFL_TAC);

val NOT_SOME_EL_ALL_EL = store_thm("NOT_SOME_EL_ALL_EL",
    (--`!P (l:'a list). ~(SOME_EL P l) = ALL_EL ($~ o P) l`--),
    GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[ALL_EL,SOME_EL]
    THEN GEN_TAC THEN PURE_ONCE_REWRITE_TAC[DE_MORGAN_THM,o_THM]
    THEN FIRST_ASSUM SUBST1_TAC THEN REFL_TAC);

val IS_EL = store_thm("IS_EL",
    (--`(!x:'a. IS_EL x[] = F) /\
     (!(y:'a) x l. IS_EL y(CONS x l) = (y = x) \/ IS_EL y l)`--),
    REWRITE_TAC[IS_EL_DEF,SOME_EL] THEN REPEAT GEN_TAC
    THEN CONV_TAC (ONCE_DEPTH_CONV BETA_CONV) THEN REFL_TAC);

val IS_EL_SNOC = store_thm("IS_EL_SNOC",
    (--`!(y:'a) x l. IS_EL y (SNOC x l) = (y = x) \/ IS_EL y l`--),
    GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC
    THEN ASM_REWRITE_TAC[SNOC,IS_EL] THEN GEN_TAC
    THEN PURE_ONCE_REWRITE_TAC[DISJ_ASSOC]
    THEN CONV_TAC ((RAND_CONV o RATOR_CONV o ONCE_DEPTH_CONV)
     (REWR_CONV DISJ_SYM)) THEN REFL_TAC);

val SUM_SNOC = store_thm("SUM_SNOC",
    (--`!x l. SUM (SNOC x l) = (SUM l) + x`--),
    GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[SUM,SNOC,ADD,ADD_0]
    THEN GEN_TAC THEN ASM_REWRITE_TAC[ADD_ASSOC]);

val SUM_FOLDR = store_thm("SUM_FOLDR",
    (--`!l:num list. SUM l = FOLDR $+ 0 l`--),
    LIST_INDUCT_TAC THEN REWRITE_TAC[SUM,FOLDR,ADD]
    THEN GEN_TAC THEN CONV_TAC (DEPTH_CONV BETA_CONV)
    THEN FIRST_ASSUM SUBST1_TAC THEN REFL_TAC);

val SUM_FOLDL = store_thm("SUM_FOLDL",
    (--`!l:num list. SUM l = FOLDL $+ 0 l`--),
    SNOC_INDUCT_TAC THENL[
      REWRITE_TAC[SUM,FOLDL],
      REWRITE_TAC[SUM_SNOC,FOLDL_SNOC]
      THEN GEN_TAC THEN CONV_TAC (DEPTH_CONV BETA_CONV)
      THEN FIRST_ASSUM SUBST1_TAC THEN REFL_TAC]);


val IS_PREFIX_APPEND = store_thm("IS_PREFIX_APPEND",
    (--`!l1 l2:'a list. (IS_PREFIX l1 l2 = (?l. l1 = APPEND l2 l))`--),
    LIST_INDUCT_TAC THENL[
     LIST_INDUCT_TAC THENL[
      REWRITE_TAC[IS_PREFIX,APPEND]
      THEN EXISTS_TAC (--`[]:'a list`--) THEN REFL_TAC, 
      REWRITE_TAC[IS_PREFIX,APPEND,GSYM NOT_CONS_NIL]],
     GEN_TAC THEN LIST_INDUCT_TAC THENL[
      REWRITE_TAC[IS_PREFIX,APPEND]
      THEN EXISTS_TAC (--`CONS (x:'a) l1`--) THEN REFL_TAC,
(* **list_Axiom** variable dependancy *)
(*      THEN EXISTS_TAC (--`CONS (h:'a) l1`--) THEN REFL_TAC, *)
      ASM_REWRITE_TAC[IS_PREFIX,APPEND,CONS_11] THEN GEN_TAC
      THEN CONV_TAC (RAND_CONV EXISTS_AND_CONV) THEN REFL_TAC]]);

val IS_SUFFIX_APPEND = store_thm("IS_SUFFIX_APPEND",
    (--`!l1 l2:'a list. (IS_SUFFIX l1 l2 = (?l. l1 = APPEND l l2))`--),
    SNOC_INDUCT_TAC THENL[
     SNOC_INDUCT_TAC THENL[
      REWRITE_TAC[IS_SUFFIX,APPEND_NIL]
      THEN EXISTS_TAC (--`[]:'a list`--) THEN REFL_TAC,
      REWRITE_TAC[IS_SUFFIX,APPEND_SNOC]
      THEN CONV_TAC (ONCE_DEPTH_CONV SYM_CONV)
      THEN REWRITE_TAC[GSYM NULL_EQ_NIL,NOT_NULL_SNOC]],
     GEN_TAC THEN SNOC_INDUCT_TAC THENL[
      REWRITE_TAC[IS_SUFFIX,APPEND_NIL]
      THEN EXISTS_TAC (--`SNOC (x:'a) l1`--) THEN REFL_TAC,
      ASM_REWRITE_TAC[IS_SUFFIX,APPEND_SNOC,SNOC_11] THEN GEN_TAC
      THEN CONV_TAC (RAND_CONV EXISTS_AND_CONV) THEN REFL_TAC]]);

val IS_SUBLIST_APPEND = store_thm("IS_SUBLIST_APPEND",
 --`!l1 l2:'a list. IS_SUBLIST l1 l2 = (?l l'. l1 = APPEND l(APPEND l2 l'))`--,
    let val NOT_NIL_APPEND_CONS2 = prove(
    	(--`!l1 (l2:'a list) x. ~([] = (APPEND l1 (CONS x l2)))`--),
    	LIST_INDUCT_TAC THEN REWRITE_TAC[APPEND] THEN REPEAT GEN_TAC
        THEN MATCH_ACCEPT_TAC (GSYM NOT_CONS_NIL))
   in
    LIST_INDUCT_TAC THEN REPEAT (FILTER_GEN_TAC (--`l2:'a list`--))
    THEN LIST_INDUCT_TAC THENL[
    	REWRITE_TAC[IS_SUBLIST,APPEND]
        THEN MAP_EVERY EXISTS_TAC [(--`[]:'a list`--), (--`[]:'a list`--)]
    	THEN REWRITE_TAC[APPEND],
        GEN_TAC THEN REWRITE_TAC[IS_SUBLIST,APPEND,NOT_NIL_APPEND_CONS2],
        REWRITE_TAC[IS_SUBLIST,APPEND]
    	THEN MAP_EVERY EXISTS_TAC [(--`[x]:'a list`--), (--`l1:'a list`--)]
(* **list_Axiom** variable dependancy *)
(*     	THEN MAP_EVERY EXISTS_TAC [(--`[h]:'a list`--), (--`l1:'a list`--)] *)
        THEN MATCH_ACCEPT_TAC CONS_APPEND,
    	GEN_TAC THEN REWRITE_TAC[IS_SUBLIST] THEN EQ_TAC 
        THEN ONCE_ASM_REWRITE_TAC[IS_PREFIX_APPEND] THENL[
    	  STRIP_TAC THENL[
    	    MAP_EVERY EXISTS_TAC [(--`[]:'a list`--), (--`l:'a list`--)]
    	    THEN ASM_REWRITE_TAC[APPEND],
    	    MAP_EVERY EXISTS_TAC [(--`(CONS x l):'a list`--), 
                                  (--`l':'a list`--)]
(* **list_Axiom** variable dependancy *)
(*    	    MAP_EVERY EXISTS_TAC [(--`(CONS h l):'a list`--), 
                                  (--`l':'a list`--)] *)
    	    THEN ONCE_ASM_REWRITE_TAC[APPEND] THEN REFL_TAC],
          CONV_TAC LEFT_IMP_EXISTS_CONV THEN LIST_INDUCT_TAC THENL[
    	    REWRITE_TAC[APPEND,CONS_11] THEN STRIP_TAC THEN DISJ1_TAC
    	    THEN ASM_REWRITE_TAC[IS_PREFIX_APPEND]
    	    THEN EXISTS_TAC (--`l':'a list`--) THEN REFL_TAC,
    	    GEN_TAC THEN REWRITE_TAC[APPEND,CONS_11]
    	    THEN STRIP_TAC THEN DISJ2_TAC
    	    THEN MAP_EVERY EXISTS_TAC [(--`l:'a list`--), (--`l':'a list`--)]
    	    THEN FIRST_ASSUM ACCEPT_TAC]]]
    end);

val IS_PREFIX_IS_SUBLIST = store_thm("IS_PREFIX_IS_SUBLIST",
    (--`!l1 l2:'a list. IS_PREFIX l1 l2 ==> IS_SUBLIST l1 l2`--),
    LIST_INDUCT_TAC THEN TRY (FILTER_GEN_TAC (--`l2:'a list`--))
    THEN LIST_INDUCT_TAC THEN REWRITE_TAC[IS_PREFIX,IS_SUBLIST]
    THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[]);

val IS_SUFFIX_IS_SUBLIST = store_thm("IS_SUFFIX_IS_SUBLIST",
    (--`!l1 l2:'a list. IS_SUFFIX l1 l2 ==> IS_SUBLIST l1 l2`--),
    REPEAT GEN_TAC THEN REWRITE_TAC[IS_SUFFIX_APPEND,IS_SUBLIST_APPEND]
    THEN DISCH_THEN (CHOOSE_THEN SUBST1_TAC)
    THEN MAP_EVERY EXISTS_TAC [(--`l:'a list`--), (--`[]:'a list`--)]
    THEN REWRITE_TAC[APPEND_NIL]);

val IS_PREFIX_REVERSE = store_thm("IS_PREFIX_REVERSE",
--`!l1 l2:'a list. IS_PREFIX (REVERSE l1) (REVERSE l2) = IS_SUFFIX l1 l2`--,
    let val NOT_NIL_APPEND_SNOC2 = prove(
        (--`!l1 (l2:'a list) x. ~([] = (APPEND l1 (SNOC x l2)))`--),
    	LIST_INDUCT_TAC THEN REWRITE_TAC[APPEND_SNOC] THEN REPEAT GEN_TAC
    	THEN MATCH_ACCEPT_TAC NOT_NIL_SNOC)
    in
    SNOC_INDUCT_TAC THEN REPEAT (FILTER_GEN_TAC (--`l2:'a list`--))
    THEN SNOC_INDUCT_TAC THENL[
        REWRITE_TAC[IS_SUFFIX_APPEND,REVERSE,IS_PREFIX]
    	THEN EXISTS_TAC (--`[]:'a list`--) THEN REWRITE_TAC[APPEND],
        GEN_TAC THEN REWRITE_TAC[IS_SUFFIX_APPEND,REVERSE,REVERSE_SNOC,
                                 IS_PREFIX]
    	THEN CONV_TAC NOT_EXISTS_CONV THEN GEN_TAC
        THEN REWRITE_TAC[APPEND,NOT_NIL_APPEND_SNOC2],
    	REWRITE_TAC[IS_SUFFIX_APPEND,REVERSE,APPEND_NIL,IS_PREFIX]
        THEN EXISTS_TAC (--`SNOC (x:'a) l1`--) THEN REFL_TAC,
    	GEN_TAC THEN REWRITE_TAC[IS_SUFFIX_APPEND,REVERSE_SNOC,IS_PREFIX]
        THEN PURE_ONCE_ASM_REWRITE_TAC[]
    	THEN REWRITE_TAC[IS_SUFFIX_APPEND,APPEND_SNOC,SNOC_11]
        THEN CONV_TAC (ONCE_DEPTH_CONV EXISTS_AND_CONV) THEN REFL_TAC]
    end);

val IS_SUFFIX_REVERSE = save_thm("IS_SUFFIX_REVERSE",
 (* `!l1 l2:'a list. IS_SUFFIX (REVERSE l1) (REVERSE l2) = IS_PREFIX l1 l2` *)
    GEN_ALL(SYM (REWRITE_RULE[REVERSE_REVERSE]
    (SPECL [(--`REVERSE(l1:'a list)`--), (--`REVERSE(l2:'a list)`--)] 
           IS_PREFIX_REVERSE))));

val IS_SUBLIST_REVERSE = store_thm("IS_SUBLIST_REVERSE",
--`!l1 l2:'a list. IS_SUBLIST (REVERSE l1) (REVERSE l2) = IS_SUBLIST l1 l2`--,
    REPEAT GEN_TAC THEN REWRITE_TAC[IS_SUBLIST_APPEND]
    THEN EQ_TAC THEN STRIP_TAC THENL[
      MAP_EVERY EXISTS_TAC [(--`REVERSE(l':'a list)`--),
                            (--`REVERSE(l:'a list)`--)]
      THEN FIRST_ASSUM (SUBST1_TAC o
    	 (REWRITE_RULE[REVERSE_REVERSE,REVERSE_APPEND]) o
    	 (AP_TERM (--`REVERSE:'a list -> 'a list`--)))
      THEN REWRITE_TAC[APPEND_ASSOC],
      FIRST_ASSUM SUBST1_TAC
      THEN REWRITE_TAC[REVERSE_APPEND,APPEND_ASSOC]
      THEN MAP_EVERY EXISTS_TAC [(--`REVERSE(l':'a list)`--),
                                 (--`REVERSE(l:'a list)`--)]
      THEN REFL_TAC]);

val PREFIX_FOLDR = store_thm("PREFIX_FOLDR",
--`!P (l:'a list). PREFIX P l = FOLDR (\x l'. P x => CONS x l' | []) [] l`--,
    GEN_TAC THEN  REWRITE_TAC[PREFIX_DEF]
    THEN LIST_INDUCT_TAC THEN REWRITE_TAC[FOLDR,SPLITP]
    THEN GEN_TAC THEN REWRITE_TAC[o_THM] THEN BETA_TAC
    THEN ASM_CASES_TAC (--`(P:'a->bool) x`--) THEN ASM_REWRITE_TAC[]);
(* **list_Axiom** variable dependancy *)
(*    THEN ASM_CASES_TAC (--`(P:'a->bool) h`--) THEN ASM_REWRITE_TAC[]); *)

val PREFIX = store_thm("PREFIX",
   (--`(!P:'a->bool. PREFIX P [] = []) /\
    (!P (x:'a) l. PREFIX P (CONS x l) = (P x => CONS x (PREFIX P l) |[]))`--),
    REWRITE_TAC[PREFIX_FOLDR,FOLDR]
    THEN REPEAT GEN_TAC THEN BETA_TAC THEN REFL_TAC);

val IS_PREFIX_PREFIX = store_thm("IS_PREFIX_PREFIX",
    (--`!P (l:'a list). IS_PREFIX l (PREFIX P l)`--),
    GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[IS_PREFIX,PREFIX]
    THEN GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[IS_PREFIX]);

val LENGTH_SCANL = store_thm("LENGTH_SCANL",
    (--`!(f:'b->'a->'b) e l. LENGTH(SCANL f e l) = SUC (LENGTH l)`--),
    FORALL_PERM_TAC [(--`l:'a list`--)] THEN LIST_INDUCT_TAC
    THEN REWRITE_TAC[SCANL,LENGTH]
    THEN REPEAT GEN_TAC THEN ASM_REWRITE_TAC[]);

val LENGTH_SCANR = store_thm("LENGTH_SCANR",
    (--`!(f:'a->'b->'b) e l. LENGTH(SCANR f e l) = SUC (LENGTH l)`--),
    FORALL_PERM_TAC [(--`l:'a list`--)] THEN LIST_INDUCT_TAC
    THEN REWRITE_TAC[SCANR] THEN CONV_TAC (ONCE_DEPTH_CONV let_CONV)
    THEN REPEAT GEN_TAC THEN ASM_REWRITE_TAC[LENGTH]);


val COMM_MONOID_FOLDL = store_thm("COMM_MONOID_FOLDL",
    (--`!f:'a->'a->'a. COMM f ==>
      !e'. MONOID f e' ==>
       (!e l. FOLDL f e l = f e (FOLDL f e' l))`--),
    REWRITE_TAC[MONOID_DEF,ASSOC_DEF,LEFT_ID_DEF,COMM_DEF]
    THEN REPEAT STRIP_TAC THEN SPEC_TAC ((--`e:'a`--),(--`e:'a`--))
    THEN SPEC_TAC ((--`l:'a list`--),(--`l:'a list`--))
    THEN LIST_INDUCT_TAC THEN PURE_ONCE_REWRITE_TAC[FOLDL] THENL[
      GEN_TAC THEN PURE_ONCE_ASM_REWRITE_TAC[]
      THEN FIRST_ASSUM (MATCH_ACCEPT_TAC o GSYM),
      REPEAT GEN_TAC THEN POP_ASSUM (fn t => PURE_ONCE_REWRITE_TAC[t])
      THEN POP_ASSUM (fn t => PURE_ONCE_REWRITE_TAC[t])
      THEN FIRST_ASSUM (MATCH_ACCEPT_TAC o GSYM)] );

val COMM_MONOID_FOLDR = store_thm("COMM_MONOID_FOLDR",
    (--`!f:'a->'a->'a. COMM f ==>
      !e'. (MONOID f e') ==>
       (!e l. FOLDR f e l = f e (FOLDR f e' l))`--),
    REWRITE_TAC[MONOID_DEF,ASSOC_DEF,LEFT_ID_DEF,COMM_DEF]
    THEN GEN_TAC THEN DISCH_THEN
      (fn th_sym => GEN_TAC THEN DISCH_THEN
        (fn th_assoc_etc =>
                let val th_assoc = CONJUNCT1 th_assoc_etc
    	    	    val th_ident = CONJUNCT2(CONJUNCT2 th_assoc_etc)
                in
            	GEN_TAC THEN LIST_INDUCT_TAC 
    	        THEN PURE_ONCE_REWRITE_TAC[FOLDR] THENL[
                 PURE_ONCE_REWRITE_TAC[th_sym]
    	         THEN MATCH_ACCEPT_TAC (GSYM th_ident),
    	    	 REPEAT GEN_TAC THEN PURE_ONCE_ASM_REWRITE_TAC[]
    	         THEN PURE_ONCE_REWRITE_TAC[th_ident]
    	         THEN PURE_ONCE_REWRITE_TAC[th_assoc]
                 THEN AP_THM_TAC THEN AP_TERM_TAC
    	    	 THEN MATCH_ACCEPT_TAC (GSYM th_sym)]
                end)) );


val FCOMM_FOLDR_APPEND = store_thm("FCOMM_FOLDR_APPEND",
--`!(g:'a->'a->'a) (f:'b->'a->'a). 
   FCOMM g f 
   ==> !e. LEFT_ID g e 
       ==> !l1 l2. FOLDR f e (APPEND l1 l2) 
                 = g (FOLDR f e l1) (FOLDR f e l2)`--,
    REWRITE_TAC[FCOMM_DEF,LEFT_ID_DEF] THEN REPEAT GEN_TAC
    THEN REPEAT DISCH_TAC THEN GEN_TAC THEN DISCH_TAC
    THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[APPEND,FOLDR]);

val FCOMM_FOLDL_APPEND = store_thm("FCOMM_FOLDL_APPEND",
--`!(f:'a->'b->'a) (g:'a->'a->'a). FCOMM f g ==>
   !e. RIGHT_ID g e ==>
   !l1 l2. FOLDL f e (APPEND l1 l2) = g (FOLDL f e l1) (FOLDL f e l2)`--,
    REWRITE_TAC[FCOMM_DEF,RIGHT_ID_DEF] THEN REPEAT GEN_TAC
    THEN DISCH_THEN (ASSUME_TAC o GSYM) THEN GEN_TAC
    THEN DISCH_TAC THEN GEN_TAC THEN SNOC_INDUCT_TAC
    THEN ASM_REWRITE_TAC[APPEND_NIL,APPEND_SNOC,FOLDL_SNOC,FOLDL]);


val MONOID_FOLDR_APPEND_FOLDR = prove(
    (--`!(f:'a->'a->'a) e. MONOID f e ==>
     (!l1 l2. FOLDR f e (APPEND l1 l2) = f (FOLDR f e l1) (FOLDR f e l2))`--),
    REWRITE_TAC[MONOID_DEF,GSYM FCOMM_ASSOC] THEN REPEAT STRIP_TAC
    THEN IMP_RES_TAC FCOMM_FOLDR_APPEND THEN ASM_REWRITE_TAC[]);

val MONOID_FOLDL_APPEND_FOLDL = prove(
    (--`!(f:'a->'a->'a) e. MONOID f e ==>
      (!l1 l2. FOLDL f e (APPEND l1 l2) = f (FOLDL f e l1) (FOLDL f e l2))`--),
    REWRITE_TAC[MONOID_DEF,GSYM FCOMM_ASSOC] THEN REPEAT STRIP_TAC
    THEN IMP_RES_TAC FCOMM_FOLDL_APPEND THEN ASM_REWRITE_TAC[]);


val FOLDL_SINGLE = store_thm("FOLDL_SINGLE",
    (--`!(f:'a->'b->'a) e x. FOLDL f e [x] = f e x`--),
    REWRITE_TAC[FOLDL]);

val FOLDR_SINGLE = store_thm("FOLDR_SINGLE",
    (--`!(f:'a->'b->'b) e x. FOLDR f e [x] = f x e`--),
    REWRITE_TAC[FOLDR]);


val FOLDR_CONS_NIL = store_thm("FOLDR_CONS_NIL",
    (--`!(l:'a list). FOLDR CONS [] l = l`--),
    LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[FOLDR]);

val FOLDL_SNOC_NIL = store_thm("FOLDL_SNOC_NIL",
    (--`!(l:'a list). FOLDL (\xs x. SNOC x xs) [] l = l`--),
    SNOC_INDUCT_TAC THEN ASM_REWRITE_TAC[FOLDL,FOLDL_SNOC]
    THEN BETA_TAC THEN REWRITE_TAC[]);

val FOLDR_FOLDL_REVERSE = store_thm("FOLDR_FOLDL_REVERSE",
    (--`!(f:'a->'b->'b) e l. 
       FOLDR f e l = FOLDL (\x y. f y x) e (REVERSE l)`--),
    GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC
    THEN ASM_REWRITE_TAC[FOLDR,FOLDL,REVERSE,FOLDL_SNOC]
    THEN BETA_TAC THEN REWRITE_TAC[]);

val FOLDL_FOLDR_REVERSE = store_thm("FOLDL_FOLDR_REVERSE",
    (--`!(f:'a->'b->'a) e l. 
       FOLDL f e l = FOLDR (\x y. f y x) e (REVERSE l)`--),
    GEN_TAC THEN GEN_TAC THEN SNOC_INDUCT_TAC
    THEN ASM_REWRITE_TAC[REVERSE,FOLDR,FOLDL,REVERSE_SNOC,FOLDR_SNOC]
    THEN BETA_TAC THEN ASM_REWRITE_TAC[FOLDL_SNOC]);

val FOLDR_REVERSE = store_thm("FOLDR_REVERSE",
    (--`!(f:'a->'b->'b) e l. 
       FOLDR f e (REVERSE l) = FOLDL (\x y. f y x) e l`--),
    REWRITE_TAC[FOLDR_FOLDL_REVERSE,REVERSE_REVERSE]);

val FOLDL_REVERSE = store_thm("FOLDL_REVERSE",
    (--`!(f:'a->'b->'a) e l. 
       FOLDL f e (REVERSE l) = FOLDR (\x y. f y x) e l`--),
    REWRITE_TAC[FOLDL_FOLDR_REVERSE,REVERSE_REVERSE]);


val FOLDR_MAP = store_thm("FOLDR_MAP",
    (--`!(f:'a->'a->'a) e (g:'b ->'a) l. 
       FOLDR f e (MAP g l) = FOLDR (\x y. f (g x) y) e l`--),
    GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC
    THEN ASM_REWRITE_TAC[FOLDL,MAP,FOLDR] THEN BETA_TAC
    THEN REWRITE_TAC[]);

val FOLDL_MAP = store_thm("FOLDL_MAP",
    (--`!(f:'a->'a->'a) e (g:'b ->'a) l. 
       FOLDL f e (MAP g l) = FOLDL (\x y. f x (g y)) e l`--),
    GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN SNOC_INDUCT_TAC
    THEN ASM_REWRITE_TAC[MAP,FOLDL,FOLDL_SNOC,MAP_SNOC,FOLDR]
    THEN BETA_TAC THEN REWRITE_TAC[]);


val ALL_EL_FOLDR = store_thm("ALL_EL_FOLDR",
    (--`!(P:'a->bool) l. ALL_EL P l = FOLDR (\x l'. P x /\ l') T l`--),
    GEN_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[ALL_EL,FOLDR,MAP]
    THEN BETA_TAC THEN REWRITE_TAC[]);

val ALL_EL_FOLDL = store_thm("ALL_EL_FOLDL",
    (--`!(P:'a->bool) l. ALL_EL P l = FOLDL (\l' x. l' /\ P x) T l`--),
    GEN_TAC THEN SNOC_INDUCT_TAC THENL[
      REWRITE_TAC[ALL_EL,FOLDL,MAP],
      ASM_REWRITE_TAC[ALL_EL_SNOC,FOLDL_SNOC,MAP_SNOC]]
    THEN BETA_TAC THEN REWRITE_TAC[]);

val SOME_EL_FOLDR = store_thm("SOME_EL_FOLDR",
    (--`!P (l:'a list). SOME_EL P l = FOLDR (\x l'. P x \/ l') F l`--),
    GEN_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[SOME_EL,MAP,FOLDR] THEN
    BETA_TAC THEN REWRITE_TAC[]);

val SOME_EL_FOLDL = store_thm("SOME_EL_FOLDL",
    (--`!P (l:'a list). SOME_EL P l = FOLDL (\l' x. l' \/ P x) F l`--),
    GEN_TAC THEN SNOC_INDUCT_TAC THENL[
      REWRITE_TAC[SOME_EL,MAP,FOLDL],
      REWRITE_TAC[SOME_EL_SNOC,MAP_SNOC,FOLDL_SNOC]
      THEN BETA_TAC THEN GEN_TAC
      THEN FIRST_ASSUM SUBST1_TAC THEN MATCH_ACCEPT_TAC DISJ_SYM] );

val ALL_EL_FOLDR_MAP = store_thm("ALL_EL_FOLDR_MAP",
    (--`!(P:'a->bool) l. ALL_EL P l = FOLDR $/\  T (MAP P l)`--),
    REWRITE_TAC[ALL_EL_FOLDR,FOLDR_MAP]);

val ALL_EL_FOLDL_MAP = store_thm("ALL_EL_FOLDL_MAP",
    (--`!(P:'a->bool) l. ALL_EL P l = FOLDL $/\  T (MAP P l)`--),
    REWRITE_TAC[ALL_EL_FOLDL,FOLDL_MAP]);

val SOME_EL_FOLDR_MAP = store_thm("SOME_EL_FOLDR_MAP",
    (--`!(P:'a->bool) l. SOME_EL P l = FOLDR $\/ F (MAP P l)`--),
    REWRITE_TAC[SOME_EL_FOLDR,FOLDR_MAP]);

val SOME_EL_FOLDL_MAP = store_thm("SOME_EL_FOLDL_MAP",
    (--`!(P:'a->bool) l. SOME_EL P l = FOLDL $\/ F (MAP P l)`--),
    REWRITE_TAC[SOME_EL_FOLDL,FOLDL_MAP]);


val FOLDR_FILTER = store_thm("FOLDR_FILTER",
    (--`!(f:'a->'a->'a) e (P:'a -> bool) l. 
       FOLDR f e (FILTER P l) = FOLDR (\x y. P x => f x y  | y) e l`--),
    GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC
    THEN ASM_REWRITE_TAC[FOLDL, FILTER, FOLDR] THEN BETA_TAC
    THEN GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[FOLDR]);

val FOLDL_FILTER = store_thm("FOLDL_FILTER",
    (--`!(f:'a->'a->'a) e (P:'a -> bool) l. 
       FOLDL f e (FILTER P l) = FOLDL (\x y. P y => f x y | x) e l`--),
     GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN SNOC_INDUCT_TAC
     THEN ASM_REWRITE_TAC[FOLDL,FOLDR_SNOC,FOLDL_SNOC,FILTER,FOLDR,FILTER_SNOC]
     THEN BETA_TAC THEN GEN_TAC THEN COND_CASES_TAC
     THEN ASM_REWRITE_TAC[FOLDL_SNOC]);

val ASSOC_FOLDR_FLAT = store_thm("ASSOC_FOLDR_FLAT",
    (--`!(f:'a->'a->'a). ASSOC f ==>
     (! e. LEFT_ID f e ==>
       (!l. FOLDR f e (FLAT l) = FOLDR f e (MAP (FOLDR f e) l)))`--),
    GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN DISCH_TAC
    THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[FLAT,MAP,FOLDR]
    THEN IMP_RES_TAC (GSYM FCOMM_ASSOC)
    THEN IMP_RES_TAC FCOMM_FOLDR_APPEND THEN ASM_REWRITE_TAC[]);

val ASSOC_FOLDL_FLAT = store_thm("ASSOC_FOLDL_FLAT",
    (--`!(f:'a->'a->'a). ASSOC f ==>
     (! e. RIGHT_ID f e ==>
       (!l. FOLDL f e (FLAT l) = FOLDL f e (MAP (FOLDL f e) l)))`--),
    GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN DISCH_TAC THEN SNOC_INDUCT_TAC
    THEN ASM_REWRITE_TAC[FLAT_SNOC,MAP_SNOC,MAP,FLAT,FOLDL_SNOC]
    THEN IMP_RES_TAC (GSYM FCOMM_ASSOC)
    THEN IMP_RES_TAC FCOMM_FOLDL_APPEND THEN ASM_REWRITE_TAC[]);

val MAP_FLAT = store_thm("MAP_FLAT",
    (--`!(f:'a->'b) l. MAP f (FLAT l) = FLAT (MAP  (MAP f) l)`--),
    GEN_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[FLAT,MAP,MAP_APPEND]);

val FILTER_FLAT = store_thm("FILTER_FLAT",
    (--`!(P:'a->bool) l. FILTER P (FLAT l) = FLAT (MAP (FILTER P) l)`--),
    GEN_TAC THEN LIST_INDUCT_TAC THEN
    ASM_REWRITE_TAC[FLAT,MAP,FILTER,FILTER_APPEND]);


val SOME_EL_MAP = store_thm("SOME_EL_MAP",
    (--`!P (f:'a->'b) l. SOME_EL P (MAP f l) = SOME_EL (P o f) l`--),
    GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THENL[
      REWRITE_TAC [SOME_EL,MAP],
      REWRITE_TAC [SOME_EL,MAP] THEN ASM_REWRITE_TAC [o_DEF]
      THEN BETA_TAC THEN REWRITE_TAC[]]);


val SOME_EL_APPEND = store_thm("SOME_EL_APPEND",
    (--`!P (l1:('a)list) l2.
     (SOME_EL P (APPEND l1 l2)) = ((SOME_EL P l1) \/ (SOME_EL P l2))`--),
   GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC [APPEND,SOME_EL]
   THEN ASM_REWRITE_TAC [] THEN REWRITE_TAC [DISJ_ASSOC]);

val SOME_EL_DISJ = store_thm("SOME_EL_DISJ",
    (--`!P Q (l:'a list).
     SOME_EL (\x. P x \/ Q x) l = SOME_EL P l \/ SOME_EL Q l`--),
    GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC
    THEN REWRITE_TAC[SOME_EL] THEN GEN_TAC THEN BETA_TAC
    THEN POP_ASSUM SUBST1_TAC THEN CONV_TAC (AC_CONV (DISJ_ASSOC,DISJ_SYM)));

val IS_EL_APPEND = store_thm("IS_EL_APPEND",
    (--`!(l1:('a)list) l2 x.
     (IS_EL x (APPEND l1 l2)) = ((IS_EL x l1) \/ (IS_EL x l2))`--),
    REWRITE_TAC[IS_EL_DEF,SOME_EL_APPEND]);

val IS_EL_FOLDR = store_thm("IS_EL_FOLDR",
    (--`!(y:'a) l. IS_EL y l = FOLDR (\x l'. (y = x) \/ l') F l`--),
    REWRITE_TAC[IS_EL_DEF, SOME_EL_FOLDR,FOLDR_MAP]
    THEN BETA_TAC THEN REWRITE_TAC[]);

val IS_EL_FOLDL = store_thm("IS_EL_FOLDL",
    (--`!(y:'a) l. IS_EL y l = FOLDL (\l' x. l' \/ (y = x)) F l`--),
    REWRITE_TAC[IS_EL_DEF,SOME_EL_FOLDL,FOLDL_MAP]
    THEN BETA_TAC THEN REWRITE_TAC[]);

val NULL_FOLDR = store_thm("NULL_FOLDR",
    (--`!(l:'a list). NULL l = FOLDR (\x l'. F) T l`--),
    LIST_INDUCT_TAC THEN REWRITE_TAC[NULL_DEF,FOLDR]);


val NULL_FOLDL = store_thm("NULL_FOLDL",
    (--`!(l:'a list). NULL l = FOLDL (\x l'. F) T l`--),
    SNOC_INDUCT_TAC THEN
    REWRITE_TAC[NULL_DEF,FOLDL_SNOC,NULL_EQ_NIL,FOLDL,
                GSYM (prove_constructors_distinct SNOC_Axiom)]);


val MAP_REVERSE = store_thm("MAP_REVERSE",
    (--`!(f:'a -> 'b) l. MAP f (REVERSE l) = REVERSE (MAP f l)`--),
    GEN_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[REVERSE,MAP,MAP_SNOC]);

val FILTER_REVERSE = store_thm("FILTER_REVERSE",
    (--`!(P:'a -> bool) l. FILTER P (REVERSE l) = REVERSE (FILTER P l)`--),
    GEN_TAC THEN LIST_INDUCT_TAC
    THEN ASM_REWRITE_TAC[REVERSE,FILTER,FILTER_SNOC]
    THEN GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[REVERSE]);

val LAST = save_thm("LAST",
    (* (--`!(:'a) l. LAST (SNOC x l) = x`--), *)
    let val lem = prove(
    (--`!x (l:'a list).  (SEG 1 (PRE(LENGTH (SNOC x l))) (SNOC x l)) = [x]`--),
    GEN_TAC THEN PURE_ONCE_REWRITE_TAC[LENGTH_SNOC]
    THEN PURE_ONCE_REWRITE_TAC[PRE]
    THEN CONV_TAC (ONCE_DEPTH_CONV num_CONV)
    THEN LIST_INDUCT_TAC
    THEN PURE_ONCE_REWRITE_TAC[LENGTH] THEN REWRITE_TAC[SNOC,SEG]
    THEN FIRST_ASSUM ACCEPT_TAC)
    in
    GENL[(--`x:'a`--), (--`l:'a list`--)]
        (REWRITE_RULE[lem,HD](SPEC (--`SNOC (x:'a) l`--) LAST_DEF))
    end);

val BUTLAST = save_thm("BUTLAST",
    (* (--`!x l. BUTLAST (SNOC x l) = l`--), *)
    let val lem = prove(
    (--`!x:'a. !l. SEG (PRE(LENGTH (SNOC x l))) 0 (SNOC x l) = l`--),
    GEN_TAC THEN PURE_ONCE_REWRITE_TAC[LENGTH_SNOC]
    THEN PURE_ONCE_REWRITE_TAC[PRE]
    THEN LIST_INDUCT_TAC
    THEN PURE_ONCE_REWRITE_TAC[LENGTH] THEN ASM_REWRITE_TAC[SNOC,SEG])
    in
    GENL[(--`x:'a`--),(--`l:'a list`--)]
        (REWRITE_RULE[lem](SPEC (--`SNOC (x:'a) l`--) BUTLAST_DEF))
    end);


val SEG_LENGTH_ID = store_thm("SEG_LENGTH_ID",
    (--`!l:'a list. SEG (LENGTH l) 0 l = l`--),
    LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[LENGTH,SEG]);

val SEG_SUC_CONS = store_thm("SEG_SUC_CONS",
    (--`!m n l (x:'a). (SEG m (SUC n) (CONS x l) = SEG m n l)`--),
    INDUCT_TAC THEN REWRITE_TAC[SEG]);

val SEG_0_SNOC = store_thm("SEG_0_SNOC",
--`!m l (x:'a). (m <= (LENGTH l)) ==> (SEG m 0 (SNOC x l) = SEG m 0 l)`--,
    INDUCT_TAC THENL[
    	REWRITE_TAC[SEG],
    	LIST_INDUCT_TAC THEN REWRITE_TAC[LENGTH] THENL[
    	    REWRITE_TAC[LESS_OR_EQ,NOT_SUC,NOT_LESS_0],
    	    REWRITE_TAC[SNOC,SEG,LESS_EQ_MONO]
            THEN REPEAT STRIP_TAC THEN RES_TAC THEN ASM_REWRITE_TAC[]]]);

val BUTLASTN_SEG = store_thm("BUTLASTN_SEG",
    (--`!n (l:'a list). (n <= (LENGTH l)) ==>
     (BUTLASTN n l = SEG (LENGTH l - n) 0 l)`--),
    INDUCT_TAC THEN REWRITE_TAC[BUTLASTN,SUB_0,SEG_LENGTH_ID]
    THEN SNOC_INDUCT_TAC
    THEN REWRITE_TAC[LENGTH,LENGTH_SNOC,BUTLASTN] THENL[
    	REWRITE_TAC[LESS_OR_EQ,NOT_LESS_0,NOT_SUC],
    	REWRITE_TAC[LESS_EQ_MONO,SUB_MONO_EQ]
        THEN REPEAT STRIP_TAC THEN RES_THEN SUBST1_TAC
    	THEN MATCH_MP_TAC (GSYM SEG_0_SNOC)
    	THEN MATCH_ACCEPT_TAC SUB_LESS_EQ]);

val LASTN_CONS = store_thm("LASTN_CONS",
    (--`!n (l:'a list). (n <= (LENGTH l)) ==>
     (!x. LASTN n (CONS x l) = LASTN n l)`--),
    INDUCT_TAC THEN REWRITE_TAC[LASTN] THEN SNOC_INDUCT_TAC THENL[
    	REWRITE_TAC[LENGTH,LESS_OR_EQ,NOT_LESS_0,NOT_SUC],
    	REWRITE_TAC[LENGTH_SNOC,(GSYM(CONJUNCT2 SNOC)),LESS_EQ_MONO]
    	THEN REPEAT STRIP_TAC THEN RES_TAC
    	THEN ASM_REWRITE_TAC[LASTN]]);

val LENGTH_LASTN = store_thm("LENGTH_LASTN",
    (--`!n (l:('a)list). (n <= LENGTH l) ==> (LENGTH (LASTN n l) = n)`--),
    INDUCT_TAC THEN REWRITE_TAC[LASTN,LENGTH] THEN SNOC_INDUCT_TAC
    THENL[
    	REWRITE_TAC[LENGTH,LESS_OR_EQ,NOT_LESS_0,NOT_SUC],
    	REWRITE_TAC[LENGTH_SNOC,LASTN,LESS_EQ_MONO]
    	THEN DISCH_TAC THEN RES_THEN SUBST1_TAC THEN REFL_TAC]);

val LASTN_LENGTH_ID = store_thm("LASTN_LENGTH_ID",
    (--`!l:'a list. LASTN (LENGTH l) l = l`--),
    SNOC_INDUCT_TAC THEN REWRITE_TAC[LENGTH,LENGTH_SNOC,LASTN]
    THEN GEN_TAC THEN POP_ASSUM SUBST1_TAC THEN REFL_TAC);

val LASTN_LASTN = store_thm("LASTN_LASTN",
    (--`!l:'a list.!n m. (m <= LENGTH l) ==>
    (n <= m) ==> (LASTN n (LASTN m l) = LASTN n l)`--),
    SNOC_INDUCT_TAC THENL[
    	REWRITE_TAC[LENGTH,LESS_OR_EQ,NOT_LESS_0]
    	THEN REPEAT GEN_TAC THEN DISCH_THEN SUBST1_TAC
    	THEN REWRITE_TAC[NOT_LESS_0,LASTN],
    	GEN_TAC THEN REPEAT INDUCT_TAC
    	THEN REWRITE_TAC[LENGTH_SNOC,LASTN,LESS_EQ_MONO,ZERO_LESS_EQ] THENL[
    	    REWRITE_TAC[LESS_OR_EQ,NOT_LESS_0,NOT_SUC],
    	    REPEAT DISCH_TAC THEN RES_TAC THEN ASM_REWRITE_TAC[]]]);

val NOT_SUC_LESS_EQ_0 = prove((--`!n. ~(SUC n <= 0)`--),
    REWRITE_TAC[LESS_OR_EQ,NOT_LESS_0,NOT_SUC]);

val FIRSTN_LENGTH_ID = store_thm("FIRSTN_LENGTH_ID",
    (--`!l:'a list. FIRSTN (LENGTH l) l = l`--),
    LIST_INDUCT_TAC THEN REWRITE_TAC[LENGTH,FIRSTN]
    THEN GEN_TAC THEN POP_ASSUM SUBST1_TAC THEN REFL_TAC);

val FIRSTN_SNOC = store_thm("FIRSTN_SNOC",
    (--`!n (l:'a list). (n <= (LENGTH l)) ==>
     (!x. FIRSTN n (SNOC x l) = FIRSTN n l)`--),
    INDUCT_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[FIRSTN,LENGTH] THENL[
    	REWRITE_TAC[LESS_OR_EQ,NOT_LESS_0,NOT_SUC],
    	REWRITE_TAC[LESS_EQ_MONO,SNOC,FIRSTN]
    	THEN REPEAT STRIP_TAC THEN RES_TAC THEN ASM_REWRITE_TAC[]]);

val BUTLASTN_LENGTH_NIL = store_thm("BUTLASTN_LENGTH_NIL",
    (--`!l:'a list. BUTLASTN (LENGTH l) l = []`--),
    SNOC_INDUCT_TAC THEN ASM_REWRITE_TAC[LENGTH,LENGTH_SNOC,BUTLASTN]);

val BUTLASTN_SUC_BUTLAST = store_thm("BUTLASTN_SUC_BUTLAST",
    (--`!n (l:('a)list). (n < (LENGTH l)) ==>
     (BUTLASTN (SUC n) l =  BUTLASTN n (BUTLAST l))`--),
    INDUCT_TAC THEN SNOC_INDUCT_TAC
    THEN REWRITE_TAC[LENGTH,NOT_LESS_0,BUTLASTN,BUTLAST]);

val BUTLASTN_BUTLAST = store_thm("BUTLASTN_BUTLAST",
    (--`!n (l:('a)list). (n < (LENGTH l)) ==>
     (BUTLASTN n (BUTLAST l) = BUTLAST (BUTLASTN n l))`--),
    INDUCT_TAC THEN REWRITE_TAC[BUTLASTN] THEN SNOC_INDUCT_TAC
    THEN REWRITE_TAC[LENGTH,LENGTH_SNOC,NOT_LESS_0,
    	LESS_MONO_EQ,BUTLASTN,BUTLAST]
    THEN DISCH_TAC THEN IMP_RES_THEN SUBST1_TAC BUTLASTN_SUC_BUTLAST
    THEN RES_TAC);

val LENGTH_BUTLASTN = store_thm("LENGTH_BUTLASTN",
    (--`!n (l:('a)list). (n <= LENGTH l) ==> 
     (LENGTH (BUTLASTN n l) = LENGTH l - n)`--),
    INDUCT_TAC THEN SNOC_INDUCT_TAC
    THEN REWRITE_TAC[BUTLASTN,SUB_0] THENL[
    	REWRITE_TAC[LENGTH,LESS_OR_EQ,NOT_LESS_0,NOT_SUC],
    	REWRITE_TAC[LENGTH_SNOC,LESS_EQ_MONO,SUB_MONO_EQ]
    	THEN FIRST_ASSUM MATCH_ACCEPT_TAC]);

val ADD_SUC_lem =
   let val l = CONJUNCTS ADD_CLAUSES
   in
    	GEN_ALL (TRANS (el 4 l) (SYM (el 3 l)))
   end ;

val BUTLASTN_BUTLASTN = store_thm("BUTLASTN_BUTLASTN",
    (--`!m n (l:'a list).  ((n + m) <= LENGTH l) ==>
     (BUTLASTN n (BUTLASTN m l) = BUTLASTN (n + m) l)`--),
    REPEAT INDUCT_TAC THEN SNOC_INDUCT_TAC
    THEN REWRITE_TAC[LENGTH,ADD,ADD_0,BUTLASTN] THENL[
    	REWRITE_TAC[LESS_OR_EQ,NOT_LESS_0,NOT_SUC],
    	REWRITE_TAC[LENGTH_SNOC,LESS_EQ_MONO,ADD_SUC_lem]
    	THEN FIRST_ASSUM MATCH_ACCEPT_TAC]);

val APPEND_BUTLASTN_LASTN = store_thm ("APPEND_BUTLASTN_LASTN",
    (--`!n (l:('a)list) . (n <= LENGTH l) ==>
     (APPEND (BUTLASTN n l) (LASTN n l) = l)`--),
    INDUCT_TAC THEN SNOC_INDUCT_TAC
    THEN REWRITE_TAC[BUTLASTN,LASTN,APPEND,APPEND_NIL] THENL[
    	REWRITE_TAC[LENGTH,LESS_OR_EQ,NOT_LESS_0,NOT_SUC],
    	REWRITE_TAC[LENGTH_SNOC,LESS_EQ_MONO,APPEND_SNOC]
    	THEN GEN_TAC THEN DISCH_TAC THEN RES_THEN SUBST1_TAC THEN REFL_TAC]);


val APPEND_FIRSTN_LASTN = store_thm("APPEND_FIRSTN_LASTN",
  (--`!m n (l:'a list). ((m + n) = (LENGTH l)) ==> 
         (APPEND (FIRSTN n l) (LASTN m l) = l)`--),
    let val ADD_EQ_LESS_EQ = prove((--`!m n p. ((n + m) = p) ==> (m <= p)`--),
      REPEAT GEN_TAC THEN DISCH_THEN (SUBST1_TAC o SYM)
      THEN PURE_ONCE_REWRITE_TAC[ADD_SYM]
      THEN MATCH_ACCEPT_TAC LESS_EQ_ADD)
    in
    REPEAT INDUCT_TAC THEN SNOC_INDUCT_TAC
    THEN REWRITE_TAC[LENGTH,LENGTH_SNOC,ADD,ADD_0,FIRSTN,LASTN,
    	APPEND,APPEND_NIL,SUC_NOT,NOT_SUC] THENL[
    	GEN_TAC THEN DISCH_THEN SUBST1_TAC
    	THEN SUBST1_TAC (SYM(SPEC_ALL LENGTH_SNOC))
    	THEN MATCH_ACCEPT_TAC FIRSTN_LENGTH_ID,
    	PURE_ONCE_REWRITE_TAC[INV_SUC_EQ] THEN GEN_TAC
    	THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[LASTN_LENGTH_ID],
    	PURE_ONCE_REWRITE_TAC[INV_SUC_EQ,ADD_SUC_lem,APPEND_SNOC]
    	THEN REPEAT STRIP_TAC THEN IMP_RES_TAC ADD_EQ_LESS_EQ
    	THEN IMP_RES_TAC FIRSTN_SNOC THEN RES_TAC
    	THEN ASM_REWRITE_TAC[]]
    end);

val BUTLASTN_APPEND2 = store_thm ("BUTLASTN_APPEND2",
    (--`!n l1 (l2:'a list). (n <= LENGTH l2) ==>
     (BUTLASTN n (APPEND l1 l2) = APPEND l1 (BUTLASTN n l2))`--),
    INDUCT_TAC THEN GEN_TAC THEN SNOC_INDUCT_TAC
    THEN REWRITE_TAC[LENGTH,BUTLASTN,NOT_SUC_LESS_EQ_0,APPEND_SNOC]
    THEN ASM_REWRITE_TAC[LENGTH_SNOC,LESS_EQ_MONO]);

(*--------------------------------------------------------------------------*)
(*(--`!(l2:'a list) (l1:'a list). BUTLASTN(LENGTH l2)(APPEND l1 l2) = l1`--)*)
(*--------------------------------------------------------------------------*)

val BUTLASTN_LENGTH_APPEND = save_thm("BUTLASTN_LENGTH_APPEND",
    GENL[(--`l2:'a list`--),(--`l1:'a list`--)]
     (REWRITE_RULE[LESS_EQ_REFL,BUTLASTN_LENGTH_NIL,APPEND_NIL]
     (SPECL[(--`LENGTH (l2:'a list)`--),(--`l1:'a list`--),(--`l2:'a list`--)]
           BUTLASTN_APPEND2)));

val LASTN_LENGTH_APPEND = store_thm("LASTN_LENGTH_APPEND",
    (--`!(l2:'a list) l1. LASTN (LENGTH l2) (APPEND l1 l2) = l2`--),
    SNOC_INDUCT_TAC
    THEN REWRITE_TAC[LENGTH,LENGTH_SNOC,APPEND,APPEND_SNOC,LASTN]
    THEN ASM_REWRITE_TAC[BUTLAST,LAST,SNOC_APPEND]);

val BUTLASTN_CONS = store_thm("BUTLASTN_CONS",
    (--`!n l. (n <= (LENGTH l)) ==> 
     (!x:'a. BUTLASTN n(CONS x l) = CONS x(BUTLASTN n l))`--),
    INDUCT_TAC THEN SNOC_INDUCT_TAC
    THEN REWRITE_TAC[LENGTH,NOT_SUC_LESS_EQ_0,BUTLASTN,GSYM(CONJUNCT2 SNOC)]
    THEN ASM_REWRITE_TAC[LENGTH_SNOC,LESS_EQ_MONO]);

(*  |- !l x. BUTLASTN(LENGTH l)(CONS x l) = [x] *)
val BUTLASTN_LENGTH_CONS = save_thm("BUTLASTN_LENGTH_CONS",
    let val thm1 = 
     SPECL [(--`LENGTH (l:'a list)`--),(--`l:'a list`--)] BUTLASTN_CONS
    in
    GEN_ALL(REWRITE_RULE[LESS_EQ_REFL,BUTLASTN_LENGTH_NIL] thm1)
    end);

val LAST_LASTN_LAST = store_thm("LAST_LASTN_LAST",
    (--`!n (l:('a)list). (n <= LENGTH l) ==> (0 < n) ==>
     (LAST(LASTN n l) = LAST l)`--),
    INDUCT_TAC THEN SNOC_INDUCT_TAC
    THEN REWRITE_TAC[LENGTH,NOT_LESS_0,NOT_SUC_LESS_EQ_0]
    THEN REWRITE_TAC[LASTN,LAST]);

val BUTLASTN_LASTN_NIL = store_thm("BUTLASTN_LASTN_NIL",
    (--`!n. !l:'a list. n <= (LENGTH l) ==> (BUTLASTN n (LASTN n l) = [])`--),
    REPEAT STRIP_TAC
    THEN IMP_RES_THEN (fn t => SUBST_OCCS_TAC [([1],SYM t)]) LENGTH_LASTN
    THEN MATCH_ACCEPT_TAC BUTLASTN_LENGTH_NIL);

val LASTN_BUTLASTN = store_thm("LASTN_BUTLASTN",
    (--`!n m. !l:'a list. ((n + m) <= LENGTH l) ==>
     (LASTN n (BUTLASTN m l) = BUTLASTN m (LASTN (n + m) l))`--),
    let val ADD_SUC_SYM = GEN_ALL (SYM (TRANS 
    	(SPEC_ALL(CONJUNCT2 ADD)) (SPEC_ALL ADD_SUC)))
    in
    REPEAT INDUCT_TAC THEN SNOC_INDUCT_TAC
    THEN REWRITE_TAC[LENGTH,NOT_SUC_LESS_EQ_0,ADD,ADD_0,LASTN,BUTLASTN]
    THEN REWRITE_TAC[LENGTH_SNOC,LESS_EQ_MONO] THENL[
    	DISCH_TAC THEN CONV_TAC SYM_CONV THEN IMP_RES_TAC BUTLASTN_LASTN_NIL,
    	 PURE_ONCE_REWRITE_TAC[ADD_SUC_SYM] THEN DISCH_TAC THEN RES_TAC]
    end);

val BUTLASTN_LASTN = store_thm("BUTLASTN_LASTN",
    (--`!m n. !l:'a list. ((m <= n) /\ (n <= LENGTH l)) ==>
     (BUTLASTN m (LASTN n l) = LASTN (n - m) (BUTLASTN m l))`--),
    REPEAT INDUCT_TAC THEN SNOC_INDUCT_TAC
    THEN REWRITE_TAC[LENGTH,NOT_LESS_0,NOT_SUC_LESS_EQ_0,SUB_0,BUTLASTN,LASTN]
    THEN ASM_REWRITE_TAC[LENGTH_SNOC,LESS_EQ_MONO,SUB_MONO_EQ]);

val LASTN_1 = store_thm("LASTN_1",
    (--`!l:'a list. ~(l = []) ==> (LASTN 1 l = [LAST l])`--),
    SNOC_INDUCT_TAC THEN REWRITE_TAC[]
    THEN REPEAT STRIP_TAC THEN CONV_TAC (ONCE_DEPTH_CONV num_CONV)
    THEN REWRITE_TAC[LASTN,APPEND_NIL,SNOC,LAST]);

val BUTLASTN_1 = store_thm("BUTLASTN_1",
    (--`!l:'a list. ~(l = []) ==> (BUTLASTN 1 l = BUTLAST l)`--),
    SNOC_INDUCT_TAC THEN REWRITE_TAC[]
    THEN REPEAT STRIP_TAC THEN CONV_TAC (ONCE_DEPTH_CONV num_CONV)
    THEN REWRITE_TAC[BUTLAST,BUTLASTN]);

val BUTLASTN_APPEND1 = store_thm("BUTLASTN_APPEND1",
--`!l2 n. (LENGTH l2 <= n) ==>
   !l1:'a list. BUTLASTN n (APPEND l1 l2) = BUTLASTN (n - (LENGTH l2)) l1`--,
    SNOC_INDUCT_TAC
    THEN REWRITE_TAC[LENGTH,LENGTH_SNOC,APPEND,APPEND_SNOC,APPEND_NIL,SUB_0]
    THEN GEN_TAC THEN INDUCT_TAC
    THEN REWRITE_TAC[NOT_SUC_LESS_EQ_0,LESS_EQ_MONO,BUTLASTN,SUB_MONO_EQ]
    THEN FIRST_ASSUM MATCH_ACCEPT_TAC);

val LASTN_APPEND2 = store_thm("LASTN_APPEND2",
    (--`!n (l2:'a list). n <= (LENGTH l2) ==>
     (!l1. LASTN n (APPEND l1 l2) = LASTN n l2)`--),
    INDUCT_TAC THEN SNOC_INDUCT_TAC
    THEN REWRITE_TAC[LENGTH,LENGTH_SNOC,LASTN,NOT_SUC_LESS_EQ_0]
    THEN REWRITE_TAC[LESS_EQ_MONO,LASTN,APPEND_SNOC]
    THEN REPEAT STRIP_TAC THEN RES_TAC THEN ASM_REWRITE_TAC[]);

val LASTN_APPEND1 = store_thm("LASTN_APPEND1",
--`!(l2:'a list) n. (LENGTH l2) <= n ==>
   !l1. LASTN n (APPEND l1 l2) = APPEND (LASTN (n - (LENGTH l2)) l1) l2`--,
    SNOC_INDUCT_TAC THEN REWRITE_TAC[LENGTH,LENGTH_SNOC,
    	APPEND,APPEND_SNOC,APPEND_NIL,LASTN,SUB_0]
    THEN GEN_TAC THEN INDUCT_TAC
    THEN REWRITE_TAC[NOT_SUC_LESS_EQ_0,LASTN,LESS_EQ_MONO,SUB_MONO_EQ]
    THEN DISCH_TAC THEN RES_TAC THEN ASM_REWRITE_TAC[]);

val LASTN_MAP = store_thm("LASTN_MAP",
    (--`!n l. (n <= LENGTH l) ==>
     (!(f:'a->'b). LASTN n (MAP f l) = MAP f (LASTN n l))`--),
    INDUCT_TAC THEN SNOC_INDUCT_TAC
    THEN REWRITE_TAC[LENGTH,LASTN,MAP,NOT_SUC_LESS_EQ_0]
    THEN REWRITE_TAC[LENGTH_SNOC,LASTN,MAP_SNOC,LESS_EQ_MONO]
    THEN REPEAT STRIP_TAC THEN RES_TAC THEN ASM_REWRITE_TAC[]);

val BUTLASTN_MAP = store_thm("BUTLASTN_MAP",
    (--`!n l. (n <= LENGTH l) ==>
     (!(f:'a->'b). BUTLASTN n (MAP f l) = MAP f (BUTLASTN n l))`--),
    INDUCT_TAC THEN SNOC_INDUCT_TAC
    THEN REWRITE_TAC[LENGTH,BUTLASTN,MAP,NOT_SUC_LESS_EQ_0]
    THEN REWRITE_TAC[LENGTH_SNOC,BUTLASTN,MAP_SNOC,LESS_EQ_MONO]
    THEN REPEAT STRIP_TAC THEN RES_TAC THEN ASM_REWRITE_TAC[]);

val ALL_EL_LASTN = store_thm("ALL_EL_LASTN",
    (--`!P (l:'a list). ALL_EL P l ==>
     (!m. m <= (LENGTH l) ==> ALL_EL P (LASTN m l))`--),
    GEN_TAC THEN SNOC_INDUCT_TAC THEN REWRITE_TAC[ALL_EL,LENGTH]
    THEN GEN_TAC THENL[
    	REWRITE_TAC[LESS_OR_EQ,NOT_LESS_0]
    	THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[ALL_EL,LASTN],
    	REWRITE_TAC[ALL_EL_SNOC,LENGTH_SNOC] THEN STRIP_TAC
    	THEN INDUCT_TAC THENL[
    	    REWRITE_TAC[ALL_EL,LASTN],
    	    REWRITE_TAC[ALL_EL_SNOC,LASTN,LESS_EQ_MONO]
    	    THEN DISCH_TAC THEN RES_TAC THEN ASM_REWRITE_TAC[]]]);

val ALL_EL_BUTLASTN = store_thm("ALL_EL_BUTLASTN",
    (--`!P (l:'a list). ALL_EL P l ==>
     (!m. m <= (LENGTH l) ==> ALL_EL P (BUTLASTN m l))`--),
    GEN_TAC THEN SNOC_INDUCT_TAC THEN REWRITE_TAC[ALL_EL,LENGTH]
    THEN GEN_TAC THENL[
    	REWRITE_TAC[LESS_OR_EQ,NOT_LESS_0]
    	THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[ALL_EL,BUTLASTN],
    	REWRITE_TAC[ALL_EL_SNOC,LENGTH_SNOC] THEN STRIP_TAC
    	THEN INDUCT_TAC THENL[
    	    DISCH_TAC THEN ASM_REWRITE_TAC[ALL_EL_SNOC,BUTLASTN],
    	    REWRITE_TAC[ALL_EL_SNOC,BUTLASTN,LESS_EQ_MONO]
    	    THEN DISCH_TAC THEN RES_TAC THEN ASM_REWRITE_TAC[]]]);

val LENGTH_FIRSTN = store_thm ("LENGTH_FIRSTN",
    (--`!n (l:('a)list). (n <= LENGTH l) ==> (LENGTH (FIRSTN n l) = n)`--),
    INDUCT_TAC THEN LIST_INDUCT_TAC
    THEN REWRITE_TAC[LENGTH,FIRSTN,NOT_SUC_LESS_EQ_0,LESS_EQ_MONO]
    THEN DISCH_TAC THEN RES_THEN SUBST1_TAC THEN REFL_TAC);

val FIRSTN_FIRSTN = store_thm("FIRSTN_FIRSTN",
    (--`!m (l:'a list). (m <= LENGTH l) ==>
    !n. (n <= m) ==> (FIRSTN n (FIRSTN m l) = FIRSTN n l)`--),
    INDUCT_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[LENGTH,FIRSTN] THENL[
    	GEN_TAC THEN DISCH_TAC THEN INDUCT_TAC
    	THEN REWRITE_TAC[NOT_SUC_LESS_EQ_0,FIRSTN],
    	REWRITE_TAC[NOT_SUC_LESS_EQ_0],
    	GEN_TAC THEN REWRITE_TAC[LESS_EQ_MONO] THEN DISCH_TAC
    	THEN INDUCT_TAC THEN REWRITE_TAC[FIRSTN]
    	THEN REWRITE_TAC[LESS_EQ_MONO] THEN DISCH_TAC THEN RES_TAC
    	THEN ASM_REWRITE_TAC[]]);

val LENGTH_BUTFIRSTN = store_thm("LENGTH_BUTFIRSTN",
    (--`!n (l:'a list). (n <= (LENGTH l)) ==>
     (LENGTH (BUTFIRSTN n l) = LENGTH l - n)`--),
    INDUCT_TAC THEN LIST_INDUCT_TAC
    THEN REWRITE_TAC[LENGTH,BUTFIRSTN,SUB_0,NOT_SUC_LESS_EQ_0]
    THEN REWRITE_TAC[LESS_EQ_MONO,SUB_MONO_EQ]
    THEN FIRST_ASSUM MATCH_ACCEPT_TAC);

val BUTFIRSTN_LENGTH_NIL = store_thm("BUTFIRSTN_LENGTH_NIL",
    (--`!l:'a list. BUTFIRSTN (LENGTH l) l = []`--),
    LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[LENGTH,BUTFIRSTN]);

val BUTFIRSTN_APPEND1 = store_thm("BUTFIRSTN_APPEND1",
    (--`!n (l1:'a list). (n <= LENGTH l1) ==>
     !l2. BUTFIRSTN n (APPEND l1 l2) = APPEND (BUTFIRSTN n l1) l2`--),
    INDUCT_TAC THEN LIST_INDUCT_TAC
    THEN REWRITE_TAC[LENGTH,BUTFIRSTN,NOT_SUC_LESS_EQ_0,LESS_EQ_MONO]
    THEN GEN_TAC THEN ASM_REWRITE_TAC[APPEND,BUTFIRSTN]);

val BUTFIRSTN_APPEND2 = store_thm("BUTFIRSTN_APPEND2",
    (--`!(l1:'a list) n. ((LENGTH l1) <= n) ==>
     !l2. BUTFIRSTN n (APPEND l1 l2) = BUTFIRSTN (n - (LENGTH l1)) l2`--),
    LIST_INDUCT_TAC THEN REWRITE_TAC[LENGTH,BUTFIRSTN,APPEND,SUB_0]
    THEN GEN_TAC THEN INDUCT_TAC THEN ASM_REWRITE_TAC
    	[NOT_SUC_LESS_EQ_0,LESS_EQ_MONO,BUTFIRSTN,SUB_MONO_EQ]);

val BUTFIRSTN_BUTFIRSTN = store_thm("BUTFIRSTN_BUTFIRSTN",
    (--`!n m (l:'a list). ((n + m) <= LENGTH l) ==>
     (BUTFIRSTN n(BUTFIRSTN m l) = BUTFIRSTN (n + m) l)`--),
    REPEAT INDUCT_TAC THEN LIST_INDUCT_TAC
    THEN REWRITE_TAC[LENGTH,BUTFIRSTN,NOT_SUC_LESS_EQ_0,NOT_LESS_0,ADD,ADD_0]
    THEN REWRITE_TAC[ADD_SUC_lem,LESS_EQ_MONO]
    THEN FIRST_ASSUM MATCH_ACCEPT_TAC);

val APPEND_FIRSTN_BUTFIRSTN = store_thm("APPEND_FIRSTN_BUTFIRSTN",
    (--`!n (l:'a list). (n <= LENGTH l) ==>
     (APPEND (FIRSTN n l) (BUTFIRSTN n l) = l)`--),
    INDUCT_TAC THEN LIST_INDUCT_TAC
    THEN REWRITE_TAC[LENGTH,FIRSTN,BUTFIRSTN,APPEND,NOT_SUC_LESS_EQ_0]
    THEN PURE_ONCE_REWRITE_TAC[LESS_EQ_MONO] THEN GEN_TAC
    THEN DISCH_TAC THEN RES_TAC THEN ASM_REWRITE_TAC[]);

val LASTN_SEG = store_thm("LASTN_SEG",
    (--`!n (l:'a list). (n <= (LENGTH l)) ==>
                          (LASTN n l = SEG n (LENGTH l - n) l)`--),
    let val SUB_SUC =
       prove((--`!k m. (m < k) ==> (k - m = SUC (k - SUC m))`--),
      REPEAT GEN_TAC THEN
      SUBST_TAC[SYM(SPECL[(--`k:num`--),(--`m:num`--)]SUB_MONO_EQ)]
      THEN DISCH_THEN (fn thm =>  
               let val thm' = MATCH_MP  LESS_SUC_NOT thm
               in
               ACCEPT_TAC (REWRITE_RULE [thm'] 
                      (SPECL [(--`k:num`--),(--`SUC m`--)] (CONJUNCT2 SUB)))
               end))
    in
    INDUCT_TAC THEN REWRITE_TAC[LASTN,SUB_0,SEG] THEN LIST_INDUCT_TAC
    THEN REWRITE_TAC[LENGTH,LASTN,NOT_SUC_LESS_EQ_0]
    THEN REWRITE_TAC[LESS_EQ_MONO,SUB_MONO_EQ]
    THEN GEN_TAC THEN DISCH_TAC THEN IMP_RES_TAC LESS_OR_EQ THENL[
    	IMP_RES_THEN SUBST1_TAC SUB_SUC
    	THEN PURE_ONCE_REWRITE_TAC[SEG] THEN IMP_RES_TAC LESS_EQ
    	THEN RES_THEN (SUBST1_TAC o SYM) THEN MATCH_MP_TAC LASTN_CONS
    	THEN FIRST_ASSUM ACCEPT_TAC,
    	FIRST_ASSUM SUBST1_TAC THEN REWRITE_TAC[SUB_EQUAL_0]
    	THEN SUBST1_TAC(SYM(SPECL[(--`x:'a`--),(--`l:'a list`--)]
                                 (CONJUNCT2 LENGTH))) 
(* **list_Axiom** variable dependancy *)
(*    	THEN SUBST1_TAC(SYM(SPECL[(--`h:'a`--),(--`l:'a list`--)]
                                 (CONJUNCT2 LENGTH))) *)
    	THEN REWRITE_TAC[SEG_LENGTH_ID,LASTN_LENGTH_ID]]
    end);

val FIRSTN_SEG = store_thm("FIRSTN_SEG",
    (--`!n (l:'a list). (n <= (LENGTH l)) ==> (FIRSTN n l = SEG n 0 l)`--),
    INDUCT_TAC THEN LIST_INDUCT_TAC
    THEN REWRITE_TAC[LENGTH,FIRSTN,SEG,NOT_SUC_LESS_EQ_0,LESS_EQ_MONO]
    THEN REPEAT STRIP_TAC THEN RES_TAC THEN ASM_REWRITE_TAC[]);

val BUTFIRSTN_SEG = store_thm("BUTFIRSTN_SEG",
    (--`!n (l:'a list). (n <= (LENGTH l)) ==>
     (BUTFIRSTN n l = SEG (LENGTH l - n) n l)`--),
    INDUCT_TAC THEN LIST_INDUCT_TAC
    THEN REWRITE_TAC[LENGTH,BUTFIRSTN,SEG,NOT_SUC_LESS_EQ_0,
    	LESS_EQ_MONO,SUB_0,SEG_LENGTH_ID]
    THEN REPEAT STRIP_TAC THEN RES_TAC
    THEN ASM_REWRITE_TAC[SUB_MONO_EQ,SEG_SUC_CONS]);

val APPEND_BUTLAST_LAST  = store_thm("APPEND_BUTLAST_LAST",
    (--`!l:'a list. ~(l = []) ==> (APPEND (BUTLAST l) [(LAST l)] = l)`--),
    SNOC_INDUCT_TAC THEN REWRITE_TAC[NOT_SNOC_NIL,BUTLAST,LAST,SNOC_APPEND]);

val BUTFIRSTN_SNOC = store_thm("BUTFIRSTN_SNOC",
    (--`!n (l:'a list). (n <= LENGTH l) ==>
     (!x. BUTFIRSTN n (SNOC x l) = SNOC x (BUTFIRSTN n l))`--),
    INDUCT_TAC THEN LIST_INDUCT_TAC
    THEN REWRITE_TAC[LENGTH,BUTFIRSTN,SNOC,NOT_SUC_LESS_EQ_0,LESS_EQ_MONO]
    THEN FIRST_ASSUM MATCH_ACCEPT_TAC);

val APPEND_BUTLASTN_BUTFIRSTN = store_thm("APPEND_BUTLASTN_BUTFIRSTN",
    (--`!m n (l:'a list). ((m + n) = (LENGTH l)) ==>
     (APPEND (BUTLASTN m l) (BUTFIRSTN n l) = l)`--),
    let val ADD_EQ_LESS_EQ = 
     prove((--`!m n p. ((m+n)=p) ==> (m<=p)`--),
      REPEAT STRIP_TAC THEN POP_ASSUM(ASSUME_TAC o SYM) THEN
      ASM_REWRITE_TAC[LESS_EQ_ADD])
    in
    REPEAT INDUCT_TAC THEN LIST_INDUCT_TAC
    THEN REWRITE_TAC[LENGTH,APPEND,ADD,ADD_0,NOT_SUC,SUC_NOT,SNOC,
    	NOT_SUC_LESS_EQ_0,LESS_EQ_MONO,INV_SUC_EQ] THENL[
    	REWRITE_TAC[BUTLASTN,BUTFIRSTN,APPEND],
    	GEN_TAC THEN DISCH_THEN SUBST1_TAC
    	THEN SUBST1_TAC (SYM(SPECL[(--`x:'a`--),(--`l:'a list`--)]
                                  (CONJUNCT2 LENGTH)))
(* **list_Axiom** variable dependancy *)
(*    	THEN SUBST1_TAC (SYM(SPECL[(--`h:'a`--),(--`l:'a list`--)]
                                  (CONJUNCT2 LENGTH)))    *)
    	THEN REWRITE_TAC[BUTFIRSTN_LENGTH_NIL,BUTLASTN,APPEND_NIL],
    	GEN_TAC THEN DISCH_THEN SUBST1_TAC
    	THEN SUBST1_TAC (SYM(SPECL[(--`x:'a`--),(--`l:'a list`--)]
                                  (CONJUNCT2 LENGTH)))
(* **list_Axiom** variable dependancy *)
(*    	THEN SUBST1_TAC (SYM(SPECL[(--`h:'a`--),(--`l:'a list`--)]
                                  (CONJUNCT2 LENGTH))) *)
    	THEN REWRITE_TAC[BUTLASTN_LENGTH_NIL,BUTFIRSTN,APPEND],
    	GEN_TAC THEN DISCH_TAC THEN PURE_ONCE_REWRITE_TAC[BUTFIRSTN]
    	THEN RULE_ASSUM_TAC (REWRITE_RULE[ADD_SUC_lem])
    	THEN IMP_RES_TAC ADD_EQ_LESS_EQ THEN IMP_RES_TAC BUTLASTN_CONS
    	THEN ASM_REWRITE_TAC[APPEND,CONS_11] THEN RES_TAC]
    end);

val SEG_SEG = store_thm("SEG_SEG",
    (--`!n1 m1 n2 m2 (l:'a list).
     (((n1 + m1) <= (LENGTH l)) /\ ((n2 + m2) <= n1)) ==>
     (SEG n2 m2 (SEG n1 m1 l) = SEG n2 (m1 + m2) l)`--),
    REPEAT INDUCT_TAC THEN LIST_INDUCT_TAC 
    THEN REWRITE_TAC[LENGTH,SEG,NOT_LESS_0,NOT_SUC_LESS_EQ_0,ADD,ADD_0]
    THENL[
    	GEN_TAC THEN REWRITE_TAC[LESS_EQ_MONO,CONS_11]
    	THEN STRIP_TAC THEN SUBST_OCCS_TAC[([3],SYM(SPEC(--`0`--)ADD_0))]
    	THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[ADD_0],

    	REWRITE_TAC[LESS_EQ_MONO,ADD_SUC_lem] THEN STRIP_TAC
    	THEN SUBST_OCCS_TAC[([2],SYM(SPEC(--`m2:num`--)(CONJUNCT1 ADD)))]
    	THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[ADD_0],

    	REWRITE_TAC[LESS_EQ_MONO,ADD_SUC_lem] THEN STRIP_TAC
    	THEN SUBST_OCCS_TAC[([2],SYM(SPEC(--`m1:num`--)ADD_0))]
    	THEN FIRST_ASSUM MATCH_MP_TAC
        THEN ASM_REWRITE_TAC[LESS_EQ_MONO,ADD_0],

    	PURE_ONCE_REWRITE_TAC[LESS_EQ_MONO] THEN STRIP_TAC
    	THEN FIRST_ASSUM MATCH_MP_TAC THEN CONJ_TAC THENL[
    	    PURE_ONCE_REWRITE_TAC[GSYM ADD_SUC_lem]
    	    THEN FIRST_ASSUM ACCEPT_TAC,
    	    ASM_REWRITE_TAC[ADD,LESS_EQ_MONO]]]);

val SEG_APPEND1 = store_thm("SEG_APPEND1",
    (--`!n m (l1:'a list). ((n + m) <= LENGTH l1) ==>
     (!l2. SEG n m (APPEND l1 l2) = SEG n m l1)`--),
    REPEAT INDUCT_TAC THEN LIST_INDUCT_TAC 
    THEN REWRITE_TAC[LENGTH,SEG,NOT_LESS_0,NOT_SUC_LESS_EQ_0,ADD,ADD_0]
    THEN GEN_TAC THEN REWRITE_TAC[LESS_EQ_MONO,APPEND,SEG,CONS_11] THENL[
    	DISCH_TAC THEN FIRST_ASSUM MATCH_MP_TAC
    	THEN ASM_REWRITE_TAC[ADD_0],
    	PURE_ONCE_REWRITE_TAC[ADD_SUC_lem]
    	THEN FIRST_ASSUM MATCH_ACCEPT_TAC]);

val SEG_APPEND2 = store_thm("SEG_APPEND2",
    (--`!l1:'a list. !m n l2.
     (LENGTH l1 <= m) /\ (n <= LENGTH l2) ==>
     (SEG n m (APPEND l1 l2) = SEG n (m - (LENGTH l1)) l2)`--),
    LIST_INDUCT_TAC THEN REPEAT (FILTER_GEN_TAC (--`m:num`--))
    THEN REPEAT INDUCT_TAC THEN LIST_INDUCT_TAC
    THEN REWRITE_TAC[LENGTH,SEG,NOT_LESS_0,NOT_SUC_LESS_EQ_0,ADD,ADD_0]
    THEN REPEAT GEN_TAC THEN REWRITE_TAC[SUB_0,APPEND,SEG]
    THEN REWRITE_TAC[LESS_EQ_MONO,SUB_MONO_EQ] THEN STRIP_TAC
    THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[LENGTH,LESS_EQ_MONO]);

val SEG_FIRSTN_BUTFIRSTN = store_thm("SEG_FIRSTN_BUTFISTN",
    (--`!n m (l:'a list). ((n + m) <= (LENGTH l)) ==>
     (SEG n m l = FIRSTN n (BUTFIRSTN m l))`--),
    REPEAT INDUCT_TAC THEN LIST_INDUCT_TAC
    THEN REWRITE_TAC[LENGTH,NOT_SUC_LESS_EQ_0,ADD,ADD_0,
    	SEG,FIRSTN,BUTFIRSTN,LESS_EQ_MONO,CONS_11] THENL[
    	MATCH_ACCEPT_TAC (GSYM FIRSTN_SEG),
    	PURE_ONCE_REWRITE_TAC[ADD_SUC_lem]
    	THEN FIRST_ASSUM MATCH_ACCEPT_TAC]);

val SEG_APPEND = store_thm("SEG_APPEND",
    (--`!m (l1:'a list) n l2. (m < LENGTH l1) /\ ((LENGTH l1) <= (n + m)) /\
      ((n + m) <= ((LENGTH l1) + (LENGTH l2))) ==>
      (SEG n m (APPEND l1 l2) =
    	APPEND (SEG ((LENGTH l1) - m) m l1) (SEG ((n + m)-(LENGTH l1)) 0 l2))`--),
    INDUCT_TAC THEN LIST_INDUCT_TAC THEN REPEAT (FILTER_GEN_TAC (--`n:num`--))
    THEN INDUCT_TAC THEN LIST_INDUCT_TAC THEN REPEAT GEN_TAC
    THEN REWRITE_TAC[LENGTH,SEG,NOT_LESS_0,NOT_SUC_LESS_EQ_0,ADD,ADD_0,SUB_0]
    THEN REWRITE_TAC
    	[LESS_EQ_MONO,SUB_0,SUB_MONO_EQ,APPEND,SEG,NOT_SUC_LESS_EQ_0,CONS_11]
    THEN RULE_ASSUM_TAC (REWRITE_RULE[ADD_0,SUB_0])
    THENL[
    	DISCH_THEN (CONJUNCTS_THEN ASSUME_TAC)
    	THEN POP_ASSUM (SUBST1_TAC o (MATCH_MP LESS_EQUAL_ANTISYM))
    	THEN REWRITE_TAC[SEG,APPEND_NIL,SUB_EQUAL_0],
    	STRIP_TAC THEN DISJ_CASES_TAC (SPEC (--`LENGTH (l1:'a list)`--)LESS_0_CASES)
    	THENL[
    	    POP_ASSUM (ASSUME_TAC o SYM) THEN IMP_RES_TAC LENGTH_NIL
    	    THEN ASM_REWRITE_TAC[APPEND,SEG,SUB_0],
    	    FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[LENGTH]],
    	DISCH_THEN (CONJUNCTS_THEN ASSUME_TAC)
    	THEN POP_ASSUM (SUBST1_TAC o (MATCH_MP LESS_EQUAL_ANTISYM))
    	THEN REWRITE_TAC[SEG,APPEND_NIL,SUB_EQUAL_0],
    	REWRITE_TAC[LESS_MONO_EQ,GSYM NOT_LESS] THEN STRIP_TAC THEN RES_TAC,
    	DISCH_THEN (CONJUNCTS_THEN ASSUME_TAC)
    	THEN POP_ASSUM (SUBST1_TAC o (MATCH_MP LESS_EQUAL_ANTISYM))
    	THEN REWRITE_TAC[SEG,APPEND_NIL,SUB_EQUAL_0]
    	THEN REWRITE_TAC[ADD_SUC_lem,ADD_SUB,SEG],
    	REWRITE_TAC[LESS_MONO_EQ,SEG_SUC_CONS] THEN STRIP_TAC
    	THEN PURE_ONCE_REWRITE_TAC[ADD_SUC_lem]
    	THEN FIRST_ASSUM MATCH_MP_TAC
    	THEN ASM_REWRITE_TAC[GSYM ADD_SUC_lem,LENGTH]]);


val SEG_LENGTH_SNOC = store_thm("SEG_LENGTH_SNOC",
    (--`!(l:'a list) x. SEG 1 (LENGTH l) (SNOC x l) = [x]`--),
    CONV_TAC (ONCE_DEPTH_CONV num_CONV) THEN LIST_INDUCT_TAC
    THEN ASM_REWRITE_TAC[LENGTH,SNOC,SEG]);

val SEG_SNOC = store_thm("SEG_SNOC",
    (--`!n m (l:'a list). ((n + m) <= LENGTH l) ==>
     !x. SEG n m (SNOC x l) = SEG n m l`--),
    REPEAT INDUCT_TAC THEN LIST_INDUCT_TAC
    THEN REWRITE_TAC[LENGTH,NOT_SUC_LESS_EQ_0,ADD,ADD_0,SNOC,SEG] THENL[
    	REWRITE_TAC[CONS_11,LESS_EQ_MONO] THEN REPEAT STRIP_TAC
    	THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[ADD_0],
    	REWRITE_TAC[LESS_EQ_MONO,ADD_SUC_lem] THEN DISCH_TAC
    	THEN FIRST_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC]);

val ELL_SEG = store_thm("ELL_SEG",
    (--`!n (l:'a list). (n < LENGTH l) ==>
     (ELL n l = HD(SEG 1 (PRE(LENGTH l - n)) l))`--),
    let val SUC_PRE = prove((--`!n . (0 < n) ==> ((SUC (PRE n)) = n)`--),
      REPEAT STRIP_TAC THEN  (ACCEPT_TAC (REWRITE_RULE[]
          (MATCH_MP (SPECL[(--`PRE n`--),(--`n:num`--)] PRE_SUC_EQ)
                 (ASSUME (--`0 < n`--)) ))))
    in
    INDUCT_TAC THEN SNOC_INDUCT_TAC
    THEN REWRITE_TAC[LENGTH,LENGTH_SNOC,NOT_LESS_0] THENL[
    	REWRITE_TAC[PRE,SUB_0,ELL,LAST,SEG_LENGTH_SNOC,HD],
    	REWRITE_TAC[LESS_MONO_EQ,ELL,BUTLAST,SUB_MONO_EQ]
    	THEN REPEAT STRIP_TAC THEN RES_THEN SUBST1_TAC
    	THEN CONV_TAC SYM_CONV THEN AP_TERM_TAC THEN MATCH_MP_TAC SEG_SNOC
    	THEN PURE_ONCE_REWRITE_TAC[ADD_SYM]
        THEN PURE_ONCE_REWRITE_TAC[GSYM ADD1]
    	THEN IMP_RES_TAC SUB_LESS_0 THEN IMP_RES_THEN SUBST1_TAC SUC_PRE
    	THEN MATCH_ACCEPT_TAC SUB_LESS_EQ]
    end);

val REWRITE1_TAC = fn t => REWRITE_TAC[t];

val SNOC_FOLDR = store_thm ("SNOC_FOLDR",
    (--`!(x:'a) l. SNOC x l = FOLDR CONS [x] l `--),
    GEN_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[FOLDR,SNOC]);

val IS_EL_FOLDR_MAP = store_thm("IS_EL_FOLDR_MAP",
    (--`!(x:'a) l. IS_EL x l = FOLDR $\/ F (MAP ($= x) l)`--),
    REWRITE_TAC[IS_EL_FOLDR,FOLDR_MAP]);

val IS_EL_FOLDL_MAP = store_thm("IS_EL_FOLDL_MAP",
    (--`!(x:'a) l. IS_EL x l = FOLDL $\/ F (MAP ($= x) l)`--),
    REWRITE_TAC[IS_EL_FOLDL,FOLDL_MAP]);

val FILTER_FILTER = store_thm("FILTER_FILTER",
    (--`!P Q (l:'a list). FILTER P (FILTER Q l) = FILTER (\x. P x /\ Q x) l`--),
    GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[FILTER]
    THEN BETA_TAC THEN GEN_TAC THEN COND_CASES_TAC
    THEN ASM_REWRITE_TAC[FILTER]);

val FCOMM_FOLDR_FLAT = store_thm("FCOMM_FOLDR_FLAT",
    (--`!(g:'a->'a->'a) (f:'b->'a->'a). FCOMM g f ==>
     (! e. LEFT_ID g e ==>
       (!l. FOLDR f e (FLAT l) = FOLDR g e (MAP (FOLDR f e) l)))`--),
    GEN_TAC THEN GEN_TAC THEN DISCH_TAC THEN GEN_TAC
    THEN DISCH_TAC THEN LIST_INDUCT_TAC
    THEN ASM_REWRITE_TAC[FLAT,MAP,FOLDR]
    THEN IMP_RES_TAC FCOMM_FOLDR_APPEND THEN ASM_REWRITE_TAC[]);

val FCOMM_FOLDL_FLAT = store_thm("FCOMM_FOLDL_FLAT",
    (--`!(f:'a->'b->'a) (g:'a->'a->'a). FCOMM f g ==>
     (! e. RIGHT_ID g e ==>
       (!l. FOLDL f e (FLAT l) = FOLDL g e (MAP (FOLDL f e) l)))`--),
    GEN_TAC THEN GEN_TAC THEN DISCH_TAC THEN GEN_TAC
    THEN DISCH_TAC THEN SNOC_INDUCT_TAC 
    THEN ASM_REWRITE_TAC[FLAT_SNOC,MAP_SNOC,MAP,FLAT,FOLDL_SNOC,FOLDL]
    THEN IMP_RES_TAC FCOMM_FOLDL_APPEND THEN ASM_REWRITE_TAC[]);

val FOLDR1 = prove(
    (--`!(f:'a->'a->'a).
      (!a b c. f a (f b c) = f b (f a c)) ==>
       (!e l. (FOLDR f (f x e) l = f x (FOLDR f e l)))`--),
    GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC
    THEN REWRITE_TAC[REVERSE, FOLDR] THEN ONCE_REWRITE_TAC
    [ASSUME (--`!a b c. (f:'a->'a->'a) a (f b c) = f b (f a c)`--)]
    THEN REWRITE_TAC[ASSUME(--`FOLDR (f:'a->'a->'a)(f x e) l = f x (FOLDR f e l)`--)]);

val FOLDL1 = prove(
    (--`!(f:'a->'a->'a).
      (!a b c. f (f a b) c = f (f a c) b) ==>
       (!e l. (FOLDL f (f e x) l = f (FOLDL f e l) x))`--),
    GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN SNOC_INDUCT_TAC
    THEN REWRITE_TAC[REVERSE, FOLDL, FOLDL_SNOC]
    THEN ONCE_REWRITE_TAC
    [ASSUME (--`!a b c. (f:'a->'a->'a) (f a b) c = f (f a c) b`--)]
    THEN REWRITE_TAC[ASSUME(--`FOLDL(f:'a->'a->'a)(f e x) l = f (FOLDL f e l) x`--)]);

val FOLDR_REVERSE2 = prove(
    (--`!(f:'a->'a->'a).
      (!a b c. f a (f b c) = f b (f a c)) ==>
       (!e l. FOLDR f e (REVERSE l) = FOLDR f e l)`--),
    GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC
    THEN ASM_REWRITE_TAC[REVERSE, FOLDR, FOLDR_SNOC]
    THEN IMP_RES_TAC FOLDR1 THEN ASM_REWRITE_TAC[]);

val FOLDR_MAP_REVERSE = store_thm("FOLDR_MAP_REVERSE",
    (--`!(f:'a->'a->'a).
      (!a b c. f a (f b c) = f b (f a c)) ==>
       (!e (g:'b->'a) l. FOLDR f e (MAP g (REVERSE l)) = FOLDR f e (MAP g l))`--),
    GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC
    THEN ASM_REWRITE_TAC[REVERSE, FOLDR, FOLDR_SNOC,MAP,MAP_SNOC]
    THEN IMP_RES_TAC FOLDR1 THEN ASM_REWRITE_TAC[]);

val FOLDR_FILTER_REVERSE = store_thm("FOLDR_FILTER_REVERSE",
    (--`!(f:'a->'a->'a).
      (!a b c. f a (f b c) = f b (f a c)) ==>
       (!e (P:'a->bool) l. 
           FOLDR f e (FILTER P (REVERSE l)) = FOLDR f e (FILTER P l))`--),
    GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC
    THEN ASM_REWRITE_TAC[REVERSE, FOLDR, FOLDR_SNOC,FILTER,FILTER_SNOC]
    THEN IMP_RES_TAC FOLDR1 THEN GEN_TAC THEN COND_CASES_TAC THENL[
    	ASM_REWRITE_TAC[ FOLDR, FOLDR_SNOC,FILTER,FILTER_SNOC]
    	THEN ASM_REWRITE_TAC[GSYM FILTER_REVERSE],
    	ASM_REWRITE_TAC[ FOLDR, FOLDR_SNOC,FILTER,FILTER_SNOC]]);

val FOLDL_REVERSE2 = prove(
    (--`!(f:'a->'a->'a).
      (!a b c. f (f a b) c = f (f a c) b) ==>
       (!e l. FOLDL f e (REVERSE l) = FOLDL f e l)`--),
    GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN SNOC_INDUCT_TAC
    THEN ASM_REWRITE_TAC[REVERSE,REVERSE_SNOC, FOLDL, FOLDL_SNOC]
    THEN IMP_RES_TAC FOLDL1 THEN ASM_REWRITE_TAC[]);

val COMM_ASSOC_LEM1 = prove(
    (--`!(f:'a->'a->'a). COMM f ==> (ASSOC f ==>
      (!a b c. f a (f b c) = f b (f a c)))`--),
    REWRITE_TAC[ASSOC_DEF] THEN REPEAT STRIP_TAC
    THEN ASM_REWRITE_TAC[] THEN SUBST1_TAC(SPECL [(--`a:'a`--),(--`b:'a`--)]
      (REWRITE_RULE [COMM_DEF] (ASSUME (--`COMM (f:'a->'a->'a)`--))))
    THEN REWRITE_TAC[]);

val COMM_ASSOC_LEM2 = prove(
    (--`!(f:'a->'a->'a). COMM f ==> (ASSOC f ==>
      (!a b c. f (f a b) c = f (f a c) b))`--),
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC
      [GSYM (REWRITE_RULE[ASSOC_DEF] (ASSUME (--`ASSOC (f:'a->'a->'a)`--)))]
    THEN SUBST1_TAC(SPECL [(--`b:'a`--),(--`c:'a`--)]
      (REWRITE_RULE [COMM_DEF] (ASSUME (--`COMM (f:'a->'a->'a)`--))))
    THEN REWRITE_TAC[]);

val COMM_ASSOC_FOLDR_REVERSE = store_thm("COMM_ASSOC_FOLDR_REVERSE",
    (--`!f:'a->'a->'a. COMM f ==> (ASSOC f ==>
       (!e l. FOLDR f e (REVERSE l) = FOLDR f e l))`--),
    REPEAT STRIP_TAC THEN MATCH_MP_TAC FOLDR_REVERSE2
    THEN REPEAT GEN_TAC
    THEN IMP_RES_TAC COMM_ASSOC_LEM1
    THEN ACCEPT_TAC
      (SPEC_ALL
         (ASSUME (--`!c b a. (f:'a->'a->'a) a (f b c) = f b (f a c)`--))));

val COMM_ASSOC_FOLDL_REVERSE = store_thm("COMM_ASSOC_FOLDL_REVERSE",
    (--`!f:'a->'a->'a. COMM f ==> (ASSOC f ==>
       (!e l. FOLDL f e (REVERSE l) = FOLDL f e l))`--),
    REPEAT STRIP_TAC THEN MATCH_MP_TAC FOLDL_REVERSE2
    THEN IMP_RES_TAC COMM_ASSOC_LEM2
    THEN REPEAT GEN_TAC
    THEN ACCEPT_TAC
      (SPEC_ALL
         (ASSUME (--`!c b a. (f:'a->'a->'a) (f a b) c = f (f a c) b`--))));



(*<------------------------------------------------------------>*)
val ELL_LAST = store_thm("ELL_LAST",
    (--`!l:'a list. ~(NULL l) ==> (ELL 0 l = LAST l)`--),
    SNOC_INDUCT_TAC THENL[
      REWRITE_TAC[NULL],
      REPEAT STRIP_TAC THEN REWRITE_TAC[ELL]]);

val ELL_0_SNOC = store_thm("ELL_0_SNOC",
    (--`!l:'a list. !x. (ELL 0 (SNOC x l) = x)`--),
     REPEAT GEN_TAC THEN REWRITE_TAC[ELL,LAST]);

val ELL_SNOC = store_thm("ELL_SNOC",
    (--`!n. (0 < n) ==> !x (l:'a list).ELL n (SNOC x l) = ELL (PRE n) l`--),
    INDUCT_TAC THENL[
      REWRITE_TAC[NOT_LESS_0],
      REWRITE_TAC[ELL,BUTLAST,PRE,LESS_0]]);

(* |- !n x (l:'a list). (ELL (SUC n) (SNOC x l) = ELL n l) *)
val ELL_SUC_SNOC = save_thm("ELL_SUC_SNOC",
    GEN_ALL(PURE_ONCE_REWRITE_RULE[PRE]
    (MP (SPEC (--`SUC n`--) ELL_SNOC) (SPEC_ALL LESS_0))));

val ELL_CONS = store_thm("ELL_CONS",
    (--`!n (l:'a list). n < (LENGTH l) ==> (!x. ELL n (CONS x l) = ELL n l)`--),
    let val SNOC_lem = GSYM(CONJUNCT2 SNOC)
    in
    INDUCT_TAC THEN SNOC_INDUCT_TAC THEN REWRITE_TAC[NOT_LESS_0,LENGTH]
    THENL[
    	REPEAT STRIP_TAC THEN REWRITE_TAC[SNOC_lem,ELL_0_SNOC],
    	GEN_TAC THEN REWRITE_TAC[LENGTH_SNOC,LESS_MONO_EQ,
    	    ELL_SUC_SNOC,SNOC_lem]
    	THEN FIRST_ASSUM MATCH_ACCEPT_TAC]
    end);

val ELL_LENGTH_CONS = store_thm("ELL_LENGTH_CONS", 
    (--`!l:'a list. !x. (ELL (LENGTH l) (CONS x l) = x)`--),
    let val LAST_EL = (* (--`!x:'a. LAST [x] = x`--) *)
    GEN_ALL(REWRITE_RULE[SNOC](SPECL[(--`x:'a`--),(--`[]:'a list`--)]LAST))
    in
    SNOC_INDUCT_TAC THENL[
      REWRITE_TAC[ELL,LENGTH,LAST_EL],
      REWRITE_TAC[ELL,LENGTH_SNOC,BUTLAST,(GSYM(CONJUNCT2 SNOC))]
      THEN POP_ASSUM ACCEPT_TAC]
    end);

val ELL_LENGTH_SNOC = store_thm("ELL_LENGTH_SNOC", 
    (--`!l:'a list. !x. (ELL (LENGTH l) (SNOC x l) = (NULL l => x | HD l))`--),
    LIST_INDUCT_TAC THENL[
      REWRITE_TAC[ELL_0_SNOC,LENGTH,NULL],
      REWRITE_TAC[ELL_SUC_SNOC,LENGTH,HD,NULL,ELL_LENGTH_CONS]]);

val ELL_APPEND2 = store_thm("ELL_APPEND2",
    (--`!n l2. n < LENGTH l2 ==> !l1:'a list. ELL n (APPEND l1 l2) = ELL n l2`--),
    INDUCT_TAC THEN SNOC_INDUCT_TAC 
    THEN REWRITE_TAC[LENGTH,NOT_LESS_0]
    THEN REWRITE_TAC[APPEND_SNOC,ELL_0_SNOC,ELL_SUC_SNOC,
    	LENGTH_SNOC,LESS_MONO_EQ] THEN FIRST_ASSUM MATCH_ACCEPT_TAC);

val ELL_APPEND1 = store_thm("ELL_APPEND1",
    (--`!l2 n. LENGTH l2 <= n ==>
     !l1:'a list. ELL n (APPEND l1 l2) = ELL (n - LENGTH l2) l1`--),
    SNOC_INDUCT_TAC THEN REPEAT (FILTER_GEN_TAC (--`n:num`--))
    THEN INDUCT_TAC THEN REWRITE_TAC
    	[LENGTH,LENGTH_SNOC,SUB_0,APPEND_NIL,NOT_SUC_LESS_EQ_0]
    THEN REWRITE_TAC[LESS_EQ_MONO,ELL_SUC_SNOC,SUB_MONO_EQ,APPEND_SNOC]
    THEN FIRST_ASSUM MATCH_ACCEPT_TAC);

val ELL_PRE_LENGTH = store_thm("ELL_PRE_LENGTH",
    (--`!l:'a list. ~(l = []) ==> (ELL (PRE(LENGTH l)) l  = HD l)`--),
    LIST_INDUCT_TAC THEN REWRITE_TAC[LENGTH,PRE]
    THEN REPEAT STRIP_TAC THEN REWRITE_TAC[ELL_LENGTH_CONS,HD]);

val EL_LENGTH_SNOC = store_thm("EL_LENGTH_SNOC", 
    (--`!l:'a list. !x. EL (LENGTH l) (SNOC x l) = x`--),
    LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[EL,SNOC,HD,TL,LENGTH]);

val EL_PRE_LENGTH = store_thm("EL_PRE_LENGTH",
    (--`!l:'a list. ~(l = []) ==> (EL (PRE(LENGTH l)) l  = LAST l)`--),
    SNOC_INDUCT_TAC THEN REWRITE_TAC[LENGTH_SNOC,PRE,LAST,EL_LENGTH_SNOC]);

val EL_SNOC = store_thm("EL_SNOC",
    (--`!n (l:'a list). n < (LENGTH l) ==> (!x. EL n (SNOC x l) = EL n l)`--),
    INDUCT_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[LENGTH,NOT_LESS_0]
    THENL[
    	REWRITE_TAC[SNOC,EL,HD],
    	REWRITE_TAC[SNOC,EL,TL,LESS_MONO_EQ]
    	THEN FIRST_ASSUM MATCH_ACCEPT_TAC]);

val LESS_PRE_SUB_LESS = prove((--`!n m. (m < n) ==> (PRE(n - m) < n)`--),
    let val PRE_K_K = prove((--`!k . (0<k) ==> (PRE k < k)`--),
      INDUCT_THEN INDUCTION MP_TAC THEN
      REWRITE_TAC [LESS_REFL,LESS_0,PRE,LESS_SUC_REFL])
    in
    REPEAT INDUCT_TAC THENL[
    	REWRITE_TAC[NOT_LESS_0],
    	REWRITE_TAC[NOT_LESS_0],
    	REWRITE_TAC[SUB_0,PRE_K_K],
    	REWRITE_TAC[LESS_MONO_EQ,SUB_MONO_EQ]
    	THEN REWRITE_TAC[LESS_THM]
    	THEN STRIP_TAC THEN DISJ2_TAC THEN RES_TAC]
    end);

val EL_ELL = store_thm("EL_ELL",
    (--`!n (l:'a list). n < LENGTH l ==> (EL n l = ELL (PRE((LENGTH l) - n)) l)`--),
    INDUCT_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[LENGTH,NOT_LESS_0]
    THENL[
    	REWRITE_TAC[PRE,EL,ELL_LENGTH_CONS,HD,SUB_0],
        REWRITE_TAC[EL,TL,LESS_MONO_EQ,SUB_MONO_EQ]
    	THEN GEN_TAC THEN DISCH_TAC
    	THEN MAP_EVERY IMP_RES_TAC [LESS_PRE_SUB_LESS,ELL_CONS]
    	THEN RES_TAC THEN ASM_REWRITE_TAC[]]);

val EL_LENGTH_APPEND = store_thm("EL_LENGTH_APPEND",
  (--`!(l2:('a)list) (l1:('a)list) .
      ~(NULL l2)==> ( EL (LENGTH l1) (APPEND l1 l2) = HD l2)`--),
  GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC [LENGTH,APPEND,EL,TL,NULL]
  THEN REPEAT STRIP_TAC THEN RES_TAC);

val ELL_EL = store_thm("ELL_EL",
    (--`!n (l:'a list). n < LENGTH l ==> (ELL n l = EL (PRE((LENGTH l) - n)) l)`--),
    let val lem = prove((--`!n m. n < m ==> ?k. (m - n = SUC k) /\ k < m`--),
    	REPEAT INDUCT_TAC THEN REWRITE_TAC[NOT_LESS_0] THENL[
    	    REWRITE_TAC[SUB_0] THEN DISCH_TAC
    	    THEN EXISTS_TAC (--`m:num`--) THEN REWRITE_TAC[LESS_SUC_REFL],
    	    ASM_REWRITE_TAC[LESS_MONO_EQ,SUB_MONO_EQ]
    	    THEN DISCH_TAC THEN RES_TAC THEN EXISTS_TAC (--`k:num`--)
    	    THEN IMP_RES_TAC LESS_SUC THEN ASM_REWRITE_TAC[]])
    in
    INDUCT_TAC THEN SNOC_INDUCT_TAC THEN REWRITE_TAC[LENGTH,NOT_LESS_0]
    THENL[
        REWRITE_TAC[SUB_0,ELL_0_SNOC,LENGTH_SNOC,PRE,EL_LENGTH_SNOC],
    	REWRITE_TAC[LENGTH_SNOC,ELL_SUC_SNOC,SUB_MONO_EQ,LESS_MONO_EQ]
    	THEN REPEAT STRIP_TAC THEN RES_THEN SUBST1_TAC 
    	THEN MATCH_MP_TAC (GSYM EL_SNOC)
    	THEN IMP_RES_TAC lem THEN ASM_REWRITE_TAC[PRE]]
    end);

val ELL_MAP = store_thm("ELL_MAP",
    (--`!n l (f:'a->'b). n < (LENGTH l) ==> (ELL n (MAP f l) = f (ELL n l))`--),
    INDUCT_TAC THEN SNOC_INDUCT_TAC THEN REWRITE_TAC[LENGTH,NOT_LESS_0]
    THENL[
        REWRITE_TAC[ELL_0_SNOC,MAP_SNOC],
        REWRITE_TAC[LENGTH_SNOC,ELL_SUC_SNOC,MAP_SNOC,LESS_MONO_EQ] 
    	THEN FIRST_ASSUM MATCH_ACCEPT_TAC]);

val LENGTH_BUTLAST = store_thm("LENGTH_BUTLAST",
    (--`!l:'a list. ~(l = []) ==> (LENGTH(BUTLAST l) = PRE(LENGTH l))`--),
    SNOC_INDUCT_TAC THEN REWRITE_TAC[LENGTH_SNOC,BUTLAST,PRE]);

val BUTFIRSTN_LENGTH_APPEND = store_thm("BUTFIRSTN_LENGTH_APPEND",
    (--`!l1 l2:'a list. BUTFIRSTN(LENGTH l1)(APPEND l1 l2) = l2`--),
    LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[LENGTH,BUTFIRSTN,APPEND]);

val FIRSTN_APPEND1 = store_thm("FIRSTN_APPEND1",
    (--`!n (l1:'a list). n <= (LENGTH l1) ==>
     !l2. FIRSTN n (APPEND l1 l2) = FIRSTN n l1`--),
    INDUCT_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC
    	[LENGTH,NOT_SUC_LESS_EQ_0,FIRSTN,APPEND,CONS_11,LESS_EQ_MONO]
    THEN FIRST_ASSUM MATCH_ACCEPT_TAC);

val FIRSTN_APPEND2 = store_thm("FIRSTN_APPEND2",
    (--`!(l1:'a list) n. (LENGTH l1) <= n ==>
     !l2. FIRSTN n (APPEND l1 l2) = APPEND l1 (FIRSTN (n - (LENGTH l1)) l2)`--),
    LIST_INDUCT_TAC THEN REWRITE_TAC[LENGTH,APPEND,SUB_0]
    THEN GEN_TAC THEN INDUCT_TAC THEN REWRITE_TAC[NOT_SUC_LESS_EQ_0,
    	LESS_EQ_MONO,SUB_MONO_EQ,FIRSTN,CONS_11]
    THEN FIRST_ASSUM MATCH_ACCEPT_TAC);

val FIRSTN_LENGTH_APPEND = store_thm("FIRSTN_LENGTH_APPEND",
    (--`!(l1:'a list) l2. FIRSTN (LENGTH l1) (APPEND l1 l2) = l1`--),
    LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[LENGTH,FIRSTN,APPEND]);

(*<---------------------------------------------------------------------->*)

val REVERSE_FLAT = store_thm("REVERSE_FLAT",
   (--`!l:'a list list. REVERSE (FLAT l) = FLAT(REVERSE(MAP REVERSE l))`--),
   LIST_INDUCT_TAC THEN REWRITE_TAC[REVERSE,FLAT,MAP]
   THEN ASM_REWRITE_TAC[REVERSE_APPEND,FLAT_SNOC]);

val MAP_COND = prove(
   (--`!(f:'a-> 'b) c l1 l2.
        (MAP f (c => l1 | l2)) = (c => (MAP f l1) | (MAP f l2))`--),
   REPEAT GEN_TAC THEN BOOL_CASES_TAC (--`c:bool`--) THEN ASM_REWRITE_TAC[]);

val MAP_FILTER = store_thm("MAP_FILTER",
   (--`!(f:'a -> 'a) P l. 
        (!x. P (f x) = P x) ==>
             (MAP f (FILTER P l) = FILTER P (MAP f l))`--),
   GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[MAP,FILTER]
   THEN GEN_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[MAP_COND,MAP]
   THEN RES_THEN SUBST1_TAC THEN REFL_TAC);

val FLAT_APPEND = store_thm("FLAT_APPEND",
    (--`!l1 l2:'a list list.
         FLAT (APPEND l1 l2) = APPEND (FLAT l1) (FLAT l2)`--),
    LIST_INDUCT_TAC THEN REWRITE_TAC[APPEND,FLAT]
    THEN ASM_REWRITE_TAC[APPEND_ASSOC]);

val FLAT_REVERSE = store_thm("FLAT_REVERSE",
    (--`!l:'a list list. FLAT (REVERSE l) = REVERSE (FLAT (MAP REVERSE l))`--),
    LIST_INDUCT_TAC THEN  REWRITE_TAC[FLAT,REVERSE,MAP]
    THEN ASM_REWRITE_TAC[FLAT_SNOC,REVERSE_APPEND,REVERSE_REVERSE]);

val FLAT_FLAT = store_thm("FLAT_FLAT",
    (--`!l:'a list list list. FLAT (FLAT l) = FLAT(MAP FLAT l)`--),
    LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[FLAT,FLAT_APPEND,MAP]);

val ALL_EL_REVERSE = store_thm("ALL_EL_REVERSE",
    (--`!P (l:'a list). ALL_EL P (REVERSE l) = ALL_EL P l`--),
    GEN_TAC THEN LIST_INDUCT_TAC
    THEN ASM_REWRITE_TAC[ALL_EL,REVERSE,ALL_EL_SNOC]
    THEN GEN_TAC THEN MATCH_ACCEPT_TAC CONJ_SYM);

val SOME_EL_REVERSE = store_thm("SOME_EL_REVERSE",
    (--`!P (l:'a list). SOME_EL P (REVERSE l) = SOME_EL P l`--),
    GEN_TAC THEN LIST_INDUCT_TAC
    THEN ASM_REWRITE_TAC[SOME_EL,REVERSE,SOME_EL_SNOC]
    THEN GEN_TAC THEN MATCH_ACCEPT_TAC DISJ_SYM);

val ALL_EL_SEG = store_thm("ALL_EL_SEG",
    (--`!P (l:'a list). ALL_EL P l ==>
     !m k. (m + k) <= (LENGTH l) ==> ALL_EL P (SEG m k l)`--),
    GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[ALL_EL,SEG,LENGTH] THENL[
      REPEAT INDUCT_TAC
      THEN REWRITE_TAC[ADD,ADD_0,NOT_SUC_LESS_EQ_0,SEG,ALL_EL],

      GEN_TAC THEN STRIP_TAC THEN REPEAT INDUCT_TAC
      THEN REWRITE_TAC[ADD,ADD_0,NOT_SUC_LESS_EQ_0,LESS_EQ_MONO,SEG,ALL_EL]
      THENL[
        ASM_REWRITE_TAC[]
        THEN RES_THEN
            (ASSUME_TAC o 
             (REWRITE_RULE[ADD_0]) o
             (SPECL [(--`0`--),(--`m:num`--)]))
    	THEN DISCH_TAC THEN RES_TAC,
    	let val lem = SPEC(--`k:num`--) (GEN (--`n:num`--)
    	    (SYM(TRANS (SPEC_ALL(CONJUNCT2 ADD)) (SPEC_ALL ADD_SUC))))
        in
    	SUBST1_TAC lem THEN DISCH_TAC THEN RES_TAC
        end]]);

val ALL_EL_FIRSTN = store_thm("ALL_EL_FIRSTN",
    (--`!P (l:'a list). ALL_EL P l ==>
     !m. m <= (LENGTH l) ==> ALL_EL P (FIRSTN m l)`--),
    REPEAT STRIP_TAC THEN IMP_RES_THEN SUBST1_TAC FIRSTN_SEG
    THEN IMP_RES_THEN MATCH_MP_TAC ALL_EL_SEG
    THEN ASM_REWRITE_TAC[ADD_0]);

val ALL_EL_BUTFIRSTN = store_thm("ALL_EL_BUTFIRSTN",
    (--`!P (l:'a list). ALL_EL P l ==>
     !m. m <= (LENGTH l) ==> ALL_EL P (BUTFIRSTN m l)`--),
    REPEAT STRIP_TAC THEN IMP_RES_THEN SUBST1_TAC BUTFIRSTN_SEG
    THEN IMP_RES_THEN MATCH_MP_TAC ALL_EL_SEG
    THEN IMP_RES_THEN SUBST1_TAC SUB_ADD
    THEN MATCH_ACCEPT_TAC LESS_EQ_REFL);

val SOME_EL_SEG = store_thm("SOME_EL_SEG",
    (--`!m k (l:'a list). (m + k) <= (LENGTH l) ==> 
     !P. SOME_EL P (SEG m k l) ==> SOME_EL P l`--),
    REPEAT INDUCT_TAC THEN LIST_INDUCT_TAC
    THEN REWRITE_TAC[SOME_EL,SEG,LENGTH,ADD,ADD_0,NOT_SUC_LESS_EQ_0]
    THEN GEN_TAC THEN REWRITE_TAC[LESS_EQ_MONO] THENL[
      FIRST_ASSUM (ASSUME_TAC o (REWRITE_RULE[ADD_0]) o (SPEC(--`0`--)))
      THEN REPEAT STRIP_TAC THENL[
    	DISJ1_TAC THEN FIRST_ASSUM ACCEPT_TAC,
    	DISJ2_TAC THEN RES_TAC],
    	let val lem = SPEC(--`k:num`--) (GEN (--`n:num`--)
    	    (SYM(TRANS (SPEC_ALL(CONJUNCT2 ADD)) (SPEC_ALL ADD_SUC))))
       in
    	SUBST1_TAC lem THEN REPEAT STRIP_TAC THEN DISJ2_TAC THEN RES_TAC
       end]);

val SOME_EL_FIRSTN = store_thm("SOME_EL_FIRSTN",
    (--`!m (l:'a list). m <= (LENGTH l) ==>
    	!P.  SOME_EL P (FIRSTN m l) ==> SOME_EL P l`--),
    REPEAT GEN_TAC THEN DISCH_TAC THEN IMP_RES_THEN SUBST1_TAC FIRSTN_SEG
    THEN MATCH_MP_TAC SOME_EL_SEG THEN ASM_REWRITE_TAC[ADD_0]);

val SOME_EL_BUTFIRSTN = store_thm("SOME_EL_BUTFIRSTN",
    (--`!m (l:'a list). m <= (LENGTH l) ==>
     !P. SOME_EL P (BUTFIRSTN m l) ==> SOME_EL P l`--),
    REPEAT GEN_TAC THEN DISCH_TAC THEN IMP_RES_THEN SUBST1_TAC BUTFIRSTN_SEG
    THEN MATCH_MP_TAC SOME_EL_SEG THEN IMP_RES_THEN SUBST1_TAC SUB_ADD
    THEN MATCH_ACCEPT_TAC LESS_EQ_REFL);

val SOME_EL_LASTN = store_thm("SOME_EL_LASTN",
    (--`!m (l:'a list). m <= (LENGTH l) ==>
     !P. SOME_EL P (LASTN m l) ==> SOME_EL P l`--),
    REPEAT GEN_TAC THEN DISCH_TAC THEN IMP_RES_THEN SUBST1_TAC LASTN_SEG
    THEN MATCH_MP_TAC SOME_EL_SEG THEN PURE_ONCE_REWRITE_TAC[ADD_SYM]
    THEN IMP_RES_THEN SUBST1_TAC SUB_ADD THEN MATCH_ACCEPT_TAC LESS_EQ_REFL);

val SOME_EL_BUTLASTN = store_thm("SOME_EL_BUTLASTN",
    (--`!m (l:'a list). m <= (LENGTH l) ==>
     !P. SOME_EL P (BUTLASTN m l) ==> SOME_EL P l`--),
    REPEAT GEN_TAC THEN DISCH_TAC THEN IMP_RES_THEN SUBST1_TAC BUTLASTN_SEG
    THEN MATCH_MP_TAC SOME_EL_SEG THEN PURE_ONCE_REWRITE_TAC[ADD_0]
    THEN MATCH_ACCEPT_TAC SUB_LESS_EQ);

val IS_EL_REVERSE = store_thm("IS_EL_REVERSE",
    (--`!(x:'a) l. IS_EL x (REVERSE l) = IS_EL x l`--),
    GEN_TAC THEN LIST_INDUCT_TAC 
    THEN ASM_REWRITE_TAC[REVERSE,IS_EL,IS_EL_SNOC]);

val IS_EL_FILTER = store_thm("IS_EL_FILTER",
    (--`!P (x:'a). P x ==> !l. IS_EL x (FILTER P l) = IS_EL x l`--),
    REPEAT GEN_TAC THEN DISCH_TAC THEN LIST_INDUCT_TAC
    THEN REWRITE_TAC[FILTER,IS_EL] THEN GEN_TAC THEN COND_CASES_TAC
    THEN ASM_REWRITE_TAC[IS_EL] THEN EQ_TAC THENL[
    	DISCH_TAC THEN DISJ2_TAC THEN FIRST_ASSUM ACCEPT_TAC,
    	STRIP_TAC THEN POP_ASSUM SUBST_ALL_TAC THEN RES_TAC]);

val IS_EL_SEG = store_thm("IS_EL_SEG",
    (--`!n m (l:'a list). ((n + m) <= (LENGTH l)) ==>
     !x. IS_EL x (SEG n m l) ==> IS_EL x l`--),
    REPEAT INDUCT_TAC THEN LIST_INDUCT_TAC
    THEN REWRITE_TAC[ADD,ADD_0,NOT_SUC_LESS_EQ_0,LENGTH,IS_EL,
    	SEG,LESS_EQ_MONO] THEN GEN_TAC THENL[
    	DISCH_TAC THEN FIRST_ASSUM (IMP_RES_TAC o
    	    (REWRITE_RULE[ADD_0]) o (SPEC(--`0`--)))
    	THEN GEN_TAC THEN DISCH_THEN (DISJ_CASES_THEN2 
    	    (fn t => DISJ1_TAC THEN ACCEPT_TAC t)
    	    (fn t => DISJ2_TAC THEN ASSUME_TAC t THEN RES_TAC)),
    	let val lem = (GEN_ALL
    	    (SYM(TRANS (SPEC_ALL(CONJUNCT2 ADD)) (SPEC_ALL ADD_SUC))))
        in
    	PURE_ONCE_REWRITE_TAC[lem] THEN REPEAT STRIP_TAC
    	THEN DISJ2_TAC THEN RES_TAC
        end]);

val IS_EL_SOME_EL = store_thm("IS_EL_SOME_EL",
    (--`!(x:'a) l. IS_EL x l = SOME_EL ($= x) l`--),
    GEN_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[IS_EL,SOME_EL]);

val IS_EL_FIRSTN = store_thm("IS_EL_FIRSTN",
    (--`!m l. m <= (LENGTH l) ==> !x:'a.  IS_EL x (FIRSTN m l) ==> IS_EL x l`--),
    PURE_ONCE_REWRITE_TAC[IS_EL_SOME_EL] THEN REPEAT STRIP_TAC
    THEN IMP_RES_TAC SOME_EL_FIRSTN);

val IS_EL_BUTFIRSTN = store_thm("IS_EL_BUTFIRSTN",
    (--`!m l. m <= (LENGTH l) ==> !x:'a.  IS_EL x (BUTFIRSTN m l) ==> IS_EL x l`--),
    PURE_ONCE_REWRITE_TAC[IS_EL_SOME_EL] THEN REPEAT STRIP_TAC
    THEN IMP_RES_TAC SOME_EL_BUTFIRSTN);

val IS_EL_BUTLASTN = store_thm("IS_EL_BUTLASTN",
    (--`!m l. m <= (LENGTH l) ==> !x:'a.  IS_EL x (BUTLASTN m l) ==> IS_EL x l`--),
    PURE_ONCE_REWRITE_TAC[IS_EL_SOME_EL] THEN REPEAT STRIP_TAC
    THEN IMP_RES_TAC SOME_EL_BUTLASTN);

val IS_EL_LASTN = store_thm("IS_EL_LASTN",
    (--`!m l. m <= (LENGTH l) ==> !x:'a.  IS_EL x (LASTN m l) ==> IS_EL x l`--),
    PURE_ONCE_REWRITE_TAC[IS_EL_SOME_EL] THEN REPEAT STRIP_TAC
    THEN IMP_RES_TAC SOME_EL_LASTN);


val ZIP_SNOC = store_thm("ZIP_SNOC",
    (--`!l1 l2. (LENGTH l1 = LENGTH l2) ==>
     !(x1:'a) (x2:'b). 
      ZIP((SNOC x1 l1), (SNOC x2 l2)) = SNOC (x1,x2) (ZIP(l1,l2))`--),
    LIST_INDUCT_TAC THEN REPEAT (FILTER_GEN_TAC (--`l2:'b list`--))
    THEN LIST_INDUCT_TAC THEN REWRITE_TAC[SNOC,ZIP,LENGTH,NOT_SUC,SUC_NOT]
    THEN REWRITE_TAC[INV_SUC_EQ,CONS_11] THEN REPEAT STRIP_TAC
    THEN RES_THEN MATCH_ACCEPT_TAC);

val UNZIP_SNOC = store_thm("UNZIP_SNOC",
    (--`!(x:'a # 'b) l.
     UNZIP(SNOC x l) = (SNOC(FST x)(FST(UNZIP l)), SNOC(SND x)(SND(UNZIP l)))`--),
    GEN_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[SNOC,UNZIP]);

val LENGTH_ZIP = store_thm("LENGTH_ZIP",
    (--`!l1:'a list. !l2:'b list. (LENGTH l1 = LENGTH l2) ==>
    (LENGTH(ZIP(l1,l2)) = LENGTH l1) /\ (LENGTH(ZIP(l1,l2)) = LENGTH l2)`--),
    LIST_INDUCT_TAC THEN REPEAT (FILTER_GEN_TAC (--`l2:'b list`--))
    THEN LIST_INDUCT_TAC
    THEN REWRITE_TAC[ZIP,LENGTH,NOT_SUC,SUC_NOT,INV_SUC_EQ]
    THEN DISCH_TAC THEN RES_TAC THEN ASM_REWRITE_TAC[]);

val LENGTH_UNZIP_FST = store_thm("LENGTH_UNZIP_FST",
    (--`!l:('a # 'b)list. LENGTH (UNZIP_FST l) = LENGTH l`--),
    PURE_ONCE_REWRITE_TAC[UNZIP_FST_DEF]
    THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[UNZIP,LENGTH]);

val LENGTH_UNZIP_SND = store_thm("LENGTH_UNZIP_SND",
    (--`!l:('a # 'b)list. LENGTH (UNZIP_SND l) = LENGTH l`--),
    PURE_ONCE_REWRITE_TAC[UNZIP_SND_DEF]
    THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[UNZIP,LENGTH]);

val ZIP_UNZIP = store_thm("ZIP_UNZIP",
    (--`!l:('a # 'b)list. ZIP(UNZIP l) = l`--),
    LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[UNZIP,ZIP]);

val UNZIP_ZIP = store_thm("UNZIP_ZIP",
    (--`!l1:'a list. !l2:'b list.
     (LENGTH l1 = LENGTH l2) ==> (UNZIP(ZIP(l1,l2)) = (l1,l2))`--),
    LIST_INDUCT_TAC THEN REPEAT (FILTER_GEN_TAC (--`l2:'b list`--))
    THEN LIST_INDUCT_TAC
    THEN ASM_REWRITE_TAC[UNZIP,ZIP,LENGTH,NOT_SUC,SUC_NOT,INV_SUC_EQ]
    THEN REPEAT STRIP_TAC THEN RES_THEN SUBST1_TAC THEN REWRITE_TAC[]);

val SUM_APPEND = store_thm("SUM_APPEND",
    (--`!l1 l2. SUM (APPEND l1 l2) = SUM l1 + SUM l2`--),
    LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[SUM,APPEND,ADD,ADD_0,ADD_ASSOC]);

val SUM_REVERSE = store_thm("SUM_REVERSE",
    (--`!l. SUM (REVERSE l) = SUM l`--),
    LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[SUM,REVERSE,SUM_SNOC]
    THEN MATCH_ACCEPT_TAC ADD_SYM);

val SUM_FLAT = store_thm("SUM_FLAT",
    (--`!l. SUM (FLAT l) = SUM (MAP SUM l)`--),
    LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[SUM,FLAT,MAP,SUM_APPEND]);

val EL_APPEND1 = store_thm("EL_APPEND1",
    (--`!n l1 (l2:'a list). n < (LENGTH l1) ==> (EL n (APPEND l1 l2) = EL n l1)`--),
    INDUCT_TAC THEN LIST_INDUCT_TAC
    THEN ASM_REWRITE_TAC[EL,APPEND,HD,TL,LENGTH,NOT_LESS_0,LESS_MONO_EQ]);

val EL_APPEND2 = store_thm("EL_APPEND2",
    (--`!(l1:'a list) n. (LENGTH l1) <= n ==>
     !l2. EL n (APPEND l1 l2) = EL (n - (LENGTH l1)) l2`--),
    LIST_INDUCT_TAC THEN REWRITE_TAC[LENGTH,APPEND,SUB_0]
    THEN GEN_TAC THEN INDUCT_TAC THEN ASM_REWRITE_TAC[EL,APPEND,HD,TL,
    	LENGTH,NOT_SUC_LESS_EQ_0,SUB_MONO_EQ,LESS_EQ_MONO]);

val EL_MAP = store_thm("EL_MAP",
    (--`!n l. n < (LENGTH l) ==> !f:'a->'b. EL n (MAP f l) = f (EL n l)`--),
    INDUCT_TAC THEN LIST_INDUCT_TAC
    THEN ASM_REWRITE_TAC[LENGTH,EL,MAP,LESS_MONO_EQ,NOT_LESS_0,HD,TL]);

val EL_CONS = store_thm("EL_CONS",
    (--`!n. 0 < n ==> !(x:'a) l. EL n (CONS x l) = EL (PRE n) l`--),
    INDUCT_TAC THEN ASM_REWRITE_TAC[NOT_LESS_0,EL,HD,TL,PRE]);

val EL_SEG = store_thm("EL_SEG",
    (--`!n (l:'a list). n < (LENGTH l) ==> (EL n l = HD (SEG 1 n l))`--),
    INDUCT_TAC THEN LIST_INDUCT_TAC
    THEN ASM_REWRITE_TAC[LENGTH,EL,HD,TL,NOT_LESS_0,LESS_MONO_EQ]
    THEN CONV_TAC (ONCE_DEPTH_CONV num_CONV) THEN REWRITE_TAC[SEG,HD]
    THEN DISCH_TAC THEN RES_THEN SUBST1_TAC
    THEN CONV_TAC (ONCE_DEPTH_CONV num_CONV) THEN REFL_TAC);

val EL_IS_EL = store_thm("EL_IS_EL",
    (--`!n (l:'a list). n < (LENGTH l) ==> (IS_EL (EL n l) l)`--),
    INDUCT_TAC THEN LIST_INDUCT_TAC
    THEN ASM_REWRITE_TAC[LENGTH,EL,HD,TL,NOT_LESS_0,LESS_MONO_EQ,IS_EL]
    THEN REPEAT STRIP_TAC THEN DISJ2_TAC THEN RES_TAC);

val TL_SNOC = store_thm("TL_SNOC",
    (--`!(x:'a) l. TL(SNOC x l) = ((NULL l) => [] | SNOC x (TL l))`--),
    GEN_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[SNOC,TL,NULL]);

val SUB_SUC_LESS = prove(
    (--`!m n. (n < m) ==> (m - (SUC n)) < m`--),
    INDUCT_TAC THEN REWRITE_TAC[NOT_LESS_0,SUB_MONO_EQ]
    THEN INDUCT_TAC THENL[
    	REWRITE_TAC[SUB_0,LESS_SUC_REFL],
    	REWRITE_TAC[LESS_MONO_EQ] THEN DISCH_TAC THEN RES_TAC
    	THEN IMP_RES_TAC LESS_SUC]);

val EL_REVERSE = store_thm("EL_REVERSE",
    (--`!n (l:'a list). n < (LENGTH l) ==>
     (EL n (REVERSE l) = EL (PRE(LENGTH l - n)) l)`--),
    INDUCT_TAC THEN SNOC_INDUCT_TAC
    THEN ASM_REWRITE_TAC[LENGTH,LENGTH_SNOC,
    	EL,HD,TL,NOT_LESS_0,LESS_MONO_EQ,SUB_0] THENL[
    	REWRITE_TAC[REVERSE_SNOC,PRE,EL_LENGTH_SNOC,HD],
    	REWRITE_TAC[REVERSE_SNOC,SUB_MONO_EQ,TL]
    	THEN REPEAT STRIP_TAC THEN RES_THEN SUBST1_TAC
    	THEN MATCH_MP_TAC (GSYM EL_SNOC)
    	THEN REWRITE_TAC(PRE_SUB1 :: (map GSYM [SUB_PLUS,ADD1]))
    	THEN IMP_RES_TAC SUB_SUC_LESS]);

val EL_REVERSE_ELL = store_thm("EL_REVERSE_ELL",
    (--`!n (l:'a list). n < (LENGTH l) ==> (EL n (REVERSE l) = ELL n l)`--),
    INDUCT_TAC THEN SNOC_INDUCT_TAC
    THEN ASM_REWRITE_TAC[LENGTH,LENGTH_SNOC,REVERSE_SNOC,
    	EL,ELL,HD,TL,LAST,BUTLAST,NOT_LESS_0,LESS_MONO_EQ,SUB_0]);

val ELL_LENGTH_APPEND = store_thm("ELL_LENGTH_APPEND",
    (--`!(l1:('a)list) (l2:('a)list).
      ~(NULL l1)==> (ELL (LENGTH l2) (APPEND l1 l2) = LAST l1)`--),
    GEN_TAC THEN SNOC_INDUCT_TAC
    THEN ASM_REWRITE_TAC
    	[LENGTH,LENGTH_SNOC,APPEND_SNOC,APPEND_NIL,ELL,TL,BUTLAST]);

val ELL_IS_EL = store_thm("ELL_IS_EL",
    (--`!n (l:'a list). n < (LENGTH l) ==> (IS_EL (EL n l) l)`--),
    INDUCT_TAC THEN LIST_INDUCT_TAC
    THEN ASM_REWRITE_TAC[LENGTH,EL,HD,TL,NOT_LESS_0,LESS_MONO_EQ,IS_EL]
    THEN REPEAT STRIP_TAC THEN DISJ2_TAC THEN RES_TAC);

val ELL_REVERSE = store_thm("ELL_REVERSE",
    (--`!n (l:'a list). n < (LENGTH l) ==>
     (ELL n (REVERSE l) = ELL (PRE(LENGTH l - n)) l)`--),
    INDUCT_TAC THEN LIST_INDUCT_TAC
    THEN ASM_REWRITE_TAC[LENGTH,LENGTH_SNOC,REVERSE,SUB_0,ELL,LAST,
    	BUTLAST,NOT_LESS_0,LESS_MONO_EQ,PRE,ELL_LENGTH_CONS,SUB_MONO_EQ]
    THEN REPEAT STRIP_TAC THEN RES_THEN SUBST1_TAC
    THEN MATCH_MP_TAC (GSYM ELL_CONS)
    THEN REWRITE_TAC(PRE_SUB1 :: (map GSYM [SUB_PLUS,ADD1]))
    THEN IMP_RES_TAC SUB_SUC_LESS);

val ELL_REVERSE_EL = store_thm("ELL_REVERSE_EL",
    (--`!n (l:'a list). n < (LENGTH l) ==> (ELL n (REVERSE l) = EL n l)`--),
    INDUCT_TAC THEN LIST_INDUCT_TAC
    THEN ASM_REWRITE_TAC[LENGTH,LENGTH_SNOC,REVERSE,REVERSE_SNOC,
    	EL,ELL,HD,TL,LAST,BUTLAST,NOT_LESS_0,LESS_MONO_EQ,SUB_0]);


val LESS_EQ_SPLIT = 
    let val asm_thm = ASSUME (--`(m + n) <= p`--)
    in
    GEN_ALL(DISCH_ALL
     (CONJ(MP(SPECL [(--`n:num`--),(--`m+n`--),(--`p:num`--)] LESS_EQ_TRANS)
       	      (CONJ (SUBS [SPECL [(--`n:num`--),(--`m:num`--)] ADD_SYM]
                     (SPECL [(--`n:num`--),(--`m:num`--)] LESS_EQ_ADD)) asm_thm))
	  (MP (SPECL [(--`m:num`--),(--`m+n`--),(--`p:num`--)] LESS_EQ_TRANS)
               (CONJ (SPEC_ALL LESS_EQ_ADD) asm_thm))))
   end;

val SUB_GREATER_EQ_ADD = prove(
    (--`!p n m. (p >= n) ==> (((p - n) >= m) = (p >= (m + n)))`--),
    REWRITE_TAC[
      SYM (SPEC (--`n:num`--) (SPEC (--`p-n`--) (SPEC (--`m:num`--) 
           (REWRITE_RULE[GSYM GREATER_EQ] LESS_EQ_MONO_ADD_EQ))))]
    THEN REPEAT STRIP_TAC
    THEN POP_ASSUM (fn th => ASSUME_TAC
      (MP (SPEC (--`n:num`--) (SPEC (--`p:num`--) SUB_ADD)) 
          (REWRITE_RULE[SPEC (--`n:num`--) (SPEC (--`p:num`--) GREATER_EQ)] th)))
    THEN SUBST_TAC[(SPEC_ALL ADD_SYM)] THEN ASM_REWRITE_TAC[]);

(* SUB_LESS_EQ_ADD = |- !p n m. n <= p ==> (m <= (p - n) = (m + n) <= p) *)
val SUB_LESS_EQ_ADD = (REWRITE_RULE[GREATER_EQ] SUB_GREATER_EQ_ADD);

val FIRSTN_BUTLASTN = store_thm("FIRSTN_BUTLASTN",
    (--`!n (l:'a list). n <= (LENGTH l) ==>
     (FIRSTN n l = BUTLASTN ((LENGTH l) - n) l)`--),
    INDUCT_TAC THEN REWRITE_TAC[FIRSTN,BUTLASTN_LENGTH_NIL,SUB_0]
    THEN LIST_INDUCT_TAC THEN REWRITE_TAC[NOT_SUC_LESS_EQ_0,FIRSTN,LENGTH,
    	SUB_0,BUTLASTN,LESS_EQ_MONO,SUB_MONO_EQ]
    THEN GEN_TAC THEN DISCH_TAC THEN RES_THEN SUBST1_TAC
    THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC BUTLASTN_CONS
    THEN MATCH_ACCEPT_TAC SUB_LESS_EQ);

val BUTLASTN_FIRSTN = store_thm("BUTLASTN_FIRSTN",
    (--`!n (l:'a list). n <= (LENGTH l) ==>
     (BUTLASTN n l = FIRSTN ((LENGTH l) - n) l)`--),
    INDUCT_TAC THEN REWRITE_TAC[FIRSTN,BUTLASTN_LENGTH_NIL,SUB_0]
    THEN SNOC_INDUCT_TAC THEN REWRITE_TAC[NOT_SUC_LESS_EQ_0,LENGTH,LENGTH_SNOC,
    	SUB_0,BUTLASTN,FIRSTN,FIRSTN_LENGTH_ID,LESS_EQ_MONO,SUB_MONO_EQ]
    THEN GEN_TAC THEN DISCH_TAC THEN RES_THEN SUBST1_TAC
    THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC FIRSTN_SNOC
    THEN MATCH_ACCEPT_TAC SUB_LESS_EQ);

val LASTN_BUTFIRSTN = store_thm("LASTN_BUTFIRSTN",
    (--`!n (l:'a list). n <= (LENGTH l) ==>
     (LASTN n l = BUTFIRSTN ((LENGTH l) - n) l)`--),
    INDUCT_TAC THEN REWRITE_TAC[LASTN,BUTFIRSTN_LENGTH_NIL,SUB_0]
    THEN SNOC_INDUCT_TAC THEN REWRITE_TAC[NOT_SUC_LESS_EQ_0,LASTN,LENGTH,
    	LENGTH_SNOC,SUB_0,LESS_EQ_MONO,SUB_MONO_EQ]
    THEN GEN_TAC THEN DISCH_TAC THEN RES_THEN SUBST1_TAC
    THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC BUTFIRSTN_SNOC
    THEN MATCH_ACCEPT_TAC SUB_LESS_EQ);

val BUTFIRSTN_LASTN = store_thm("BUTFIRSTN_LASTN",
    (--`!n (l:'a list). n <= (LENGTH l) ==>
     (BUTFIRSTN n l = LASTN ((LENGTH l) - n) l)`--),
    INDUCT_TAC THEN REWRITE_TAC[LASTN_LENGTH_ID,BUTFIRSTN,SUB_0]
    THEN LIST_INDUCT_TAC THEN REWRITE_TAC[NOT_SUC_LESS_EQ_0,LASTN,LENGTH,
    	BUTFIRSTN,SUB_0,LESS_EQ_MONO,SUB_MONO_EQ]
    THEN GEN_TAC THEN DISCH_TAC THEN RES_THEN SUBST1_TAC
    THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC LASTN_CONS
    THEN MATCH_ACCEPT_TAC SUB_LESS_EQ);

val SUB_ADD_lem = prove(
    (--`!l n m. (n + m) <= l ==> ((l - (n + m)) + n = l - m)`--),
    REPEAT INDUCT_TAC 
    THEN REWRITE_TAC[ADD,ADD_0,SUB_0,NOT_SUC_LESS_EQ_0] THENL[
        MATCH_ACCEPT_TAC SUB_ADD,
    	PURE_ONCE_REWRITE_TAC [GSYM(CONJUNCT2 ADD)] 
    	THEN SUBST1_TAC (SYM (SPECL[(--`SUC n`--),(--`m:num`--)]ADD_SUC))
    	THEN REWRITE_TAC[SUB_MONO_EQ,LESS_EQ_MONO]
    	THEN FIRST_ASSUM MATCH_ACCEPT_TAC]);

val SEG_LASTN_BUTLASTN = store_thm("SEG_LASTN_BUTLASTN",
    (--`!n m (l:'a list). ((n + m) <= (LENGTH l)) ==>
     (SEG n m l = LASTN n (BUTLASTN ((LENGTH l) - (n + m)) l))`--),
    let val th2 = SUBS [(REWRITE_RULE[SUB_LESS_EQ]
        (SPECL[(--`(LENGTH (l:'a list)) - m`--), (--`l:'a list`--)]
           LENGTH_LASTN))]
    	(SPECL[(--`n:num`--),(--`LASTN((LENGTH l) - m)(l:'a list)`--)]
           FIRSTN_BUTLASTN)
        val  th3 = UNDISCH_ALL (SUBS[UNDISCH_ALL
        (SPECL[(--`LENGTH(l:'a list)`--),(--`m:num`--),(--`n:num`--)]SUB_LESS_EQ_ADD)] th2)
        val th4 = PURE_ONCE_REWRITE_RULE[ADD_SYM](REWRITE_RULE[
    	UNDISCH_ALL(SPECL[(--`LENGTH(l:'a list)`--),(--`n:num`--),(--`m:num`--)]SUB_ADD_lem),
    	SUB_LESS_EQ] 
    	(PURE_ONCE_REWRITE_RULE[ADD_SYM](SPECL
    	[(--`n:num`--),(--`(LENGTH (l:'a list)) - (n + m)`--),(--`l:'a list`--)]LASTN_BUTLASTN)))
    in
    REPEAT GEN_TAC THEN DISCH_TAC
    THEN IMP_RES_THEN SUBST1_TAC SEG_FIRSTN_BUTFIRSTN
    THEN IMP_RES_TAC LESS_EQ_SPLIT
    THEN SUBST1_TAC (UNDISCH_ALL(SPECL[(--`m:num`--),(--`l:'a list`--)] BUTFIRSTN_LASTN))
    THEN SUBST1_TAC th3 THEN REWRITE_TAC[GSYM SUB_PLUS]
    THEN SUBST_OCCS_TAC[([1],(SPEC_ALL ADD_SYM))]
    THEN CONV_TAC SYM_CONV THEN ACCEPT_TAC th4
    end);

val BUTFIRSTN_REVERSE = store_thm("BUTFIRSTN_REVERSE",
    (--`!n (l:'a list). n <= (LENGTH l) ==>
     (BUTFIRSTN n (REVERSE l) = REVERSE(BUTLASTN n l))`--),
    INDUCT_TAC THEN SNOC_INDUCT_TAC THEN ASM_REWRITE_TAC[NOT_SUC_LESS_EQ_0, 
    	LENGTH,LENGTH_SNOC,BUTFIRSTN,BUTLASTN,LESS_EQ_MONO,REVERSE_SNOC]);

val BUTLASTN_REVERSE = store_thm("BUTLASTN_REVERSE",
    (--`!n (l:'a list). n <= (LENGTH l) ==>
     (BUTLASTN n (REVERSE l) = REVERSE(BUTFIRSTN n l))`--),
    INDUCT_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[NOT_SUC_LESS_EQ_0, 
    	LENGTH,BUTFIRSTN,BUTLASTN,LESS_EQ_MONO,REVERSE]);
    
val LASTN_REVERSE = store_thm("LASTN_REVERSE",
    (--`!n (l:'a list). n <= (LENGTH l) ==>
     (LASTN n (REVERSE l) = REVERSE(FIRSTN n l))`--),
    INDUCT_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[NOT_SUC_LESS_EQ_0, 
    	LENGTH,FIRSTN,LASTN,LESS_EQ_MONO,REVERSE,SNOC_11]);

val FIRSTN_REVERSE = store_thm("FIRSTN_REVERSE",
    (--`!n (l:'a list). n <= (LENGTH l) ==>
     (FIRSTN n (REVERSE l) = REVERSE(LASTN n l))`--),
    INDUCT_TAC THEN SNOC_INDUCT_TAC
    THEN ASM_REWRITE_TAC[NOT_SUC_LESS_EQ_0,LENGTH,LENGTH_SNOC,
    	FIRSTN,LASTN,LESS_EQ_MONO,REVERSE,REVERSE_SNOC,CONS_11]);

val SEG_REVERSE = store_thm("SEG_REVERSE",
    (--`!n m (l:'a list). ((n + m) <= (LENGTH l)) ==>
     (SEG n m (REVERSE l) =  REVERSE(SEG n (LENGTH l - (n + m)) l))`--),
    let val LEN_REV = (SPEC(--`l:'a list`--) LENGTH_REVERSE)
    val SUB_LE_ADD = 
    	SPECL[(--`LENGTH(l:'a list)`--),(--`m:num`--),(--`n:num`--)]SUB_LESS_EQ_ADD
    val SEG_lem = REWRITE_RULE[SUB_LESS_EQ](PURE_ONCE_REWRITE_RULE[ADD_SYM]
    	(SUBS[UNDISCH_ALL(SPEC_ALL(SPEC(--`LENGTH(l:'a list)`--) SUB_ADD_lem))]
    	 (PURE_ONCE_REWRITE_RULE[ADD_SYM]
    	  (SPECL[(--`n:num`--),(--`LENGTH(l:'a list) -(n+m)`--),(--`l:'a list`--)]
    	    SEG_LASTN_BUTLASTN))))
    val lem = PURE_ONCE_REWRITE_RULE[ADD_SUB](PURE_ONCE_REWRITE_RULE[ADD_SYM]
    	(SPEC (--`LENGTH(l:'a list)`--)
    	 (UNDISCH_ALL(SPECL[(--`LENGTH(l:'a list)`--),(--`m:num`--)]SUB_SUB))))    in
    REPEAT GEN_TAC THEN DISCH_TAC
    THEN FIRST_ASSUM (SUBST1_TAC o (MATCH_MP  SEG_FIRSTN_BUTFIRSTN)
    	o (SUBS[SYM LEN_REV]))
    THEN IMP_RES_TAC LESS_EQ_SPLIT
    THEN IMP_RES_THEN SUBST1_TAC (SPECL[(--`m:num`--),(--`l:'a list`--)]BUTFIRSTN_REVERSE)
    THEN FIRST_ASSUM 
    	(ASSUME_TAC o (MP(SPECL[(--`m:num`--),(--`(l:'a list)`--)]LENGTH_BUTLASTN)))
    THEN FIRST_ASSUM (fn t =>  ASSUME_TAC (SUBS[t]
    	(SPECL[(--`n:num`--),(--`BUTLASTN m (l:'a list)`--)]FIRSTN_REVERSE)))
    THEN FIRST_ASSUM (SUBST_ALL_TAC o (MP SUB_LE_ADD))
    THEN RES_THEN SUBST1_TAC THEN AP_TERM_TAC
    THEN SUBST1_TAC SEG_lem THEN SUBST1_TAC lem THEN REFL_TAC
    end);

(*<---------------------------------------------------------------->*)
val LENGTH_GENLIST = store_thm("LENGTH_GENLIST",
    (--`!(f:num->'a) n. LENGTH(GENLIST f n) = n`--),
    GEN_TAC THEN INDUCT_TAC
    THEN ASM_REWRITE_TAC[GENLIST,LENGTH,LENGTH_SNOC]);

val LENGTH_REPLICATE = store_thm("LENGTH_REPLICATE",
    (--`!n (x:'a). LENGTH(REPLICATE n x) = n`--),
    INDUCT_TAC THEN ASM_REWRITE_TAC[REPLICATE,LENGTH]);

val IS_EL_REPLICATE = store_thm("IS_EL_REPLICATE",
    (--`!n. 0 < n ==> !x:'a. IS_EL x (REPLICATE n x)`--),
    INDUCT_TAC THEN ASM_REWRITE_TAC[NOT_LESS_0,IS_EL,REPLICATE]);

val ALL_EL_REPLICATE = store_thm("ALL_EL_REPLICATE",
    (--`!(x:'a) n. ALL_EL ($= x) (REPLICATE n x)`--),
    GEN_TAC THEN INDUCT_TAC
    THEN ASM_REWRITE_TAC[NOT_LESS_0,ALL_EL,REPLICATE]);


val AND_EL_FOLDL = save_thm("AND_EL_FOLDL",
    GEN_ALL (CONV_RULE (DEPTH_CONV ETA_CONV)
    (REWRITE_RULE[ALL_EL_FOLDL,I_THM](AP_THM AND_EL_DEF (--`l:bool list`--)))));

val AND_EL_FOLDR = save_thm("AND_EL_FOLDR",
    GEN_ALL (CONV_RULE (DEPTH_CONV ETA_CONV)
    (REWRITE_RULE[ALL_EL_FOLDR,I_THM](AP_THM AND_EL_DEF (--`l:bool list`--)))));

val OR_EL_FOLDL = save_thm("OR_EL_FOLDL",
    GEN_ALL (CONV_RULE (DEPTH_CONV ETA_CONV)
    (REWRITE_RULE[SOME_EL_FOLDL,I_THM](AP_THM OR_EL_DEF (--`l:bool list`--)))));

val OR_EL_FOLDR = save_thm("OR_EL_FOLDR",
    GEN_ALL (CONV_RULE (DEPTH_CONV ETA_CONV)
    (REWRITE_RULE[SOME_EL_FOLDR,I_THM](AP_THM OR_EL_DEF (--`l:bool list`--)))));

val MAP2_ZIP = store_thm("MAP2_ZIP",
    (--`!l1 l2. (LENGTH l1 = LENGTH l2) ==>
     !f:'a->'b->'c. MAP2 f l1 l2 = MAP (UNCURRY f) (ZIP (l1,l2))`--),
    let val UNCURRY_DEF = definition "pair" "UNCURRY_DEF"
    in
    LIST_INDUCT_TAC THEN REPEAT (FILTER_GEN_TAC (--`l2:'b list`--))
    THEN LIST_INDUCT_TAC THEN REWRITE_TAC[MAP,MAP2,ZIP,LENGTH,NOT_SUC,SUC_NOT]
    THEN ASM_REWRITE_TAC[CONS_11,UNCURRY_DEF,INV_SUC_EQ]
    end);

export_theory();
