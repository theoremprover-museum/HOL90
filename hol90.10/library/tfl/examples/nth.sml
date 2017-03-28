(*---------------------------------------------------------------------------
 * Underspecified functions and how they get handled.
 *---------------------------------------------------------------------------*)
new_theory"nth" handle _ => ();
new_parent"kls_list";


val ARITH = EQT_ELIM o ARITH_CONV o Term;
val ARITH_TAC = CONV_TAC ARITH_CONV;

val mem_def = definition "kls_list" "mem_def";

(* Auxiliary facts *)
val [HD,TL,LENGTH]      = map (definition "list") ["HD","TL","LENGTH"];
val [LESS_0,NOT_LESS_0] = map (theorem"prim_rec") ["LESS_0", "NOT_LESS_0"];
val LESS_MONO_EQ = theorem"arithmetic" "LESS_MONO_EQ";

(*---------------------------------------------------------------------------
 * This is a "partial" function. Well, to be clear, it is a total function in
 * HOL, but the user is not given any rule for finding the value when the 
 * list is empty. In ML, applying a program compiled from this description 
 * to an empty list will raise a Match exception.
 *---------------------------------------------------------------------------*)
val nth_def = 
Rfunction `inv_image ^pred FST` 
   `(nth(0, h::t) = (h:'a)) /\
    (nth(SUC n, h::t) = nth(n,t))`;

(*---------------------------------------------------------------------------
 * Iterate a function application. Notice that this forces the type of the
 * function to be ":'a ->'a".
 *---------------------------------------------------------------------------*)
val funpow_def = 
Rfunction `inv_image ^pred FST` 
   `(funpow(0, (f:'a->'a), x) = x) /\
    (funpow(SUC n, f, x) = f(funpow(n,f,x)))`;


(*---------------------------------------------------------------------------
 * This lemma is needed in the proof below. An automated induction system
 * would have to discover this and prove it on the fly. Written more
 * elegantly in curried form, we'd have
 * 
 *   funpow n f o f = f o funpow n f
 *---------------------------------------------------------------------------*)
val funpow_law = Q.store_thm("funpow_law",
`!n f (l:'a list). funpow (n, f, f l) = f (funpow (n, f, l))`,
PROGRAM_TAC{induction = #induction funpow_def, rules = #rules funpow_def}
  THENL [REFL_TAC, ASM_RW_TAC[]]);

(*---------------------------------------------------------------------------
 * A simple relationship between nth and funpow. Invoking "nth" is the
 * same as taking the tail of the list "n" times and then returning the head
 * of the resulting list. The proof goes by induction on the definition of 
 * nth. 
 *---------------------------------------------------------------------------*)
val nth_funpow_thm = Q.store_thm("nth_funpow_thm",
`!n (L:'a list). n < LENGTH L ==> (nth(n,L) = HD(funpow(n,TL,L)))`,
REC_INDUCT_TAC (#induction nth_def)
   THEN RW_TAC[HD, LENGTH, NOT_LESS_0, LESS_0, LESS_MONO_EQ,
               #rules funpow_def, #rules nth_def]
   THEN REPEAT STRIP_TAC THEN RES_TAC THEN ASM_RW_TAC[]
   THEN RW_TAC[GSYM funpow_law,TL]);

(*---------------------------------------------------------------------------
 * Note. This is not the only way to prove this. Iterated induction
 * on the structure of the data also works. However, one loses the
 * connection with the definition of the function, and hence the 
 * possibilities for automation.
 *
  INDUCT_TAC THEN INDUCT_THEN (theorem"list" "list_INDUCT") MP_TAC
     THEN RW_TAC[HD, LENGTH, NOT_LESS_0, LESS_0, LESS_MONO_EQ,
                 #rules funpow_def, #rules nth_def]
     THEN REPEAT STRIP_TAC THEN RES_TAC THEN ASM_RW_TAC[]
     THEN RW_TAC[GSYM funpow_law,TL];
 *
 *---------------------------------------------------------------------------*)


val mem_nth = Q.store_thm("mem_nth",
`!n (l:'a list). n < LENGTH l ==> mem (nth(n,l)) l`,
PROG_TAC{induction = #induction nth_def, rules = #rules nth_def}
 THEN REPEAT (POP_ASSUM MP_TAC)
 THEN RW_TAC[mem_def,LENGTH, LESS_MONO_EQ]
 THEN ARITH_TAC);

html_theory"-";
export_theory();
