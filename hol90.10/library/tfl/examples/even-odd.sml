(*----------------------------------------------------------------------------
 *
 *            Mutual recursion : even and odd
 *
 * This isn't such an interesting example, since the induction theorems 
 * obtained are just standard mathematical induction!
 *---------------------------------------------------------------------------*)

new_theory"even_odd";


local open Hol_datatype
in
  val tag_info = hol_datatype `tag = Even of num | Odd of num`;
end;


val tag_size_def = Q.new_definition("tag_size", `tag_size = tag_case I I`);

val EO = Rfunction`measure tag_size`
            `(EO(Even 0) = T)              /\
             (EO(Even(SUC x)) = EO(Odd x)) /\
             (EO(Odd 0) = F)               /\
             (EO(Odd(SUC x)) = EO(Even x))`;

val EOterminates = 
prove_termination EO (RW_TAC[tag_size_def, theorem"combin" "I_THM",
                             theorem"prim_rec" "LESS_SUC_REFL"]);

val even_def = define Prefix `even n = EO(Even n)`;
val odd_def  = define Prefix `odd n  = EO(Odd n)`;

(*---------------------------------------------------------------------------
 *  |- (even 0 = T) /\
 *    (!x. even (SUC x) = odd x) /\
 *     (odd 0 = F) /\
 *     (!x. odd (SUC x) = even x) : thm
 *---------------------------------------------------------------------------*)
val (even_odd_rules as [even0,evenSUC,odd0,oddSUC]) = 
map GEN_ALL 
  (CONJUNCTS (RW_RULE[EOterminates, GSYM even_def, GSYM odd_def] (#rules EO)));

val even_unroll0 = GEN_ALL(PURE_RW_RULE[odd0] (Q.SPEC`0` evenSUC));
val even_unrollSUC = GEN_ALL(RW_RULE[oddSUC] (Q.SPEC`SUC x` evenSUC))
val evens = LIST_CONJ[even0,even_unroll0,even_unrollSUC];

val odd_unroll0 = GEN_ALL(PURE_RW_RULE[even0] (Q.SPEC`0` oddSUC));
val odd_unrollSUC = GEN_ALL(RW_RULE[evenSUC] (Q.SPEC`SUC x` oddSUC))
val odds = LIST_CONJ[odd0,odd_unroll0,odd_unrollSUC];


val base = Q.SPEC`tag_case (P1:num->bool) Q1` 
                (RW_RULE[EOterminates] (DISCH_ALL(#induction EO)));

val even_th = GEN_ALL
               (RW_RULE[](DISCH_ALL(Q.GEN`x` (Q.SPEC`Even x`(UNDISCH base)))));


local val CH = Q.TAUT_CONV`x/\y==>z = x==>y==>z`
      val CH' = Q.TAUT_CONV`x==>y==>z = y/\x==>z`
in 
val ind_thm  = GEN_ALL
  (RW_RULE[CH']
    (DISCH_ALL
      (UNDISCH_ALL 
        (RW_RULE[CH]
           (Q.SPECL[`P`,`P`] even_th)))))
end;

val odd_th = GEN_ALL
              (RW_RULE[](DISCH_ALL(Q.GEN`x` (Q.SPEC`Odd x`(UNDISCH base)))));


g`!n. odd n = ~even n`;
e (REC_INDUCT_TAC ind_thm THEN RW_TAC even_odd_rules);

(* This is better. How to derive it? *)
val prospect = 
   mk_thm([],Term`!P. P 0 
                      /\ P (SUC 0) 
                      /\ (!x. P x ==> P (SUC (SUC x))) 
                      ==> !z. P z`);
restart();
e (REC_INDUCT_TAC prospect);
e (RW_TAC[evens,odds]);


html_theory"-";
