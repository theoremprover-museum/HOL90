(*---------------------------------------------------------------------------
 * Answer to a question from Thorsten Altenkirch: does defining, e.g.,
 * "occurs" work where the recursively defined function is passed in a 
 * call to another function? For "occurs", this can be made to work, but it 
 * requires the user to prove and install a congruence theorem for the
 * function that takes "occurs" as an argument. It also requires that 
 * "occurs" is fully eta-expanded in the recursive call. TFL can probably be
 * altered to do this eta-expansion on-the-fly. Whether all higher-order 
 * functions have useful congruence rules is a good question.
 *---------------------------------------------------------------------------*)

new_theory"term" handle _ => ();
cons_path"../" theory_path;
new_parent"kls_list";


val exists_def =
#definer(assoc "list" (Hol_datatype.current()))
   {name="exists", fixity=Prefix,
    def = Term`(exists (P:'a->bool) [] = F) /\ 
               (exists P        (h::t) = P h \/ exists P t)`};


val exists_cong = Q.prove
`!L L' P P'.
    (L=L') /\ 
    (!y:'a. mem y L' ==> (P y = P' y)) 
     ==> (exists P L = exists P' L')`
(#induct_tac (assoc"list" (Hol_datatype.current()))
 THENL
 [ REPEAT GEN_TAC 
     THEN DISCH_THEN (CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM) (K ALL_TAC))
     THEN RW_TAC[exists_def],
   REPEAT STRIP_TAC THEN POP_ASSUM MP_TAC 
     THEN POP_ASSUM (SUBST_ALL_TAC o SYM) 
     THEN POP_ASSUM (ASSUME_TAC o RW_RULE[] o Q.SPEC`L`)
     THEN RW_TAC[exists_def,definition"kls_list" "mem_def",
                 Q.TAUT_CONV`(A \/ B ==> C) = (A ==> C) /\ (B ==> C)`]
     THEN CONV_TAC (DEPTH_CONV FORALL_AND_CONV)
     THEN DISCH_THEN (fn th =>
          let val [th1,th2] = CONJUNCTS th
          in MATCH_MP_TAC (Q.TAUT_CONV`(A=C) /\ (B=D) ==> (A \/ B = C \/ D)`) 
               THEN CONJ_TAC THENL
                [ (ACCEPT_TAC o RW_RULE[] o Q.SPEC`h`) th1,
                  ANTE_RES_THEN ACCEPT_TAC th2]
          end)]);

val () = Prim.Context.write (exists_cong::Prim.Context.read());


local open Hol_datatype
in
val term_ty_def = 
     hol_datatype `term = Var of 'a
                        | Const of 'a
                        | App of term => term`
end;



(*---------------------------------------------------------------------------
 * Does a variable occur in a term?
 *---------------------------------------------------------------------------*)
val Occ_def = function
        `(Occ (v1, Var v2) = ((v1:'a) = v2)) /\
         (Occ (v, Const x) = F) /\
         (Occ (v, App M N) = exists (\x. Occ(v,x)) [M;N])`;


val Occ1_def = function
     `(Occ1 (v1, Var v2) = ((v1:'a) = v2)) /\
      (Occ1 (v, Const x) = F) /\
      (Occ1 (v, App M N) = Occ1 (v,M) \/ Occ1 (v,N))`;

val mem_def = definition"kls_list" "mem_def";

g`!(x:'a) M. Occ (x,M) = Occ1 (x,M)`;
expandf (REC_INDUCT_TAC (CONJUNCT2 Occ_def) THEN 
 RW_TAC[CONJUNCT1 Occ_def, CONJUNCT1 Occ1_def,exists_def] THEN BETA_TAC
 THEN RW_TAC[mem_def,Q.TAUT_CONV`A \/ B ==> C = (A ==> C) /\ (B ==> C)`]
 THEN REPEAT GEN_TAC THEN DISCH_THEN (fn th => CONJUNCTS_THEN2 
   (MP_TAC o Q.INST[`x`|->`M:'a term`]) 
   (MP_TAC o Q.INST[`x`|->`N:'a term`]) (SPEC_ALL th))
 THEN RW_TAC[]);

(* Simpler by standard induction! *)
g`!(x:'a) M. Occ (x,M) = Occ1 (x,M)`;
expandf (REC_INDUCT_TAC (CONJUNCT2 Occ1_def) THEN 
 RW_TAC[CONJUNCT1 Occ_def, CONJUNCT1 Occ1_def,exists_def] THEN BETA_TAC
 THEN RW_TAC[]);


val pterm_def = Rfunction `Empty`
  `(pterm (M, App P Q) = (M=P) \/ (M=Q)) /\
   (pterm (M, (x:'a term)) = F)`;

define Prefix `pred_term M N = pterm(M:'a term,N)`;

val pred_term_eqns = PURE_RW_RULE[GSYM(definition"-" "pred_term")]
                           (#rules pterm_def);

val pred_term_induction = Q.GEN`P`
 (CONV_RULE (DEPTH_CONV GEN_BETA_CONV)
     (Q.SPEC`\(x,y). P x y` (#induction pterm_def)));

use"../utils.sml";
(*---------------------------------------------------------------------------
 * There is a certain regularity about these.
 *---------------------------------------------------------------------------*)

val WF_pred_term = Q.prove
`WF (pred_term:'a term -> 'a term -> bool)`
(RW_TAC[definition"WF" "WF_DEF"] THEN BETA_TAC THEN GEN_TAC 
  THEN CONV_TAC (CONTRAPOS_CONV THENC NNF_CONV) THEN 
  DISCH_TAC THEN REC_INDUCT_TAC ((#induction o #2) term_ty_def)
  THEN REPEAT CONJ_TAC 
  THEN REPEAT GEN_TAC THEN CCONTR_TAC 
  THEN POP_ASSUM (STRIP_ASSUME_TAC o RW_RULE[] o CONV_RULE NNF_CONV)
  THEN RES_THEN MP_TAC
  THEN RW_TAC[pred_term_eqns]
  THEN NNF_TAC
  THEN GEN_TAC THEN DISCH_THEN (DISJ_CASES_THEN SUBST1_TAC)
  THEN FIRST_ASSUM ACCEPT_TAC);

val Vars_def =
 Rfunction`inv_image pred_term FST`
   `(Vars (Var (x:'a), L) =  (mem x L => L | x::L)) /\
    (Vars (Const y, L) = L) /\
    (Vars (App M N, L) = Vars (M, Vars(N,L)))`;


val terminates = prove_termination Vars_def
(RW_TAC[pred_term_eqns] 
    THEN MATCH_MP_TAC(theorem "WF" "WF_inv_image")
    THEN ACCEPT_TAC WF_pred_term);

val Vars_eqns = RW_RULE[terminates] (DISCH_ALL (#rules Vars_def));
val Vars_induction = RW_RULE[terminates] (DISCH_ALL (#induction Vars_def));

g`!(v:'a) M N L. mem v (Vars (M,Vars (N,L))) 
                 ==> mem v (Vars (M,L)) \/ 
                     mem v (Vars (N,L)) \/ 
                     mem v L`;
e DONE_TAC;
val memv = top_thm();


g`!(x:'a) M. mem x (Vars(M,[])) ==> Occ(x,M)`;
expandf (REC_INDUCT_TAC (CONJUNCT2 Occ_def));
expandf(RW_TAC[Vars_eqns, CONJUNCT1 Occ_def,mem_def,exists_def] THEN BETA_TAC);
e (REPEAT STRIP_TAC);
e (IMP_RES_TAC memv);
(*1*)
e (RULE_ASSUM_TAC (fn th => RW_RULE[] (Q.SPEC`M` th) handle _ => th));
e (ASM_RW_TAC[]);
(*2*)
e (RULE_ASSUM_TAC (fn th => RW_RULE[] (Q.SPEC`N` th) handle _ => th));
e (ASM_RW_TAC[]);
(*3*)
e (POP_ASSUM MP_TAC THEN RW_TAC[mem_def]);


g`!(x:'a) M. mem x (Vars(M,[])) ==> Occ(x,M)`;
e (GEN_TAC THEN REC_INDUCT_TAC ((#induction o #2) term_ty_def));
expandf (RW_TAC[Vars_eqns,mem_def,CONJUNCT1 Occ_def]);
e (RW_TAC[exists_def] THEN BETA_TAC);
e (REPEAT STRIP_TAC);
e (IMP_RES_TAC memv THEN ASM_RW_TAC[] 
   THEN POP_ASSUM MP_TAC THEN RW_TAC[mem_def]);


(*---------------------------------------------------------------------------
open Rewrite;
load_library_in_place(find_library"nested_rec");

local
(* val prodAxiom = #axiom (assoc "prod" (Hol_datatype.current())) *)
structure FOT : NestedRecTypeInputSig = 
struct
  structure DefTypeInfo = DefTypeInfo
  open DefTypeInfo
    (* fo_term = Var of 'a
               | Const of num 
               | App of fo_term => fo_term list
     *)
                
  val def_type_spec =
    [{type_name = "FOT",
      constructors =
        [{name = "Var",   arg_info = [existing (Type`:'a`)]},
         {name = "Const", arg_info = [existing (Type`:num`)]},
         {name = "App",   arg_info = 
          [being_defined "FOT",
           type_op{Tyop="list", Args = [being_defined "FOT"]}]}
        ]}]
  val recursor_thms = [theorem "list" "list_Axiom" (*, prodAxiom *)]
  val New_Ty_Existence_Thm_Name = "FOT_existence"
  val New_Ty_Induct_Thm_Name = "FOT_induct"
  val New_Ty_Uniqueness_Thm_Name = "FOT_unique"
  val Constructors_Distinct_Thm_Name = "FOT_distinct"
  val Constructors_One_One_Thm_Name = "FOT_one_one"
  val Cases_Thm_Name = "FOT_cases"
end
in
    structure FOT = NestedRecTypeFunc (FOT)
end;

val FOT_CASES = Q.prove
`!t. (?y. t = Var y) \/ (?n. t = Const n) \/ ?f l. t = App f l`
(GEN_TAC THEN STRIP_ASSUME_TAC(Q.SPEC`t` (CONJUNCT1 FOT_cases))
 THEN POP_ASSUM SUBST_ALL_TAC THENL
 [DISJ1_TAC THEN Q.EXISTS_TAC`y` THEN RW_TAC[],
  DISJ2_TAC THEN DISJ1_TAC THEN Q.EXISTS_TAC`y` THEN RW_TAC[],
  DISJ2_TAC THEN DISJ2_TAC THEN MAP_EVERY Q.EXISTS_TAC[`y`,`y'`] THEN REFL_TAC]
);

val FOT_DISTINCT = CONJUNCT1 FOT_distinct;

try define_mutual_functions
 {name = "case_fot",fixities = NONE,
  rec_axiom = FOT_existence,
  def = Term`(case_fot f1 f2 f3 (Var x)   = f1 x) /\
             (case_fot f1 f2 f3 (Const y) = f2 y) /\
             (case_fot f1 f2 f3 (App c l) = f3 c l)`};

*)

