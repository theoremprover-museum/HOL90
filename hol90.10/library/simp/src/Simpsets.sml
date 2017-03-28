structure Simpsets : Simpsets_sig =
struct

open liteLib ho_matchLib;
open Lib CoreHol;
open Thm Theory Drule Conv Let_conv Taut_thms Rec_type_support Parse
Drule Psyntax LiteLib Traverse Theorems Equal Simplifier Cond_rewr Ho_rewrite;
infix |> THENQC;

val _ = say "Making system simpsets...\n";

(* ---------------------------------------------------------------------
 * bool_ss
 *   This is essentially the same as the old REWRITE_TAC []
 *   with the "basic rewrites" plus:
 *      - ABS_SIMP removed in favour of BETA_CONV
 *      - COND_ID added: (P => Q | Q) = Q
 *      - contextual rewrites for P ==> Q and P => T1 | T2 added
 *   The convs and "basic rewrites" come from BOOL_ss, while the
 *   contextual rewrites are found in CONG_ss.  This split is done so
 *   that the potential inefficient context gathering required for the
 *   congruence reasoning can be omitted in a custom simpset built from
 *   BOOL_ss.
 * --------------------------------------------------------------------*)

fun BETA_CONVS tm = (RATOR_CONV BETA_CONVS THENQC BETA_CONV) tm

fun comb_ETA_CONV t =
    (if (not (is_exists t orelse is_forall t orelse is_select t)) then
         RAND_CONV ETA_CONV
     else NO_CONV) t

val BOOL_ss = SIMPSET
  {convs=[{name="BETA_CONV (beta reduction)",
           trace=2,
           key=SOME ([],(--`(\x:'a. y:'b) z`--)),
	   conv=K (K BETA_CONV)},
	  {name = "let_CONV (reduction of let terms)",
	   trace = 2,
	   key = SOME ([], (--`$LET (f:'a->'b) x`--)),
	   conv = K (K let_CONV)},
          {name = "ETA_CONV (eta reduction)",
           trace = 2,
           key = SOME ([],
                       --`(f:('a->'b)->'c) (\x:'a. (g:'a->'b) x)`--),
           conv = K (K comb_ETA_CONV)},
          {name = "ETA_CONV (eta reduction)",
           trace = 2,
           key = SOME ([], --`\x:'a. \y:'b. (f:'a->'b->'c) x y`--),
           conv = K (K (ABS_CONV ETA_CONV))}],
   rewrs=[REFL_CLAUSE,  EQ_CLAUSES,
          NOT_CLAUSES,  AND_CLAUSES,
          OR_CLAUSES,   IMP_CLAUSES,
          COND_CLAUSES, FORALL_SIMP,
          EXISTS_SIMP,  COND_ID,
          EXISTS_REFL, GSYM EXISTS_REFL,
          EXISTS_UNIQUE_REFL, GSYM EXISTS_UNIQUE_REFL,
          COND_BOOL_CLAUSES,
          EXCLUDED_MIDDLE,
          ONCE_REWRITE_RULE [DISJ_SYM] EXCLUDED_MIDDLE,
          SELECT_REFL, Theorems.SELECT_REFL_2],
   congs = [], filter = SOME mk_cond_rewrs, ac = [], dprocs = []};

val CONG_ss = SIMPSET
  {convs = [], rewrs = [],
   congs = [IMP_CONG, COND_CONG],
   filter=NONE, ac=[], dprocs=[]};

(*------------------------------------------------------------------------
 * PAIR_ss
 *------------------------------------------------------------------------*)

val PAIR_ss =SIMPSET
  {convs=[{name="GEN_BETA_CONV (beta reduction)",
           trace=2,
           key=SOME ([],(--`(\(x,y):('a # 'b). y:'b) (z,w)`--)),
           conv=K (K GEN_BETA_CONV)}],
   rewrs=[theorem "pair" "FST", theorem "pair" "SND",
	  theorem "pair" "PAIR",
	  theorem "pair" "PAIR_EQ"],
   filter=NONE,ac=[],dprocs=[],congs=[]};


(*------------------------------------------------------------------------
 * UNWIND_ss
 *------------------------------------------------------------------------*)

val UNWIND_ss = SIMPSET
  {convs=[{name="UNWIND_EXISTS_CONV",
           trace=1,
           key=SOME ([],(--`?x:'a. P`--)),
           conv=K (K Unwind.UNWIND_EXISTS_CONV)},
          {name="UNWIND_FORALL_CONV",
           trace=1,
           key=SOME ([],(--`!x:'a. P`--)),
           conv=K (K Unwind.UNWIND_FORALL_CONV)}],
   rewrs=[],filter=NONE,ac=[],dprocs=[],congs=[]};

(* ---------------------------------------------------------------------
 * NOT_ss
 *
 * Moving negations inwards, eliminate disjuncts incolving negations,
 * eliminate negations on either side of equalities.
 * --------------------------------------------------------------------*)

val NOT_ss = rewrites [NOT_IMP, DE_MORGAN_THM,
                       NOT_FORALL_THM, NOT_EXISTS_THM,
                       TAUT(--`(~p = ~q) = (p = q)`--)];

(* ---------------------------------------------------------------------
 * combin_ss
 * --------------------------------------------------------------------*)

val COMBIN_ss = rewrites (map (theorem "combin")
                  ["I_THM","I_o_ID", "K_THM", "S_THM", "o_ASSOC", "o_THM"]);

fun THM thy s = theorem thy s handle _ => definition thy s;
fun okthy str = mem str (ancestry "-")

val MAP_EQ_NIL = prove(
  (--`!(l:'a list) (f:'a->'b). (MAP f l = []) = (l = [])`--),
  INDUCT_THEN (theorem "list" "list_INDUCT") ASSUME_TAC THEN
  REWRITE_TAC [definition "list" "MAP", theorem "list" "NOT_CONS_NIL"]);

val quant_CONV = RAND_CONV o ABS_CONV
val lhs_CONV   = RATOR_CONV o RAND_CONV
val gMAP_EQ_NIL =
  CONV_RULE (quant_CONV (quant_CONV (lhs_CONV (REWR_CONV EQ_SYM_EQ))))
            MAP_EQ_NIL;

val APP_NIL = prove(
  (--`!(l:'a list). APPEND l [] = l`--),
  INDUCT_THEN (theorem "list" "list_INDUCT") ASSUME_TAC THEN
  ASM_REWRITE_TAC [definition "list" "APPEND"]);

val LIST_ss = rewrites (
  map (THM "list") [
        "APPEND", "EL", "EVERY_DEF", "FLAT", "HD", "LENGTH", "MAP",
        "MAP2", "NULL_DEF", "SUM", "TL", "APPEND_ASSOC", "CONS",
        "CONS_11", "LENGTH_APPEND", "LENGTH_MAP", "MAP_APPEND",
        "NOT_CONS_NIL", "NOT_NIL_CONS"] @
  (if (okthy "List") then
     map (THM "List") [
        "SNOC", "BUTLAST", "LAST", "REVERSE", "MAP_FLAT",
        "MAP_FILTER", "MAP_SNOC", "FLAT_REVERSE", "FLAT_APPEND",
        "FILTER", "SUM", "FOLDR", "FOLDL", "ELL", "ALL_EL", "SOME_EL",
        "IS_EL", "UNZIP", "IS_PREFIX", "IS_SUFFIX", "REPLICATE", "SEG",
        "SEG_REVERSE", "SEG_SNOC", "FIRSTN", "LASTN", "BUTFIRSTN",
        "BUTLASTN", "ZIP", "NOT_NIL_SNOC", "NOT_SNOC_NIL", "SNOC_11",
        "ALL_EL_APPEND"
     ]
   else []) @ [MAP_EQ_NIL, gMAP_EQ_NIL, APP_NIL])


(* ---------------------------------------------------------------------
 *
 * --------------------------------------------------------------------*)

open Satisfy;

val SATISFY_REDUCER =
  let exception FACTDB of factdb;
      fun get_db e = (raise e) handle FACTDB db => db
  in REDUCER
    {initial = FACTDB ([],[]),
     apply=SATISFY_CONV o get_db o #context,
     addcontext=(fn (ctxt,thms) => FACTDB (add_facts (get_db ctxt) thms))}
  end;

val SATISFY_ss = dproc_ss SATISFY_REDUCER;

(* ---------------------------------------------------------------------
 * sum_ss
 * --------------------------------------------------------------------*)


val SUM_ss =
    let val s_axiom = theorem "sum" "sum_Axiom"
        val s_distinct = prove_constructors_distinct s_axiom
        val s_d2 = ONCE_REWRITE_RULE [EQ_SYM_EQ] s_distinct
    in rewrites (map (THM "sum") ["ISL","ISR","OUTL","OUTR","INL","INR"] @
		 [prove_constructors_one_one s_axiom, s_distinct, s_d2])
    end;


val bool_ss = mk_simpset [BOOL_ss, CONG_ss];

val _ = say "done!\n";

end (* struct *)







(* ---------------------------------------------------------------------
 * EXISTS_NORM_ss
 *
 * Moving existentials
 *    - inwards over disjunctions
 *    - outwards over conjunctions
 *    - outwards from left of implications (??? - do we want this??)
 *    - inwards into right of implications
 * --------------------------------------------------------------------*)

(*
val EXISTS_NORM_ss =
    pure_ss
    |> addrewrs [EXISTS_OR_THM,
        TRIV_AND_EXISTS_THM,
        LEFT_AND_EXISTS_THM,
        RIGHT_AND_EXISTS_THM,
        LEFT_IMP_EXISTS_THM,
        TRIV_EXISTS_IMP_THM];

val EXISTS_IN_ss =
    pure_ss
    |> addrewrs [EXISTS_OR_THM,
        LEFT_EXISTS_AND_THM,
        RIGHT_EXISTS_AND_THM,
        LEFT_EXISTS_IMP_THM,
        TRIV_EXISTS_IMP_THM,
        RIGHT_EXISTS_IMP_THM];

val EXISTS_OUT_ss =
    pure_ss
    |> addrewrs [EXISTS_OR_THM,
        LEFT_AND_EXISTS_THM,
        RIGHT_AND_EXISTS_THM,
        LEFT_IMP_EXISTS_THM,
        RIGHT_IMP_EXISTS_THM];
*)


