signature Prim_sig =
 sig
  type term
  type thm
  type tactic
    structure Rules : Rules_sig
    structure Thms  : Thms_sig
    structure Thry  : Thry_sig
    structure USyntax : USyntax_sig
    structure Context : sig val read : unit -> thm list
                            val write: thm list -> unit end

   datatype pattern = GIVEN of term * int
                    | OMITTED of term * int

   val mk_functional : term -> {functional:term, pats: pattern list}

   val prim_wfrec_definition : {R:term, functional:term}
                                -> {def:thm, corollary:thm}

   val gen_wfrec_definition : {R:term, eqs:term}
                               -> {rules:thm, 
                                   TCs: term list list,
                                   full_pats_TCs: (term * term list) list,
                                   patterns :pattern list}

   val wfrec_eqns : term -> {WFR : term, 
                             proto_def : term,
                             extracta  : (thm * term list) list,
                             pats  : pattern list}

   val lazyR_def : term -> {rules:thm,
                            R : term,
                            full_pats_TCs:(term * term list) list, 
                            patterns: pattern list}

   val mk_induction : term -> term -> (term * term list) list -> thm

   val postprocess: {WFtac:tactic, terminator:tactic, simplifier:term -> thm}
                      -> {rules:thm, induction:thm, TCs:term list list}
                         -> {rules:thm, induction:thm, nested_tcs:thm list}

   val termination_goals : thm -> term list
 end
   

local 
open Exception Lib CoreHol Parse;
open Type Term Dsyntax Theory Thm Drule Conv Let_conv Resolve;
open Tactical Tactic Const_def; 
infix THEN; infix ORELSE;
open RW;

val output = Portable.output
val std_out = Portable.std_out
val flush_out = Portable.flush_out

val LET_DEF = boolThry.LET_DEF;

(*---------------------------------------------------------------------------
 *      Link system. 
 *---------------------------------------------------------------------------*)

val COND_CONG = prove(
--`!P P' (x:'a) x' y y'.
      (P = P') /\ (P'  ==> (x = x')) /\ 
                  (~P' ==> (y = y'))
      ==> ((P => x | y) = (P' => x' | y'))`--,
 REPEAT STRIP_TAC THEN 
 REPEAT COND_CASES_TAC THEN 
 REPEAT RES_TAC);


val LET_CONG = prove(
--`!f (g:'a->'b) M M'. 
   (M = M') /\ 
   (!x:'a. (x = M') ==> (f x = g x)) 
   ==> 
  (LET f M = LET g M')`--,
REPEAT STRIP_TAC 
 THEN RW.RW_TAC[LET_DEF] 
 THEN BETA_TAC 
 THEN RES_TAC 
 THEN RW.ASM_RW_TAC[]);


val WIMP_CONG = prove(
--`!x y y'. (x=x) /\ 
            (x ==> (y = y')) 
            ==> 
            (x ==> y = x ==> y')`--,
REPEAT GEN_TAC 
 THEN ASM_CASES_TAC(--`x:bool`--) 
 THEN RW.ASM_RW_TAC[]);


val IMP_CONG = prove(
--`!x x' y y'. (x=x') /\ 
               (x' ==> (y = y')) 
               ==> 
               (x ==> y = x' ==> y')`--,
REPEAT GEN_TAC 
 THEN BOOL_CASES_TAC(--`x':bool`--) 
 THEN BOOL_CASES_TAC(--`x:bool`--) 
 THEN RW.RW_TAC[]); 

val _ = RW.Implicit.add_congs [IMP_CONG,COND_CONG];

(*---------------------------------------------------------------------------
 * Install prettyprinter for rewrite rule sets.
 *---------------------------------------------------------------------------*)
(* val _ = PP.install_pp ["RW","simpls"] "" RW.pp_simpls; *)

structure Tfl = TFL(structure Rules = Rules 
                    structure Thms  = Thms
                    structure Thry  = Thry)
in
structure TflLib 
 :sig
  type term
  type thm
  type tactic

   structure Prim : Prim_sig
   val current_congs : unit -> thm list

   val rfunction  
    : ({induction:thm, rules:thm, TCs:term list list} 
        -> {induction:thm, rules:thm, nested_tcs:thm list})
            -> (thm list -> thm -> thm)
                 -> term frag list -> term frag list 
                     -> {induction:thm, rules:thm, tcs:term list}

   val Rfunction  : term frag list 
                     -> term frag list 
                       -> {induction:thm, rules:thm, tcs:term list}

   val lazyR_def : term frag list -> thm
   val function : term frag list -> thm

   val WF_TAC : thm list -> tactic
   val tc_simplifier : thm list -> term -> thm
   val terminator : tactic
   val std_postprocessor : {induction:thm, rules:thm, TCs:term list list} 
                           -> {induction:thm, rules:thm, nested_tcs:thm list}

   val REC_INDUCT_TAC : thm -> tactic
   val PROGRAM_TAC : {induction: thm, rules : thm} -> tactic
   val PROG_TAC : {induction: thm, rules : thm} -> tactic

   val tgoal : {induction:thm,rules:thm,tcs:term list} -> Goalstack.proofs
   val prove_termination : {induction:thm,rules:thm,tcs:term list}
                            -> tactic -> thm

   (* Miscellaneous junk *)
   val pred : term
   val list_pred : term
   val define : fixity -> term frag list -> thm
   val timing : bool ref
   val CASES_TAC : tactic
  end = 
struct

 type term = CoreHol.Term.term
 type thm =  CoreHol.Thm.thm
 type tactic = Abbrev.tactic

structure Prim =
 struct
   type term = CoreHol.Term.term
   type thm =  CoreHol.Thm.thm
   type tactic = Abbrev.tactic

    open Tfl 

    val mk_functional = mk_functional "-"
    val wfrec_eqns = wfrec_eqns "-"
    val  prim_wfrec_definition = fn r =>
        let val {corollary,def,theory} = prim_wfrec_definition"-" r
        in {def=def, corollary=corollary}
        end
    val gen_wfrec_definition = fn r =>
        let val {rules,theory,
                 full_pats_TCs,TCs,patterns} = gen_wfrec_definition"-" r
        in {rules=rules, TCs=TCs,full_pats_TCs=full_pats_TCs,patterns=patterns}
        end
    val lazyR_def = fn r =>
        let val {rules,full_pats_TCs, R, patterns,...} = lazyR_def"-" r
        in {rules=rules, full_pats_TCs=full_pats_TCs, R=R, patterns=patterns}
        end
    val mk_induction = mk_induction"-"
    val postprocess = fn pp => postprocess pp "-"
    val termination_goals = termination_goals
 end (* Prim *)

val timing = ref false;

structure Arith = arithLib.Arith;   (* Dependence on the arith library *)

fun TFL_LIB_ERR{func,mesg} = 
     HOL_ERR{origin_structure="HOL_Tfl",origin_function=func,message=mesg};

 (*---------------------------------------------------------------------------
  * The current notion of context used by Tfl. Context is represented via
  * congruence rules. This is extensible.
  *--------------------------------------------------------------------------*)
 fun current_congs() = Prim.Context.read()@(#case_congs(Thry.extract_info"-"));

fun func_of_cond_eqn tm =
      #1(strip_comb(#lhs(dest_eq(#2 (strip_forall(#2(strip_imp tm)))))));

fun timer s1 f s2 =
   let open Portable.Timer
       open Portable.Time
   in if !timing 
      then (output(std_out, s1); 
            flush_out std_out;
            let val start = startRealTimer ()
                val x = f()
            in output(std_out,time_to_string(checkRealTimer start));
               output(std_out, "\n");
               output(std_out, s2); flush_out std_out;
               x
            end)
       else f()
   end;

(*---------------------------------------------------------------------------
 * Constrain parsed term to have a given type.
 *---------------------------------------------------------------------------*)
fun ptm_with_ty qtm ty = 
   let fun trail s = [QUOTE (s^"):"), ANTIQUOTE(ty_antiq ty), QUOTE""]
   in
   Parse.term_parser
      (case (Lib.front_last qtm)
       of ([],QUOTE s) => trail ("("^s)
        | (QUOTE s::rst, QUOTE s') => (QUOTE ("("^s)::rst) @ trail s'
        | _ => raise TFL_LIB_ERR{func="ptm_with_ty",mesg="badly formed quote"})
   end;

 (*---------------------------------------------------------------------------
  * "rfunction" is one of the main entrypoints to the definition mechanisms. 
  * "rfunction" is not for normal use, only for when "Rfunction" is not
  * satisfactory. "rfunction" is parameterized by a postprocessor and yet
  * another simplifier ("reducer"). This reducer attempts to eliminate 
  * (or simplify, when that's not possible) solved termination conditions, 
  * in the definition and induction theorems. This reducer is only invoked
  * on the results of defining a nested recursion. 
  *--------------------------------------------------------------------------*)
 local infixr 5 -->
    fun (ty1 --> ty2) = mk_type{Tyop="fun",Args=[ty1,ty2]}
    fun id_thm th = 
       let val {lhs,rhs} = dest_eq(#2(strip_forall(concl th)))
       in aconv lhs rhs
       end handle _ => false
    val solved = not o can dest_eq o #2 o strip_forall o concl
    fun join_assums th = 
       let val {lhs,rhs} = dest_eq(#2 (strip_forall (concl th)))
           val cntxtl = (#1 o strip_imp) lhs  (* cntxtl should be cntxtr *)
           val cntxtr = (#1 o strip_imp) rhs  (* but this way is solider *)
           val cntxt = op_union aconv cntxtl cntxtr
       in 
       GEN_ALL(DISCH_ALL(Rewrite.REWRITE_RULE(map ASSUME cntxt) (SPEC_ALL th)))
       end
    val gen_all = USyntax.gen_all
 in
 fun rfunction pp reducer QR Qeqns =
  let val eqs = Parse.term_parser Qeqns
      val argty = type_of(rand(lhs(hd(strip_conj eqs))))
      val R = ptm_with_ty QR (argty --> argty --> Dsyntax.bool)
      fun def() = 
         let val {rules,full_pats_TCs, TCs,...} = timer"making definition.\n"
                    (fn () => Prim.gen_wfrec_definition{R=R, eqs=eqs})
                    "Finished making definition.\n"
             val f = func_of_cond_eqn(concl(CONJUNCT1 rules handle _ => rules))
             val {induction,rules,nested_tcs} = 
                         pp{rules = rules, 
                        induction = timer "starting induction proof\n"
                                 (fn () => Prim.mk_induction f R full_pats_TCs)
                                     "finished induction proof\n",
                              TCs = TCs}
             val normal_tcs = Prim.termination_goals rules
         in case nested_tcs 
            of [] => {induction=induction, rules=rules, tcs=normal_tcs}
             | _  => let val (solved,simplified,stubborn) =
                          itlist (fn th => fn (So,Si,St) =>
                                  if (id_thm th) then (So, Si, th::St) else
                                  if (solved th) then (th::So, Si, St) 
                                  else (So, th::Si, St)) nested_tcs ([],[],[])
                         val simplified' = map join_assums simplified
                   in
                   {induction = reducer (solved@simplified') induction,
                        rules = reducer (solved@simplified') rules,
                          tcs = normal_tcs @
                                map (gen_all o rhs o #2 o strip_forall o concl)
                                    (simplified@stubborn)}
                   end
         end
  in Theory.perform_atomic_theory_op def
  end
  handle (e as Utils.ERR _) => Utils.Raise e
       |     e              => Raise e

 end;

 (*---------------------------------------------------------------------------
  * Trivial wellfoundedness prover for combinations of wellfounded relations.
  *--------------------------------------------------------------------------*)
 fun BC_TAC th = 
   if (is_imp (#2 (Dsyntax.strip_forall (concl th))))
   then MATCH_ACCEPT_TAC th ORELSE MATCH_MP_TAC th
   else MATCH_ACCEPT_TAC th;

 val WFthms =  map (theorem"WF")
                  ["WF_measure",   "WF_LESS",  "WF_PRED", "WF_LIST_PRED",
                   "WF_inv_image", "WF_RPROD", "WF_X", "WF_TC", "WF_Empty"]
 fun WF_TAC thms = REPEAT (MAP_FIRST BC_TAC (thms@WFthms) ORELSE CONJ_TAC)


 (*---------------------------------------------------------------------------
  * Simplifier for termination conditions. 
  *--------------------------------------------------------------------------*)
 val WFsimpl_thms = map (definition"WF") 
                        ["measure_def","inv_image_def","RPROD_DEF", "X_DEF"];
 val simpls = WFsimpl_thms@[definition"combin""o_DEF",theorem "combin" "I_THM"]

 fun tc_simplifier thl = Rules.simpl_conv (thl@simpls);


 (*--------------------------------------------------------------------------
  * A prover for termination conditions. This gets called after the
  * simplifier has simplified the conditions. 
  *--------------------------------------------------------------------------*)
 val terminator = CONV_TAC Arith.ARITH_CONV;


 (* Combination of these tools. *)
 val std_postprocessor = Prim.postprocess{WFtac = WF_TAC[],
                                     terminator = terminator, 
                                     simplifier = tc_simplifier[]};


 (*---------------------------------------------------------------------------
  * Takes a termination relation and a conjunction of recursion equations, 
  * and makes the definition, extracts termination conditions, attempts to 
  * solve them, and then derives recursion induction. Any remaining termination
  * conditions are also made available.
  *--------------------------------------------------------------------------*)
 val Rfunction = 
    let open RW
    in rfunction std_postprocessor
       (fn thl => 
          REWRITE_RULE Fully (Simpls(std_simpls, thl),
                              Context([],DONT_ADD), 
                              Congs (IMP_CONG::current_congs()), 
                              Solver std_solver))
    end


 (*---------------------------------------------------------------------------
  * Takes a conjunction of recursion equations. Nested recursions are not
  * accepted. The definition of the function is then made, and termination 
  * conditions are extracted. Its name comes from the fact that a 
  * termination relation doesn't need to be given; however, one will later 
  * have to be given in order to eliminate the termination conditions.
  *--------------------------------------------------------------------------*)
 fun lazyR_def qtm = 
      Theory.perform_atomic_theory_op 
              (fn () => #rules(Prim.lazyR_def (Parse.term_parser qtm)))
      handle (e as Utils.ERR _) => Utils.Raise e
           |     e              => Raise e;
 

 (*---------------------------------------------------------------------------
  * Takes a conjunction of recursion equations, and makes the definition,
  * extracts termination conditions, and then derives recursion induction.
  * Termination conditions are all put on the assumptions.
  *--------------------------------------------------------------------------*)
 fun function qtm = 
   let fun def() =
    let val {rules,R,full_pats_TCs,...} = timer"Making definition.\n"
                               (fn () => Prim.lazyR_def(Parse.term_parser qtm))
                               "Finished definition.\n"
        val f = func_of_cond_eqn (concl(CONJUNCT1 rules handle _ => rules))
        val induction = timer "Starting induction proof.\n"
                              (fn () => Prim.mk_induction f R full_pats_TCs)
                              "Finished induction proof.\n"
    in CONJ rules induction
    end
   in Theory.perform_atomic_theory_op def
   end
   handle (e as Utils.ERR _) => Utils.Raise e
        |     e              => Raise e;


(*---------------------------------------------------------------------------
 * A simple recursion induction tactic. See the "examples" directory for 
 * examples of its use.
 *---------------------------------------------------------------------------*)
fun REC_INDUCT_TAC thm =
  let val {Bvar=prop,Body} = dest_forall(concl thm)
      val parg_ty = hd(#Args(dest_type(type_of prop)))
      val n = (length o #1 o strip_forall o #2 o strip_imp) Body
      fun ndest_forall trm = 
          let fun dest (0,tm,V) = (rev V,tm)
                | dest (n,tm,V) = let val {Bvar,Body} = dest_forall tm
                                  in dest(n-1,Body, Bvar::V) end
          in dest(n,trm,[])
          end
      fun tac (asl,w) =
       let val (V,body) = ndest_forall w
           val P = mk_pabs{varstruct = USyntax.mk_vstruct parg_ty V, body=body}
                            handle _ => mk_abs{Bvar = hd V, Body=body}
           val thm' = CONV_RULE(DEPTH_CONV GEN_BETA_CONV) (ISPEC P thm)
       in MATCH_MP_TAC thm' (asl,w)
       end
       handle _ => raise Utils.ERR{module = "HOL_Tfl",
                                   func = "REC_INDUCT_TAC",
                                   mesg = "Unanticipated term structure"}
  in tac
  end;


 (*---------------------------------------------------------------------------
  * This should actually be a "safe" STRIP_TAC, where negations are not
  * treated as implications.
  *--------------------------------------------------------------------------*)
 val SAFE_DISCH_TAC = 
     Utils.W(fn (asl,w) => if (is_neg w) then NO_TAC else DISCH_TAC);

(*---------------------------------------------------------------------------
 * A naive but useful program tactic.
 *---------------------------------------------------------------------------*)
 fun PROGRAM_TAC{induction, rules} = 
    REC_INDUCT_TAC induction 
     THEN REPEAT CONJ_TAC 
     THEN REPEAT GEN_TAC 
     THEN REPEAT SAFE_DISCH_TAC 
     THEN RW.ONCE_RW_TAC[rules]
     THEN REPEAT COND_CASES_TAC;

local 
(*---------------------------------------------------------------------------
 * "DTHEN" differs from standard DISCH_THEN in that it doesn't treat negation 
 * as implication into falsity.
 *---------------------------------------------------------------------------*)
     exception FOO;
     fun DTHEN (ttac:Abbrev.thm_tactic) :tactic = fn (asl,w) =>
       if (is_neg w) then raise FOO
       else let val {ant,conseq} = Dsyntax.dest_imp w 
                val (gl,prf) = ttac (Thm.ASSUME ant) (asl,conseq) 
            in (gl, Thm.DISCH ant o prf)
            end
     val STRIP_TAC = Tactical.FIRST[GEN_TAC,CONJ_TAC,DTHEN STRIP_ASSUME_TAC]
     open RW
     fun ROTAC thl= REWRITE_TAC Once (Pure thl,Context([],DONT_ADD), 
                                      Congs[],Solver always_fails)
     val RWTAC = REWRITE_TAC Fully (Simpls(std_simpls,[]),
                                    Context([],DONT_ADD),
                                    Congs[],Solver always_fails)
in
fun PROG_TAC{induction, rules} = 
   REC_INDUCT_TAC induction 
    THEN REPEAT CONJ_TAC 
    THEN REPEAT GEN_TAC 
    THEN ROTAC[rules]
    THEN REPEAT COND_CASES_TAC 
    THEN RWTAC
    THEN REPEAT STRIP_TAC
end;


 fun list_to_goal L = ([],list_mk_conj L);

 (*---------------------------------------------------------------------------
  * Takes the termination conditions from, e.g., the output of Rfunction 
  * and puts them into a goal stack.
  *--------------------------------------------------------------------------*)
 fun tgoal{tcs,induction,rules} = 
        (Goalstack.Implicit.set_goal o list_to_goal) tcs


 (*---------------------------------------------------------------------------
  * Applies a tactic to the termination conditions arising, e.g., from an
  * invocation of Rfunction.
  *--------------------------------------------------------------------------*)
 fun prove_termination{tcs,induction,rules} tac =
     TAC_PROOF(list_to_goal tcs,tac);


 (*---------------------------------------------------------------------------
  * Install basic notions of context. In TFL, new notions of context come 
  * automatically from datatype definitions, via case-definitions and their
  * associated congruence rules, but the user can also add their own 
  * context notions by invoking "Prim.Context.write", which takes a list
  * of congruence rules and adds them to the data that Tfl uses when
  * processing a definition.
  *--------------------------------------------------------------------------*)
 val () = Prim.Context.write[Thms.LET_CONG, Thms.COND_CONG];


 (* Common wellfounded relations. *)
 val pred = Parse.term_parser`\m n. n = SUC m`;
 val list_pred = Parse.term_parser`\L1 L2. ?h:'a. L2 = CONS h L1`;


(*---------------------------------------------------------------------------
 * A preliminary attempt to have a single entrypoint for definitions. Assumes 
 * that recursive definitions are over the first argument (Melham's package 
 * is smarter and this one should be too). This is totally ad hoc, and needs
 * to be integrated with the TFL definition principles.
 *---------------------------------------------------------------------------*)
local fun basic_defn (fname,tm) =
        let fun D Prefix    = new_definition(fname,tm)
              | D (Infix i) = new_infix_definition(fname,tm,i)
              | D Binder    = new_binder_definition(fname,tm)
        in D 
        end
in
fun define fixity qtm =
 let val tm = Parse.term_parser qtm
     val f = (#1 o strip_comb o lhs o #2 o strip_forall o hd o strip_conj) tm
     val {Name,Ty} = dest_var f
 in case (dest_type (type_of f))
    of {Tyop="fun", Args=[dom,_]} =>
       (case (Lib.assoc1 (#Tyop(dest_type dom)) 
                         (Hol_datatype.current()))
        of SOME(_,{definer,...}) 
            => (definer{name=Name, fixity=fixity, def=tm}
                handle _ => basic_defn (Name,tm) fixity)
         | NONE => basic_defn (Name,tm) fixity)
    | _ => basic_defn (Name,tm) fixity
 end
end;

val CASES_TAC = Hol_datatype.CASES_TAC;

end end;
