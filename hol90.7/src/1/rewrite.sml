(* ===================================================================== *)
(* FILE          : rewrite.sml                                           *)
(* DESCRIPTION   : The rewriting routines. Translated from hol88.        *)
(*                                                                       *)
(* AUTHOR        : (c) Larry Paulson, University of Cambridge, for hol88 *)
(* TRANSLATOR    : Konrad Slind, University of Calgary                   *)
(* DATE          : September 11, 1991                                    *)
(* ===================================================================== *)


structure Rewrite :Rewrite_sig =
struct
structure Base_logic = Base_logic

open Base_logic;
open Term_io.Parse;

fun REWRITE_ERR{function,message} = 
        HOL_ERR{origin_structure = "Rewrite",
                origin_function = function,
                message = message}


abstype rewrites = RW of {thms :Thm.thm list,  net :conv Net.net}
with

 val empty_rewrites = RW{thms = [],  net = Net.empty_net}

 val base = ref empty_rewrites;

 local
 (* Split a theorem into a list of theorems suitable for rewriting:
  *
  *   1. Specialize all variables (SPEC_ALL).
  *
  *   2. Then do the following:
  *
  *        |- t1 /\ t2     -->    [|- t1 ; |- t2]
  *
  *   3. Then |- t --> |- t = T and |- ~t --> |- t = F
  *
  ***************************************************************)
 fun mk_rewrites th =
    let val th = Drule.SPEC_ALL th
        val t = Thm.concl th 
    in 
    if (Dsyntax.is_eq t)
    then [th]
    else if (Dsyntax.is_conj t)
         then (op @ o (mk_rewrites##mk_rewrites) o Drule.CONJ_PAIR) th
         else if (Dsyntax.is_neg t)
              then [Drule.EQF_INTRO th]
              else [Drule.EQT_INTRO th]
    end
    handle _ => raise REWRITE_ERR{function = "mk_rewrites",message = ""}

 open PP
 in
 fun add_rewrites (RW{thms,net}) thl =
    RW{thms = thms@thl,
       net = itlist Net.enter
                    (map (fn th => (Dsyntax.lhs(Thm.concl th), 
                                    Conv.REWR_CONV th))
                         (itlist (append o mk_rewrites) thl []))
                    net}

 fun pp_rewrites ppstrm (RW{thms,...}) =
    let val {add_string,add_break,begin_block,end_block,add_newline,...} = 
               with_ppstream ppstrm
        val pp_thm = Thm.pp_thm ppstrm
        val thms' = flatten (map mk_rewrites thms)
        val how_many = length thms'
    in begin_block PP.CONSISTENT 0;
       if (how_many = 0)
       then (add_string "<empty rule set>")
       else ( begin_block PP.INCONSISTENT 0;
              pr_list pp_thm (fn () => add_string";")
                             (fn () => add_break(2,0))
                             thms';
              end_block());
       add_newline();
       add_string("Number of rewrite rules = "^Lib.int_to_string how_many);
       add_newline();
       end_block()

end;

 end;


 fun set_base_rewrites rws = (base := rws);

 fun base_rewrites() = !base

 fun add_base_rewrites thl = (base := add_rewrites (base_rewrites()) thl);

 val _ = set_base_rewrites 
           (add_rewrites empty_rewrites
                         [Drule.REFL_CLAUSE,  Drule.EQ_CLAUSES,
                          Drule.NOT_CLAUSES,  Drule.AND_CLAUSES,
                          Drule.OR_CLAUSES,   Drule.IMP_CLAUSES,
                          Drule.COND_CLAUSES, Drule.FORALL_SIMP,
                          Drule.EXISTS_SIMP,  Drule.ABS_SIMP]);

(* Create a conversion from some rewrites *)
fun REWRITES_CONV (RW{net,...}) tm = Conv.FIRST_CONV (Net.lookup tm net) tm;


end; (* abstype *)


(* =====================================================================*)
(* Main rewriting conversion                         			*)
(* =====================================================================*)

fun GEN_REWRITE_CONV (rw_func:conv->conv) rws thl = 
   rw_func (REWRITES_CONV (add_rewrites rws thl));

(* ---------------------------------------------------------------------*)
(* Rewriting conversions.                        			*)
(* ---------------------------------------------------------------------*)

val PURE_REWRITE_CONV = GEN_REWRITE_CONV Conv.TOP_DEPTH_CONV empty_rewrites
and 
PURE_ONCE_REWRITE_CONV = GEN_REWRITE_CONV Conv.ONCE_DEPTH_CONV empty_rewrites;
 
fun REWRITE_CONV thl = GEN_REWRITE_CONV Conv.TOP_DEPTH_CONV 
                                        (base_rewrites()) thl
and ONCE_REWRITE_CONV thl = GEN_REWRITE_CONV Conv.ONCE_DEPTH_CONV 
                                        (base_rewrites()) thl;

(* Main rewriting rule *)
fun GEN_REWRITE_RULE f rws = Conv.CONV_RULE o GEN_REWRITE_CONV f rws;

val PURE_REWRITE_RULE = GEN_REWRITE_RULE Conv.TOP_DEPTH_CONV empty_rewrites
and 
PURE_ONCE_REWRITE_RULE = GEN_REWRITE_RULE Conv.ONCE_DEPTH_CONV empty_rewrites;

fun REWRITE_RULE thl = GEN_REWRITE_RULE Conv.TOP_DEPTH_CONV 
                                        (base_rewrites()) thl
and ONCE_REWRITE_RULE thl = GEN_REWRITE_RULE Conv.ONCE_DEPTH_CONV
                                             (base_rewrites()) thl;

(* Rewrite a theorem with the help of its assumptions *)

fun PURE_ASM_REWRITE_RULE thl th =
   PURE_REWRITE_RULE ((map Thm.ASSUME (Thm.hyp th)) @ thl) th
and 
PURE_ONCE_ASM_REWRITE_RULE thl th =
   PURE_ONCE_REWRITE_RULE ((map Thm.ASSUME (Thm.hyp th)) @ thl) th
and 
ASM_REWRITE_RULE thl th = 
   REWRITE_RULE ((map Thm.ASSUME (Thm.hyp th)) @ thl) th
and 
ONCE_ASM_REWRITE_RULE thl th = 
   ONCE_REWRITE_RULE ((map Thm.ASSUME (Thm.hyp th)) @ thl) th;


(* Main rewriting tactic *)

fun GEN_REWRITE_TAC f rws = Conv.CONV_TAC o GEN_REWRITE_CONV f rws;

val PURE_REWRITE_TAC = GEN_REWRITE_TAC Conv.TOP_DEPTH_CONV empty_rewrites
and 
PURE_ONCE_REWRITE_TAC = GEN_REWRITE_TAC Conv.ONCE_DEPTH_CONV empty_rewrites;

fun REWRITE_TAC thl = GEN_REWRITE_TAC Conv.TOP_DEPTH_CONV (base_rewrites()) thl
and ONCE_REWRITE_TAC thl = 
    GEN_REWRITE_TAC Conv.ONCE_DEPTH_CONV (base_rewrites()) thl;


(* Rewrite a goal with the help of its assumptions *)

fun PURE_ASM_REWRITE_TAC thl :tactic = 
   Tactical.ASSUM_LIST (fn asl => PURE_REWRITE_TAC (asl @ thl))
and ASM_REWRITE_TAC thl :tactic      = 
   Tactical.ASSUM_LIST (fn asl => REWRITE_TAC (asl @ thl))
and PURE_ONCE_ASM_REWRITE_TAC thl :tactic = 
   Tactical.ASSUM_LIST (fn asl => PURE_ONCE_REWRITE_TAC (asl @ thl))
and ONCE_ASM_REWRITE_TAC thl :tactic      = 
   Tactical.ASSUM_LIST (fn asl => ONCE_REWRITE_TAC (asl @ thl));

(* Rewriting using equations that satisfy a predicate  *)
fun FILTER_PURE_ASM_REWRITE_RULE f thl th =
    PURE_REWRITE_RULE ((map Thm.ASSUME (filter f (Thm.hyp th))) @ thl) th
and FILTER_ASM_REWRITE_RULE f thl th = 
    REWRITE_RULE ((map Thm.ASSUME (filter f (Thm.hyp th))) @ thl) th
and FILTER_PURE_ONCE_ASM_REWRITE_RULE f thl th =
    PURE_ONCE_REWRITE_RULE ((map Thm.ASSUME (filter f (Thm.hyp th))) @ thl) th
and FILTER_ONCE_ASM_REWRITE_RULE f thl th = 
    ONCE_REWRITE_RULE ((map Thm.ASSUME (filter f (Thm.hyp th))) @ thl) th;;

fun FILTER_PURE_ASM_REWRITE_TAC f thl =
    Tactical.ASSUM_LIST 
          (fn asl => PURE_REWRITE_TAC ((filter (f o Thm.concl) asl)@thl))
and FILTER_ASM_REWRITE_TAC f thl =
    Tactical.ASSUM_LIST
          (fn asl => REWRITE_TAC ((filter (f o Thm.concl) asl) @ thl))
and FILTER_PURE_ONCE_ASM_REWRITE_TAC f thl =
    Tactical.ASSUM_LIST
         (fn asl => PURE_ONCE_REWRITE_TAC ((filter (f o Thm.concl) asl) @ thl))
and FILTER_ONCE_ASM_REWRITE_TAC f thl =
    Tactical.ASSUM_LIST 
          (fn asl => ONCE_REWRITE_TAC ((filter (f o Thm.concl) asl) @ thl));


(*
 * SUBST_MATCH (|-u=v) th   searches for an instance of u in
 * (the conclusion of) th and then substitutes the corresponding
 * instance of v. Much faster than rewriting.
*)
local
(* Search a sub-term of t matching u *)
exception FIND_MATCH_ERR;
fun find_match u =
   let fun find_mt t =
          Match.match_term u t
          handle _ =>
          find_mt(Term.rator t)
          handle _ =>
          find_mt(Term.rand t)
          handle _ =>
          find_mt(#Body(Term.dest_abs t))
          handle _ =>
          raise FIND_MATCH_ERR
   in
   find_mt
   end
in
fun SUBST_MATCH eqth th =
   let val (tm_inst,ty_inst) = find_match (Dsyntax.lhs(Thm.concl eqth))
                                          (Thm.concl th)
   in
   Drule.SUBS [Drule.INST tm_inst (Thm.INST_TYPE ty_inst eqth)] th
   end
   handle _ => raise REWRITE_ERR{function = "SUBST_MATCH",message = ""}
end;


(* Possible further simplifications:

  |- !t. ((\x.t1) t2)  =  t1

  |- !t P. (!x. t /\ P x) = (t /\ (!x. P x))

  |- !x:*. (@x'.x'=x) = x

  |- !t1 t2 t3. (t1\/t2) ==> t3   =   (t1==>t3) /\ (t2==>t3)  

  |- !t1 t2 t3.  (t1\/t2) /\ t3   =   (t1/\t3) \/ (t2/\t3)   

  |- !t1 t2 t3.  t3 /\ (t1\/t2)   =   (t3/\t1) \/ (t3/\t2)   

  |- !t P.  (?x.P x) ==> t   =   !x'.(P x' ==> t)

  |- !t P.  (?x.P x) /\ t   =   ?x'.(P x' /\ t)

  |- !t P.  t /\ (?x.P x)   =   ?x'.(t /\ P x')

  |- !t1 t2:bool.  (t1 = t2)  =  (t1==>t2  /\  t2==>t1)

*)

end; (* REWRITE *)
