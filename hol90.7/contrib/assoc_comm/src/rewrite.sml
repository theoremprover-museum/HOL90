structure AC_Rewrite: AC_Rewrite_sig =
struct

open Rsyntax;

fun AC_REWRITE_ERR{func,mesg} = 
           HOL_ERR{origin_structure = "AC_Rewrite",
                   origin_function = func,
                   message = mesg}

(* Split a theorem into a list of theorems suitable for rewriting:
 *
 *   1. Specialize all variables (GSPEC o GEN_ALL).
 *
 *   2. Then do the following:
 *
 *        |- t1 /\ t2     -->    [|- t1 ; |- t2]
 *
 *   3. Then |- t --> |- t = T and |- ~t --> |- t = F
 *
*)
local
fun mk_rewrites th =
   let val th = (GSPEC o GEN_ALL) th
       val t = Thm.concl th 
   in 
   if (Dsyntax.is_eq t)
   then [th]
   else if (Dsyntax.is_conj t)
        then (op @ o (mk_rewrites##mk_rewrites) o CONJ_PAIR) th
        else if (Dsyntax.is_neg t)
             then [Drule.EQF_INTRO th]
             else [Drule.EQT_INTRO th]
   end
   handle _ => raise AC_REWRITE_ERR{func = "mk_rewrites",mesg = ""}
in
fun add_to_rules thl rules = itlist (append o mk_rewrites) thl rules

val empty_rules = []:thm list
(* List of basic rewrites (made assignable to enable us to add extra
 * rewrite rules later, e.g., those for the theory of pairs).
 *****)
val basic_rewrites = ref
  (add_to_rules [Drule.REFL_CLAUSE,
                 Drule.EQ_CLAUSES,
                 Drule.NOT_CLAUSES,
                 Drule.AND_CLAUSES,
                 Drule.OR_CLAUSES,
                 Drule.IMP_CLAUSES,                             
                 Drule.COND_CLAUSES,
                 Drule.FORALL_SIMP,
                 Drule.EXISTS_SIMP,
                 Drule.ABS_SIMP] [])
end;


fun first_success f =
   let fun first [] _ = raise AC_REWRITE_ERR{func="first_success", mesg = ""}
         | first (a::rst) itm = f a itm handle _ => first rst itm
   in first
   end;

fun AC_REWRITES_CONV ACs = first_success (Ac_tools.AC_REWR_CONV ACs);


(* =====================================================================*)
(* Main rewriting conversion                         			*)
(* =====================================================================*)

fun GEN_AC_REWRITE_CONV (rw_func:conv->conv) basic_rules ACs thl = 
   rw_func (AC_REWRITES_CONV ACs (add_to_rules thl (!basic_rules)));

(* ---------------------------------------------------------------------*)
(* Rewriting conversions.                        			*)
(* ---------------------------------------------------------------------*)

val PURE_AC_REWRITE_CONV = GEN_AC_REWRITE_CONV Conv.TOP_DEPTH_CONV
                                               (ref empty_rules)
and AC_REWRITE_CONV = GEN_AC_REWRITE_CONV Conv.TOP_DEPTH_CONV basic_rewrites
and PURE_ONCE_AC_REWRITE_CONV = GEN_AC_REWRITE_CONV Conv.ONCE_DEPTH_CONV
                                                    (ref empty_rules)
and ONCE_AC_REWRITE_CONV = GEN_AC_REWRITE_CONV Conv.ONCE_DEPTH_CONV 
                                               basic_rewrites;

(* Main rewriting rule *)
fun GEN_AC_REWRITE_RULE f n ACs = Conv.CONV_RULE o GEN_AC_REWRITE_CONV f n ACs;

val PURE_AC_REWRITE_RULE = GEN_AC_REWRITE_RULE Conv.TOP_DEPTH_CONV
                                               (ref empty_rules)
and AC_REWRITE_RULE = GEN_AC_REWRITE_RULE Conv.TOP_DEPTH_CONV basic_rewrites
and PURE_ONCE_AC_REWRITE_RULE = GEN_AC_REWRITE_RULE Conv.ONCE_DEPTH_CONV 
                                                    (ref empty_rules)
and ONCE_AC_REWRITE_RULE = GEN_AC_REWRITE_RULE Conv.ONCE_DEPTH_CONV 
                                               basic_rewrites;

(* Rewrite a theorem with the help of its assumptions *)

fun PURE_ASM_AC_REWRITE_RULE ACs thl th =
   PURE_AC_REWRITE_RULE ACs ((map Thm.ASSUME (Thm.hyp th)) @ thl) th
and ASM_AC_REWRITE_RULE ACs thl th = 
   AC_REWRITE_RULE ACs ((map Thm.ASSUME (Thm.hyp th)) @ thl) th
and PURE_ONCE_ASM_AC_REWRITE_RULE ACs thl th =
   PURE_ONCE_AC_REWRITE_RULE ACs ((map Thm.ASSUME (Thm.hyp th)) @ thl) th
and ONCE_ASM_AC_REWRITE_RULE ACs thl th = 
   ONCE_AC_REWRITE_RULE ACs ((map Thm.ASSUME (Thm.hyp th)) @ thl) th;


(* Main rewriting tactic *)

fun GEN_AC_REWRITE_TAC f n ACs = Conv.CONV_TAC o GEN_AC_REWRITE_CONV f n ACs;

val PURE_AC_REWRITE_TAC =
   GEN_AC_REWRITE_TAC Conv.TOP_DEPTH_CONV (ref empty_rules)
and AC_REWRITE_TAC =
   GEN_AC_REWRITE_TAC Conv.TOP_DEPTH_CONV basic_rewrites
and PURE_ONCE_AC_REWRITE_TAC =
   GEN_AC_REWRITE_TAC Conv.ONCE_DEPTH_CONV (ref empty_rules)
and ONCE_AC_REWRITE_TAC =
   GEN_AC_REWRITE_TAC Conv.ONCE_DEPTH_CONV basic_rewrites;


(* Rewrite a goal with the help of its assumptions *)

fun PURE_ASM_AC_REWRITE_TAC ACs thl :tactic = 
   Tactical.ASSUM_LIST (fn asl => PURE_AC_REWRITE_TAC ACs (asl @ thl))
and ASM_AC_REWRITE_TAC ACs thl :tactic      = 
   Tactical.ASSUM_LIST (fn asl => AC_REWRITE_TAC ACs (asl @ thl))
and PURE_ONCE_ASM_AC_REWRITE_TAC ACs thl :tactic = 
   Tactical.ASSUM_LIST (fn asl => PURE_ONCE_AC_REWRITE_TAC ACs (asl @ thl))
and ONCE_ASM_AC_REWRITE_TAC ACs thl :tactic      = 
   Tactical.ASSUM_LIST (fn asl => ONCE_AC_REWRITE_TAC ACs (asl @ thl));

(* Rewriting using equations that satisfy a predicate  *)
fun FILTER_PURE_ASM_AC_REWRITE_RULE f ACs thl th =
    PURE_AC_REWRITE_RULE ACs((map Thm.ASSUME (filter f (Thm.hyp th))) @ thl) th
and FILTER_ASM_AC_REWRITE_RULE f ACs thl th = 
    AC_REWRITE_RULE ACs ((map Thm.ASSUME (filter f (Thm.hyp th))) @ thl) th
and FILTER_PURE_ONCE_ASM_AC_REWRITE_RULE f ACs thl th =
    PURE_ONCE_AC_REWRITE_RULE ACs((map Thm.ASSUME (filter f (Thm.hyp th)))@thl)
                                 th
and FILTER_ONCE_ASM_AC_REWRITE_RULE f ACs thl th = 
    ONCE_AC_REWRITE_RULE ACs ((map Thm.ASSUME (filter f (Thm.hyp th))) @ thl) 
                             th;

fun FILTER_PURE_ASM_AC_REWRITE_TAC f ACs thl =
    Tactical.ASSUM_LIST 
          (fn asl => PURE_AC_REWRITE_TAC ACs((filter (f o Thm.concl) asl)@thl))
and FILTER_ASM_AC_REWRITE_TAC f ACs thl =
    Tactical.ASSUM_LIST
          (fn asl => AC_REWRITE_TAC ACs ((filter (f o Thm.concl) asl) @ thl))
and FILTER_PURE_ONCE_ASM_AC_REWRITE_TAC f ACs thl =
  Tactical.ASSUM_LIST
    (fn asl => PURE_ONCE_AC_REWRITE_TAC ACs ((filter (f o Thm.concl) asl)@thl))
and FILTER_ONCE_ASM_AC_REWRITE_TAC f ACs thl =
    Tactical.ASSUM_LIST 
       (fn asl => ONCE_AC_REWRITE_TAC ACs((filter (f o Thm.concl) asl) @ thl));

end; (* AC_Rewrite *)
