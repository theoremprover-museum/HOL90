(*****************************************************************************)
(* FILE          : thm_convs.sml                                             *)
(* DESCRIPTION   : Conversions for rewriting with arithmetic theorems.       *)
(*                                                                           *)
(* READS FILES   : <none>                                                    *)
(* WRITES FILES  : <none>                                                    *)
(*                                                                           *)
(* AUTHOR        : R.J.Boulton, University of Cambridge                      *)
(* DATE          : 4th March 1991                                            *)
(*                                                                           *)
(* TRANSLATOR    : R.J.Boulton, University of Cambridge                      *)
(* DATE          : 5th February 1993                                         *)
(*                                                                           *)
(* LAST MODIFIED : R.J.Boulton                                               *)
(* DATE          : 17th February 1993                                        *)
(*****************************************************************************)

structure Arith_thm_convs : Arith_thm_convs_sig =
struct
open Rsyntax;
open Arith_theorems;

(*===========================================================================*)
(* Conversions for rewriting Boolean terms                                   *)
(*===========================================================================*)

val CONJ_ASSOC_NORM_CONV = REWR_CONV (GSYM CONJ_ASSOC);

val DISJ_ASSOC_NORM_CONV = REWR_CONV (GSYM DISJ_ASSOC);

val EQ_EXPAND_CONV = REWR_CONV EQ_EXPAND;

val IMP_EXPAND_CONV = REWR_CONV IMP_DISJ_THM;

val IMP_F_EQ_F_CONV = REWR_CONV IMP_F_EQ_F;

val IMP_IMP_CONJ_IMP_CONV = REWR_CONV AND_IMP_INTRO;

val LEFT_DIST_NORM_CONV = REWR_CONV LEFT_AND_OVER_OR;

val NOT_CONJ_NORM_CONV =
 REWR_CONV
  (GEN_ALL (CONJUNCT1 (SPECL [--`t1:bool`--,--`t2:bool`--] DE_MORGAN_THM)));

val NOT_DISJ_NORM_CONV =
 REWR_CONV
  (GEN_ALL (CONJUNCT2 (SPECL [--`t1:bool`--,--`t2:bool`--] DE_MORGAN_THM)));

val NOT_NOT_NORM_CONV = REWR_CONV (CONJUNCT1 NOT_CLAUSES);

val OR_F_CONV = REWR_CONV (el 3 (CONJUNCTS (SPEC (--`x:bool`--) OR_CLAUSES)));

val RIGHT_DIST_NORM_CONV = REWR_CONV RIGHT_AND_OVER_OR;

(*===========================================================================*)
(* Conversions for rewriting arithmetic terms                                *)
(*===========================================================================*)

val ADD_ASSOC_CONV = REWR_CONV (theorem "arithmetic" "ADD_ASSOC");

val ADD_SYM_CONV = REWR_CONV (theorem "arithmetic" "ADD_SYM");

val GATHER_BOTH_CONV =
 REWR_CONV
  (SYM (SPECL [--`a:num`--,--`b:num`--,--`x:num`--]
         (theorem "arithmetic" "RIGHT_ADD_DISTRIB")));

val GATHER_LEFT_CONV =
 REWR_CONV
  (SUBS [el 3 (CONJUNCTS (SPECL [--`x:num`--,--`n:num`--]
                           (theorem "arithmetic" "MULT_CLAUSES")))]
    (SYM (SPECL [--`a:num`--,--`1`--,--`x:num`--]
           (theorem "arithmetic" "RIGHT_ADD_DISTRIB"))));

val GATHER_NEITHER_CONV = REWR_CONV (GSYM (theorem "arithmetic" "TIMES2"));

val GATHER_RIGHT_CONV =
 REWR_CONV
  (SUBS [el 3 (CONJUNCTS (SPECL [--`x:num`--,--`n:num`--]
                           (theorem "arithmetic" "MULT_CLAUSES")))]
    (SYM (SPECL [--`1`--,--`b:num`--,--`x:num`--]
           (theorem "arithmetic" "RIGHT_ADD_DISTRIB"))));

val GEQ_NORM_CONV = REWR_CONV (theorem "arithmetic" "GREATER_EQ");

val GREAT_NORM_CONV =
 REWR_CONV
  (SUBS [SYM (SPECL [--`m:num`--,--`n:num`--]
                 (definition "arithmetic" "GREATER")),
         SPEC (--`n:num`--) (theorem "arithmetic" "SUC_ONE_ADD")]
    (SPECL [--`n:num`--,--`m:num`--] (theorem "arithmetic" "LESS_EQ")));

val LEFT_ADD_DISTRIB_CONV =
 REWR_CONV (theorem "arithmetic" "LEFT_ADD_DISTRIB");

val LESS_NORM_CONV =
 REWR_CONV
  (SUBS [SPEC (--`m:num`--) (theorem "arithmetic" "SUC_ONE_ADD")]
    (SPECL [--`m:num`--,--`n:num`--] (theorem "arithmetic" "LESS_EQ")));

val MULT_ASSOC_CONV = REWR_CONV (theorem "arithmetic" "MULT_ASSOC");

val MULT_COMM_CONV = REWR_CONV MULT_COMM;

val NOT_GEQ_NORM_CONV =
 REWR_CONV
  (SUBS [SPEC (--`m:num`--) (theorem "arithmetic" "SUC_ONE_ADD")]
    (SPECL [--`m:num`--,--`n:num`--]
        (theorem "arithmetic" "NOT_GREATER_EQ")));

val NOT_GREAT_NORM_CONV = REWR_CONV (theorem "arithmetic" "NOT_GREATER");

val NOT_LEQ_NORM_CONV =
 REWR_CONV
  (SUBS [SPEC (--`n:num`--) (theorem "arithmetic" "SUC_ONE_ADD")]
    (SPECL [--`m:num`--,--`n:num`--] (theorem "arithmetic" "NOT_LEQ")));

val NOT_LESS_NORM_CONV = REWR_CONV (theorem "arithmetic" "NOT_LESS");

val NOT_NUM_EQ_NORM_CONV =
 REWR_CONV
  (SUBS [SPEC (--`m:num`--) (theorem "arithmetic" "SUC_ONE_ADD"),
         SPEC (--`n:num`--) (theorem "arithmetic" "SUC_ONE_ADD")]
    (SPECL [--`m:num`--,--`n:num`--] (theorem "arithmetic" "NOT_NUM_EQ")));

val NUM_EQ_NORM_CONV = REWR_CONV (theorem "arithmetic" "EQ_LESS_EQ");

val PLUS_ZERO_CONV = REWR_CONV PLUS_ZERO;

val SYM_ADD_ASSOC_CONV = REWR_CONV (GSYM (theorem "arithmetic" "ADD_ASSOC"));

val SYM_ONE_MULT_CONV = REWR_CONV (GEN_ALL (SYM (SPEC_ALL ONE_MULT)));

val ZERO_MULT_CONV = REWR_CONV ZERO_MULT;

val ZERO_MULT_PLUS_CONV =
 REWR_CONV
  (SUBS [SYM (CONJUNCT1 (SPECL [--`a:num`--,--`b:num`--]
                            (theorem "arithmetic" "MULT_CLAUSES")))]
   (SPEC (--`b:num`--)
       (GEN_ALL (CONJUNCT1 (theorem "arithmetic" "ADD_CLAUSES")))));

val ZERO_PLUS_CONV = REWR_CONV ZERO_PLUS;

(*===========================================================================*)
(* Conversions for rewriting inequalities                                    *)
(*===========================================================================*)

val LEQ_PLUS_CONV = REWR_CONV (theorem "arithmetic" "ADD_MONO_LESS_EQ");

(*===========================================================================*)
(* Conversions for final simplification                                      *)
(*===========================================================================*)

val FORALL_SIMP_CONV = REWR_CONV FORALL_SIMP;

(*===========================================================================*)
(* Conversions for normalising and eliminating subtraction                   *)
(*===========================================================================*)

val NUM_COND_RATOR_CONV =
 REWR_CONV
  (INST_TYPE [{residue = (==`:num`==),redex = (==`:'a`==)}] COND_RATOR);

val NUM_COND_RAND_CONV =
 REWR_CONV
  (INST_TYPE [{residue = (==`:num`==),redex = (==`:'a`==)}] COND_RAND);

val SUB_NORM_CONV =
 ((GEN_REWRITE_CONV I Rewrite.empty_rewrites) o
   (map (theorem "arithmetic")))
 ["SUB_LEFT_ADD",          "SUB_RIGHT_ADD",
  "SUB_LEFT_SUB",          "SUB_RIGHT_SUB",
  "LEFT_SUB_DISTRIB",      "RIGHT_SUB_DISTRIB",
  "SUB_LEFT_SUC",
  "SUB_LEFT_LESS_EQ",      "SUB_RIGHT_LESS_EQ",
  "SUB_LEFT_LESS",         "SUB_RIGHT_LESS",
  "SUB_LEFT_GREATER_EQ",   "SUB_RIGHT_GREATER_EQ",
  "SUB_LEFT_GREATER",      "SUB_RIGHT_GREATER",
  "SUB_LEFT_EQ",           "SUB_RIGHT_EQ"
 ];

(*===========================================================================*)
(* Conversions for normalising and eliminating conditionals                  *)
(*===========================================================================*)

val COND_RATOR_CONV = REWR_CONV COND_RATOR;
val COND_RAND_CONV = REWR_CONV COND_RAND;
val COND_EXPAND_CONV = REWR_CONV COND_EXPAND;

end
