(*****************************************************************************)
(* FILE          : theorems.sml                                              *)
(* DESCRIPTION   : Theorems for arithmetic formulae.                         *)
(*                                                                           *)
(* AUTHOR        : R.J.Boulton, University of Cambridge                      *)
(* DATE          : 4th March 1991                                            *)
(*                                                                           *)
(* TRANSLATOR    : R.J.Boulton, University of Cambridge                      *)
(* DATE          : 5th February 1993                                         *)
(*                                                                           *)
(* LAST MODIFIED : R.J.Boulton                                               *)
(* DATE          : 13th August 1996                                          *)
(*****************************************************************************)

structure Arith_theorems : Arith_theorems_sig =
struct

type thm = CoreHol.Thm.thm;
open Parse;
open CoreHol.Theory;
open CoreHol.Thm;
open Drule;
open Conv;
open Lib;
open HOL;

val m = --`m:num`--
and n = --`n:num`--
and p = --`p:num`--;

(*===========================================================================*)
(* Theorems for normalizing arithmetic                                       *)
(*===========================================================================*)

(*---------------------------------------------------------------------------*)
(* ONE_PLUS = |- !n. SUC n = 1 + n                                           *)
(*---------------------------------------------------------------------------*)

val ONE_PLUS = theorem "arithmetic" "SUC_ONE_ADD";

(*---------------------------------------------------------------------------*)
(* ZERO_PLUS = |- !m. 0 + m = m                                              *)
(*---------------------------------------------------------------------------*)

val ZERO_PLUS =
 GEN_ALL (el 1 (CONJUNCTS (theorem "arithmetic" "ADD_CLAUSES")));

(*---------------------------------------------------------------------------*)
(* PLUS_ZERO = |- !m. m + 0 = m                                              *)
(*---------------------------------------------------------------------------*)

val PLUS_ZERO =
 GEN_ALL (el 2 (CONJUNCTS (theorem "arithmetic" "ADD_CLAUSES")));

(*---------------------------------------------------------------------------*)
(* SUC_ADD1 = |- !m n. SUC (m + n) = (SUC m) + n                             *)
(*---------------------------------------------------------------------------*)

val SUC_ADD1 =
 GENL [m,n] (SYM (el 3 (CONJUNCTS (theorem "arithmetic" "ADD_CLAUSES"))));

(*---------------------------------------------------------------------------*)
(* SUC_ADD2 = |- !m n. SUC (m + n) = (SUC n) + m                             *)
(*---------------------------------------------------------------------------*)

val SUC_ADD2 = theorem "arithmetic" "SUC_ADD_SYM";

(*---------------------------------------------------------------------------*)
(* ZERO_MULT = |- !m. 0 * m = 0                                              *)
(* MULT_ZERO = |- !m. m * 0 = 0                                              *)
(* ONE_MULT = |- !m. 1 * m = m                                               *)
(* MULT_ONE = |- !m. m * 1 = m                                               *)
(* MULT_SUC = |- !m n. (SUC m) * n = (m * n) + n                             *)
(*---------------------------------------------------------------------------*)

local 
   val thms = CONJUNCTS (SPEC_ALL (theorem "arithmetic" "MULT_CLAUSES"))
in
   val ZERO_MULT = GEN_ALL (el 1 thms)
   val MULT_ZERO = GEN_ALL (el 2 thms)
   val ONE_MULT = GEN_ALL (el 3 thms)
   val MULT_ONE = GEN_ALL (el 4 thms)
   val MULT_SUC = GENL [m,n] (el 5 thms)
end;

(*---------------------------------------------------------------------------*)
(* MULT_COMM = |- !m n. (m * n) = (n * m)                                    *)
(*---------------------------------------------------------------------------*)

val MULT_COMM = theorem "arithmetic" "MULT_SYM";

(*---------------------------------------------------------------------------*)
(* MULT_EQ_SUC = |- !m n p. m = n = ((SUC p) * m) = ((SUC p) * n)            *)
(*---------------------------------------------------------------------------*)

val MULT_EQ_SUC = GSYM (theorem "arithmetic" "MULT_MONO_EQ");

(*---------------------------------------------------------------------------*)
(* MULT_LEQ_SUC = |- !m n p. m <= n = ((SUC p) * m) <= ((SUC p) * n)         *)
(*---------------------------------------------------------------------------*)

val MULT_LEQ_SUC = theorem "arithmetic" "MULT_LESS_EQ_SUC";

(*---------------------------------------------------------------------------*)
(* MULT_LESS_SUC = |- !m n p. m < n = ((SUC p) * m) < ((SUC p) * n)          *)
(*---------------------------------------------------------------------------*)

val MULT_LESS_SUC = GSYM (theorem "arithmetic" "LESS_MULT_MONO");

(*---------------------------------------------------------------------------*)
(* SUC_ADD_EQ_F = |- !m n. (SUC (m + n) = m) = F                             *)
(*---------------------------------------------------------------------------*)

val SUC_ADD_EQ_F =
 GENL [m,n]
  (SUBS [SYM (SPECL [m,n] (theorem "arithmetic" "ADD_SUC"))]
    (TRANS (SPECL [m,--`SUC n`--] (theorem "arithmetic" "ADD_INV_0_EQ"))
           (EQF_INTRO (GSYM (SPEC n (theorem "arithmetic" "SUC_NOT"))))));

(*---------------------------------------------------------------------------*)
(* EQ_SUC_ADD_F = |- !m n. (m = SUC (m + n)) = F                             *)
(*---------------------------------------------------------------------------*)

val EQ_SUC_ADD_F =
 (GENL [m,n] o EQF_INTRO o GSYM o EQF_ELIM o SPEC_ALL) SUC_ADD_EQ_F;

(*---------------------------------------------------------------------------*)
(* ZERO_LESS_EQ = |- !n. 0 <= n                                              *)
(*---------------------------------------------------------------------------*)

val ZERO_LESS_EQ = theorem "arithmetic" "ZERO_LESS_EQ";

(*---------------------------------------------------------------------------*)
(* ZERO_LESS_EQ_T = |- !n. (0 <= n) = T                                      *)
(*---------------------------------------------------------------------------*)

val ZERO_LESS_EQ_T =
 GEN_ALL (EQT_INTRO (SPEC_ALL (theorem "arithmetic" "ZERO_LESS_EQ")));

(*---------------------------------------------------------------------------*)
(* SUC_LESS_EQ_ZERO_F = |- !n. ((SUC n) <= 0) = F                            *)
(*---------------------------------------------------------------------------*)

val SUC_LESS_EQ_ZERO_F =
 GEN_ALL (EQF_INTRO (SPEC_ALL (theorem "arithmetic" "NOT_SUC_LESS_EQ_0")));

(*---------------------------------------------------------------------------*)
(* LESS_EQ_PLUS = |- !m n. m <= (m + n)                                      *)
(*---------------------------------------------------------------------------*)

val LESS_EQ_PLUS = theorem "arithmetic" "LESS_EQ_ADD";

(*---------------------------------------------------------------------------*)
(* SUC_ADD_LESS_EQ_F = |- !m n. ((SUC (m + n)) <= m) = F                     *)
(*---------------------------------------------------------------------------*)

val SUC_ADD_LESS_EQ_F =
 GENL [m,n]
  (EQF_INTRO (SPEC_ALL (theorem "arithmetic" "NOT_SUC_ADD_LESS_EQ")));

(*---------------------------------------------------------------------------*)
(* ZERO_LESS_SUC_T = |- !n. (0 < SUC n) = T                                  *)
(*---------------------------------------------------------------------------*)

val ZERO_LESS_SUC_T =
 GEN_ALL
  (EQT_INTRO
    (MP (SPECL [--`0`--,n] (theorem "arithmetic" "LESS_EQ_IMP_LESS_SUC"))
        (SPEC n (theorem "arithmetic" "ZERO_LESS_EQ"))));

(*---------------------------------------------------------------------------*)
(* LESS_ZERO_F = |- !n. (n < 0) = F                                          *)
(*---------------------------------------------------------------------------*)

val LESS_ZERO_F =
 (GEN_ALL o EQF_INTRO)
  (EQ_MP (SYM (SPECL [n,--`0`--] (theorem "arithmetic" "NOT_LESS")))
         (SPEC n (theorem "arithmetic" "ZERO_LESS_EQ")));

(*---------------------------------------------------------------------------*)
(* LESS_PLUS = |- !m n. m < SUC (m + n)                                      *)
(*---------------------------------------------------------------------------*)

val LESS_PLUS =
 GENL [m,n]
  (MP (SPECL [m,--`m + n`--] (theorem "arithmetic" "LESS_EQ_IMP_LESS_SUC"))
      (SPECL [m,n] (theorem "arithmetic" "LESS_EQ_ADD")));

(*---------------------------------------------------------------------------*)
(* ADD_LESS_F = |- !m n. ((m + n) < m) = F                                   *)
(*---------------------------------------------------------------------------*)

val ADD_LESS_F =
 GENL [m,n]
  (TRANS
    (SPECL [--`m + n`--,m] (theorem "arithmetic" "LESS_EQ"))
    (EQF_INTRO (SPECL [m,n] (theorem "arithmetic" "NOT_SUC_ADD_LESS_EQ"))));

(*---------------------------------------------------------------------------*)
(* EQ_EQ_TRANSIT     = |- !m n p. m = n  /\ n = p  ==> m = p                 *)
(* EQ_LEQ_TRANSIT    = |- !m n p. m = n  /\ n <= p ==> m <= p                *)
(* EQ_LESS_TRANSIT   = |- !m n p. m = n  /\ n < p  ==> m < p                 *)
(* LEQ_EQ_TRANSIT    = |- !m n p. m <= n /\ n = p  ==> m <= p                *)
(* LEQ_LEQ_TRANSIT   = |- !m n p. m <= n /\ n <= p ==> m <= p                *)
(* LEQ_LESS_TRANSIT  = |- !m n p. m <= n /\ n < p  ==> m < p                 *)
(* LESS_EQ_TRANSIT   = |- !m n p. m < n  /\ n = p  ==> m < p                 *)
(* LESS_LEQ_TRANSIT  = |- !m n p. m < n  /\ n <= p ==> m < p                 *)
(* LESS_LESS_TRANSIT = |- !m n p. m < n  /\ n < p  ==> m < p                 *)
(*                  OR |- !m n p. m < n  /\ n < p  ==> 1 + m < p (non-dense) *)
(*---------------------------------------------------------------------------*)

val EQ_EQ_TRANSIT = GENL [m,n,p] (ISPECL [m,n,p] EQ_TRANS);

val EQ_LEQ_TRANSIT =
   let val tm = (--`(m = n) /\ (n <= p)`--)
       val (th1,th2) = CONJ_PAIR (ASSUME tm)
   in  GENL [m,n,p] (DISCH tm (SUBS [SYM th1] th2))
   end;

val EQ_LESS_TRANSIT =
   let val tm = (--`(m = n) /\ (n < p)`--)
       val (th1,th2) = CONJ_PAIR (ASSUME tm)
   in  GENL [m,n,p] (DISCH tm (SUBS [SYM th1] th2))
   end;

val LEQ_EQ_TRANSIT =
   let val tm = (--`(m <= n) /\ (n = p)`--)
       val (th1,th2) = CONJ_PAIR (ASSUME tm)
   in  GENL [m,n,p] (DISCH tm (SUBS [th2] th1))
   end;

val LEQ_LEQ_TRANSIT = theorem "arithmetic" "LESS_EQ_TRANS";

val LEQ_LESS_TRANSIT = theorem "arithmetic" "LESS_EQ_LESS_TRANS";

val LESS_EQ_TRANSIT =
   let val tm = (--`(m < n) /\ (n = p)`--)
       val (th1,th2) = CONJ_PAIR (ASSUME tm)
   in  GENL [m,n,p] (DISCH tm (SUBS [th2] th1))
   end;

val LESS_LEQ_TRANSIT = theorem "arithmetic" "LESS_LESS_EQ_TRANS";

val LESS_LESS_TRANSIT = theorem "arithmetic" "LESS_TRANS";
(* For non-dense orderings:
        let val th1 = SPECL [--`SUC m`--,--`SUC n`--,p]
                         (theorem "arithmetic" "LESS_LESS_EQ_TRANS")
            and th2 = SPECL [m,n] (theorem "arithmetic" "LESS_MONO_EQ")
            and th3 = SYM (SPECL [n,p] (theorem "arithmetic" "LESS_EQ"))
            and th4 = SPEC m (theorem "arithmetic" "SUC_ONE_ADD")
        in  GENL [m,n,p] (SUBS [th2,th3,th4] th1)
        end;
*)

end; (* Arith_theorems *)
