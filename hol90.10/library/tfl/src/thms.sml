structure Thms : Thms_sig =
struct
 type Thm = CoreHol.Thm.thm
 open WFTheoryLoaded;
 open Lib CoreHol Parse;
 open Term Dsyntax Theory Drule Tactical Tactic Conv; infix THEN
 open Resolve;

   val LET_DEF = boolThry.LET_DEF;
   val WF_INDUCTION_THM = theorem "WF" "WF_INDUCTION_THM"
   val WFREC_COROLLARY = theorem "WF" "WFREC_COROLLARY"
   val CUT_DEF = definition "WF" "RESTRICT_DEF"
   val CUT_LEMMA = theorem "WF" "RESTRICT_LEMMA"

   (* SELECT_AX = |- !P x. P x ==> P ($@ P) *)
   val SELECT_AX = boolThry.SELECT_AX;

   val COND_CONG = prove(--`!P P' (x:'a) x' y y'.
            (P = P') /\ 
            (P'  ==> (x = x')) /\ 
            (~P' ==> (y = y'))
            ==> ((P => x | y) = (P' => x' | y'))`--,
         REPEAT GEN_TAC THEN STRIP_TAC THEN 
         Rewrite.ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN
         RES_TAC THEN Rewrite.ASM_REWRITE_TAC[])

   val LET_CONG = prove(--`!f (g:'a->'b) M M'. 
             (M = M') /\ 
             (!x:'a. (x = M') ==> (f x = g x)) 
             ==> (LET f M = LET g M')`--,
          Rewrite.REWRITE_TAC[LET_DEF] THEN BETA_TAC 
            THEN REPEAT GEN_TAC THEN STRIP_TAC 
            THEN Rewrite.ASM_REWRITE_TAC[] 
            THEN FIRST_ASSUM MATCH_MP_TAC THEN REFL_TAC);



   fun W f x = f x x;
   local fun bval w t = (type_of t = Parse.type_parser`:bool`) andalso 
                        (can (find_term is_var) t) andalso 
                        (free_in t w)
   in val TAUT_CONV =
       C (curry prove)
         (REPEAT GEN_TAC THEN (REPEAT o CHANGED_TAC o W)
           (C (curry op THEN) (Rewrite.REWRITE_TAC[]) o BOOL_CASES_TAC o hd 
                               o sort free_in
                               o W(find_terms o bval) o snd))
         o Parse.term_parser
   end;

   val P = GEN_ALL o TAUT_CONV;

   val thm_eq    = P`x ==> y ==> (x = y)`
   val eqT       = P`(x = T) ==> x`
   val rev_eq_mp = P`(x = y) ==> y ==> x`
   val simp_thm  = P`(x==>y) ==> (x = x') ==> (x' ==> y)`

end;
