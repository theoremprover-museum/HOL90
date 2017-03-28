signature HOL_MATCH =
    sig
        val HOL_MATCH_MP : thm -> thm -> thm
    end;

(* ========================================================================= *)
(*  FILE          : hol_match.sml                                            *)
(*  DESCRIPTION   : Some higher order matching in HOL                        *)
(*                                                                           *)
(*  AUTHOR        : Matthew Morley, University of Edinburgh                  *)
(*  DATE          : January 1993                                             *)
(*  HISTORY       : Specialised to HOL90 from HOL88 prog_logic library       *)
(* ========================================================================= *)

functor Hol_Match () : HOL_MATCH =
    struct

  fun HOL_MATCH_ERR {function,message} = 
      HOL_ERR{origin_structure = "Hol_match",
              origin_function = function,
              message = message}

  exception FAIL of string

  open Rsyntax;

(* fun apply_inst_subst (terms,types) t = subst terms (inst types t) *)

  fun apply_inst_subst (l1,l2) t = 
      rev_itlist 
      (fn pair => fn term => subst [pair] term) 
      l1 
      (rev_itlist (fn pair => fn term => inst [pair] term) l2 t)

  fun hol_match_fn VL t1 t2 =
    if t1 = t2 then ([],[])       
      else if (is_var t1) then if not(mem t1 VL) 
                                 then ([{residue=t2,redex=t1}],[])
                                 else raise FAIL "Match failed"
(* NEW *)
      else if (is_var t2) then if not(mem t2 VL) 
                                 then ([{residue=t1,redex=t2}],[])
                                 else raise FAIL "Match failed"

      else if (is_const t1) andalso (is_const t2) 
                            andalso (can (match_term t1) t2)
             then match_term t1 t2
      else if (is_comb t1) andalso is_var(rator t1) andalso is_var(rand t1)
             then let val {Rand=x,Rator=f} = dest_comb t1
                   in
                      ([{residue=(mk_abs{Bvar=x,Body=t2}),redex=f}],[])
                  end
(* NEW *)
      else if (is_comb t1) andalso is_abs(rator t1) andalso (is_comb t2) 
                           andalso is_abs(rator t2) 
             then hol_match_fn VL (rhs(concl(BETA_CONV t1)))
                                  (rhs(concl(BETA_CONV t2)))

      else if (is_comb t1) andalso is_abs(rator t1) 
             then hol_match_fn VL (rhs(concl(BETA_CONV t1))) t2
(* NEW *)
      else if (is_comb t2) andalso is_abs(rator t2) 
             then hol_match_fn VL (rhs(concl(BETA_CONV t2))) t1

      else if (is_comb t1) andalso (is_comb t2)
             then let val {Rator=rat1,Rand=rnd1} = dest_comb t1
                      and {Rator=rat2,Rand=rnd2} = dest_comb t2

                      val s = hol_match_fn VL rat1 rat2
                      val s'= hol_match_fn VL (apply_inst_subst s rnd1) 
                                               (apply_inst_subst s rnd2)
                  in 
                      ((fst s) @ (fst s'), (snd s) @ (snd s'))
                 end
      else if (is_abs t1) andalso (is_abs t2)
             then let val {Bvar=v1,Body=body1} = dest_abs t1
                      and {Bvar=v2,Body=body2} = dest_abs t2
                  in
                      if v1 = v2
                        then hol_match_fn (v1::VL) body1 body2
                        else raise FAIL "Match failed"
                  end
      else raise FAIL "Match failed"

  fun hol_match t1 t2 = (hol_match_fn [] t1 t2) handle FAIL s =>
      raise HOL_MATCH_ERR{function="hol_match",message=s}


(* ========================================================================= 
   Examples:
   =========

   hol_match (--`x+1`--) (--`2+1`--);

   hol_match (--`x+(y+x)`--) (--`3+(z+3)`--);

   hol_match (--`x+x`--)  (--`(p*q)+(p*p)`--);

   hol_match (--`(x+x)>x`--) (--`((p*q)+(p*p))>(p*p)`--);

   hol_match (--`(x+x)>x`--) (--`((p*q)+(p*p))>(q*q)`--);

   hol_match (--`x+((p*q)+x)`--) (--`(r*s)+((4*4)+(r*r))`--);

   hol_match (--`(\x. x+y)z`--) (--`1+2`--);

   hol_match (--`(\x. x+y)z`--) (--`(\x. x+2)1`--);

   hol_match (--`(\x. x+y)z`--) (--`(\w. w+2)1`--);

   hol_match (--`(\x:num. z:num)`--) (--`(\x:num. 1:num)`--);

   hol_match (--`(f:num->num)x`--) (--`x+y`--);

   hol_match (--`(f:num->num)y`--) (--`x+y`--);

   hol_match
      (--`P 0 /\ (!n. P n ==> P(SUC n)) ==> (!n. P n)`--)
      (--`m > 0 /\ (!n. m > n ==> m > SUC n) ==> (!n. m > n)`--);

   hol_match
      (--`P 0 /\ (!n. P n ==> P(SUC n)) ==> (!n. P n)`--)
      (--`0 < m /\ (!n. n < m ==> SUC n < m) ==> (!n. n < m)`--);

   hol_match (--`!x:'a. x=x`--) (--`!x:num.x=x`--);

   hol_match 
      (--`!s:string->num. p' s ==> p s`--) 
      (--`!s:string->num. F ==> (s "X" = x) /\ (s "Y" = y)`--);

   ========================================================================= *)

(* ========================================================================= *)
(*  hol_match a given part of "th" to a term, instantiating "th".            *)
(*  The part should be free in the theorem, except for outer bound variables *)
(* ========================================================================= *)


  fun HOL_PART_MATCH partfn th tm =
      let val pth = GSPEC (GEN_ALL th)  
          val pat = partfn(concl pth) 
          val matchfn = hol_match pat 
      in
          INST_TY_TERM (matchfn tm) pth
      end

(* ========================================================================= *)
(*  Matching Modus Ponens for implications like: |- !x1 ... xn. P ==> Q      *)
(*  Matches x1 ... xn : |-  P'  ---->  |- Q'                                 *)
(*  Matches all types in conclusion except those mentioned in hypotheses     *)
(* ========================================================================= *)

  fun OUTER_BETA_CONV t =
      (BETA_CONV t) handle _ =>
          (let val {Rator,Rand} = dest_comb t
           in
               MK_COMB (OUTER_BETA_CONV Rator, OUTER_BETA_CONV Rand)
           end) handle _ =>
               (let val {Bvar,Body} = dest_abs t
                in
                    (uncurry ABS) (Bvar, (OUTER_BETA_CONV Body))
                end) handle _ =>
                    (REFL t)

  fun HOL_MATCH_MP impth th =
      let val match = (HOL_PART_MATCH (#ant o dest_imp) impth) 
          handle _ => raise HOL_MATCH_ERR{function="HOL_MATCH_MP",message=""}
      in
          MATCH_MP (CONV_RULE OUTER_BETA_CONV (match (concl th))) th
      end
    
    end; (* functor Hol_Match *)

