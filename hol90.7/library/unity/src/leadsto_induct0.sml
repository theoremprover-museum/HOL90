(*	-*- Emacs Mode: sml -*-                                       *)

(*---------------------------------------------------------------------------*)
(*
   File:         leadsto_induct.ml
   Description:  

   This file defines the induction tactics for the  LEADSTO definition.
   
   Authors:      Copyright by Flemming Andersen 1990.
   Date:         December 19, 1990
*)
(*---------------------------------------------------------------------------*)

(*
loadf"aux_definitions";

autoload_defs_and_thms "unity_lemmas";
autoload_defs_and_thms "state_logic";
autoload_defs_and_thms "unless";
autoload_defs_and_thms "ensures";
autoload_defs_and_thms "leadsto_mod";
autoload_defs_and_thms "leadsto";
*)

(*
|- !X st Pr.
    (!p q.   (p ENSURES q)(CONS st Pr) ==> X p q(CONS st Pr)) /\
    (!p r q. (p ENSURES r)(CONS st Pr) /\
             (r LEADSTO q)(CONS st Pr) /\ X r q(CONS st Pr)
                                       ==> X p q(CONS st Pr)) /\
    (!P q.   (!p. p In P ==> (p LEADSTO q)(CONS st Pr)) /\
             (!p. p In P ==> X p q(CONS st Pr))
                                       ==> X (LUB P) q (CONS st Pr))

    ==> (!p q. (p LEADSTO q)(CONS st Pr) ==> X p q(CONS st Pr))
*)
local
open Rsyntax
val LEADSTO_thm34b = theorem"leadsto""LEADSTO_thm34b"
in
fun LEADSTO_INDUCT0_TAC (hyp,conc) =
 let
  val {Bvar= p,  Body= qstPrLX} = dest_forall     conc;
  val {Bvar= q,  Body=  stPrLX} = dest_forall  qstPrLX;
  val {Bvar= st, Body=    PrLX} = dest_forall   stPrLX;
  val {Bvar= Pr, Body=      LX} = dest_forall     PrLX;
  val {ant = L,  conseq=     X} = dest_imp          LX;

  val PrX           = mk_abs{Bvar= Pr, Body=         X};
  val stPrX         = mk_abs{Bvar= st, Body=       PrX};
  val qstPrX        = mk_abs{Bvar= q,  Body=     stPrX};
  val pqstPrX       = mk_abs{Bvar= p,  Body=    qstPrX};

  val RbX = (--`(^p ENSURES ^q)(CONS ^st ^Pr) ==> ^X`--);

  val r     = variant (free_varsl (conc::hyp)) (--`r:'a->bool`--);
  val RtL1  = (--`(^p ENSURES ^r) (CONS ^st ^Pr)`--);
  val RtL2  = (--`(^r LEADSTO ^q) (CONS ^st ^Pr)`--);
  val RtX1  = subst[{residue= r, redex= p}] X;

  val P     = variant (free_varsl (conc::hyp)) (--`P:('a->bool)->bool`--);
  val p'    = variant (free_varsl (conc::hyp)) (--`p:'a->bool`--);
  val RdX1  = subst[{residue= p', redex= p}] L;
  val RdX1' = (--`!^p'. ^p' In ^P ==> ^RdX1`--);
  val RdX2  = subst[{residue= p', redex= p}] X;
  val RdX2' = (--`!^p'. ^p' In ^P ==> ^RdX2`--);
  val RdX3  = subst[{residue= --`LUB ^P`--, redex= p}] X;

  val Xb    = (--`!^p ^q ^st ^Pr. ^RbX`--);
  val Xt    = (--`!^p ^r ^q ^st ^Pr. (^RtL1 /\ ^RtL2 /\ ^RtX1) ==> ^X`--);
  val Xd    = (--`!^P ^q ^st ^Pr. ^RdX1' /\ ^RdX2' ==> ^RdX3`--);

  val Pr'   = variant (free_varsl (conc::hyp)) (--`Pr:('a->'a)list`--);
  val X'    = subst[{residue= Pr', redex= --`CONS ^st ^Pr`--}] X;
  val PrX'         = mk_abs{Bvar= Pr, Body=        X'};
  val qPrX'        = mk_abs{Bvar= q,  Body=      PrX'};
  val pqPrX'       = mk_abs{Bvar= p,  Body=     qPrX'};
 in
   ([(hyp, Xb),(hyp, Xt),(hyp, Xd)],
     (fn [thmb,thmt,thmd] =>
           MP (BETA_RULE (SPEC pqPrX' LEADSTO_thm34b))
              (CONJ thmb (CONJ thmt thmd))))
 end handle e => raise HOL_ERR { origin_structure = "leadsto_induct0",
                             origin_function  = "LEADSTO_INDUCT0_TAC",
			     message          = "Can't apply induction"}
end;


(* Emacs editor information
|  Local variables:
|  mode:sml
|  sml-prog-name:"hol90"
|  End:
*)
