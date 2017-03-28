(************************ cond.sml **************************************)
(*                                                                      *)
(* Author: Ralf Reetz                                                   *)
(* Date:   29.8.1994                                                    *)
(*                                                                      *)
(* Description:                                         	        *)
(*                                                                      *)
(*   see cond.sig                                                       *)
(*                                                                      *)
(* Used files:     cond.sig                                             *)
(* Used modules:                                                        *)
(* Used theories:                                                       *)
(* Used libraries:                                                      *)
(*                                                                      *)
(************************************************************************)

structure  cond : COND =
struct

open Rsyntax;  (* use records *)

(*--------------------- RATOR_COND ----------------------------------------*)

val RATOR_COND_thm =
  prove(--`!f:'a->'b.!A x y.(f (A => x|y)) = (A => f x|f y)`--,
   REPEAT GEN_TAC THEN BOOL_CASES_TAC (--`A:bool`--) THEN REWRITE_TAC []);

(*--- FILTER ---*)

fun FILTER_RATOR_COND_CONV filter t =
 let
  fun error () =
   raise HOL_ERR
   {message          = ("term\n"^(term_to_string t)^
                       "\n has not the form: f (A -> x|y)"),
    origin_function  = "RATOR_COND_CONV",
    origin_structure = "cond"}
 in
  if is_comb t then
   let
    val {Rator = f, Rand = Axy} = dest_comb t
   in
    if is_cond Axy then
     if filter f then
      let
       val {cond = A, larm = x, rarm = y} = dest_cond Axy
      in
       ISPECL [f,A,x,y] RATOR_COND_thm
      end
     else
      raise HOL_ERR
      {message = ("the supplied filter is not true for:\n"^
                 (term_to_string f)),
       origin_function = "FILTER_RATOR_COND_CONV",
       origin_structure = "cond"}
    else
     error()
   end
  else
   error()
 end;

fun FILTER_RATOR_COND_RULE filter =
  CONV_RULE(TOP_DEPTH_CONV (FILTER_RATOR_COND_CONV filter));

fun FILTER_RATOR_COND_TAC filter =
  CONV_TAC(TOP_DEPTH_CONV (FILTER_RATOR_COND_CONV filter));

(*--- ---*)

val RATOR_COND_CONV = FILTER_RATOR_COND_CONV (fn t => true);

val RATOR_COND_RULE =
  CONV_RULE(TOP_DEPTH_CONV RATOR_COND_CONV);

val RATOR_COND_TAC =
  CONV_TAC(TOP_DEPTH_CONV RATOR_COND_CONV);

(*----------------- RAND_COND ----------------------------------------------*)

val RAND_COND_thm =
  prove(--`!A.!f:'a->'b.!g.!x.(A => f|g) x = (A => f x|g x)`--,
    REPEAT GEN_TAC THEN BOOL_CASES_TAC (--`A:bool`--) THEN REWRITE_TAC []);

(*--- FILTER ---*)

fun FILTER_RAND_COND_CONV filter t =
 let
  fun error () =
   HOL_ERR
   {message          = ("term\n"^(term_to_string t)^
                       "\nhas not the form: (A => f|g) x"),
    origin_function  = "FILTER_RAND_COND_CONV",
    origin_structure = "cond"}
 in
  if is_comb t then
   let
    val {Rator = Afg, Rand = x} = dest_comb t
   in
    if is_cond Afg then
     if filter x then
      let
       val {cond = A, larm = f, rarm = g} = dest_cond Afg
      in
       ISPECL [A,f,g,x] RAND_COND_thm
      end
     else
      raise HOL_ERR
      {message = ("the supplied filter is not true for\n"^
                 (term_to_string x)^"\n"),
       origin_function = "FILTER_RAND_COND_CONV",
       origin_structure = "cond"}
    else
     raise (error())
   end
  else
   raise (error())
 end

fun FILTER_RAND_COND_RULE filter =
  CONV_RULE(DEPTH_CONV (FILTER_RAND_COND_CONV filter));

fun FILTER_RAND_COND_TAC filter =
  CONV_TAC(DEPTH_CONV (FILTER_RAND_COND_CONV filter));

(*--- ---*)

val RAND_COND_CONV = FILTER_RAND_COND_CONV (fn t => true);

val RAND_COND_RULE =
 CONV_RULE(DEPTH_CONV RAND_COND_CONV);

val RAND_COND_TAC =
 CONV_TAC(DEPTH_CONV RAND_COND_CONV);

(*-------------------------- COND_RATOR ------------------------------------*)

val COND_RATOR_thm =
  prove(--`!f:'a->'b.!A x y.(A => f x|f y) = (f (A => x|y))`--,
    REPEAT GEN_TAC THEN BOOL_CASES_TAC (--`A:bool`--) THEN REWRITE_TAC []);

fun FILTER_COND_RATOR_CONV filter t = 
 let
  fun error () =
   HOL_ERR
   {origin_function  = "FILTER_COND_RATOR_CONV",
    origin_structure = "cond",
    message          = ("\n"^(term_to_string t)^
                       "\nhas not the form: A => f x|f y\n")}
 in
  if is_cond t then
   let
    val {cond = A, larm = fx, rarm = fy} = dest_cond t
   in
    if (is_comb fx) andalso (is_comb fy) then
     let
      val {Rator = f_left, Rand = x}  = dest_comb fx
      val {Rator = f_right, Rand = y} = dest_comb fy
     in
      if (f_left = f_right) then
       if filter f_left then
        ISPECL [f_left,A,x,y] COND_RATOR_thm
       else
        raise HOL_ERR
        {message = ("\nthe supplied filter is not true for\n\n"^
                   (term_to_string f_left)^"\n"),
         origin_function = "FILTER_COND_RATOR_CONV",
         origin_structure = "cond"}
      else
       raise (error())
     end
    else
     raise (error())
   end
  else
   raise (error())
 end;

fun FILTER_COND_RATOR_RULE filter =
  CONV_RULE(DEPTH_CONV (FILTER_COND_RATOR_CONV filter));

fun FILTER_COND_RATOR_TAC filter =
  CONV_TAC(DEPTH_CONV (FILTER_COND_RATOR_CONV filter));

(*--- ---*)

val COND_RATOR_CONV = FILTER_COND_RATOR_CONV (fn t => true);

val COND_RATOR_RULE =
  CONV_RULE(DEPTH_CONV COND_RATOR_CONV);

val COND_RATOR_TAC =
  CONV_TAC(DEPTH_CONV COND_RATOR_CONV);

(*-------------------------- COND_RAND ------------------------------------*)

val COND_RAND_thm =
  prove(--`!f:'a->'b.!g.!A x.(A => f x|g x) = ((A => f|g) x)`--,
    REPEAT GEN_TAC THEN BOOL_CASES_TAC (--`A:bool`--) THEN REWRITE_TAC []);

fun FILTER_COND_RAND_CONV filter t = 
 let
  fun error () =
   raise HOL_ERR
   {origin_function  = "FILTER_COND_RAND_CONV",
    origin_structure = "cond",
    message          = ((term_to_string t)^
                       "\nhas not the form: A => f x|g x\n")}
 in
  if is_cond t then
   let
    val {cond = A, larm = fx, rarm = gx} = dest_cond t
   in
    if (is_comb fx) andalso (is_comb gx) then
     let
      val {Rator = f, Rand = x1} = dest_comb fx
      val {Rator = g, Rand = x2} = dest_comb gx
     in
      if x1=x2 then
       if filter x1 then
        ISPECL [f,g,A,x1] COND_RAND_thm
       else
        raise HOL_ERR
        {message = ("the supplied filter is not true for\n"^
                   (term_to_string x1)^"\n"),
         origin_function = "FILTER_COND_RAND_CONV",
         origin_structure = "cond"}
      else
       raise (error())
     end
    else
     raise (error())
   end
  else
   raise (error())
 end;

fun FILTER_COND_RAND_RULE filter =
  CONV_RULE(DEPTH_CONV (FILTER_COND_RAND_CONV filter));

fun FILTER_COND_RAND_TAC filter =
  CONV_TAC(DEPTH_CONV (FILTER_COND_RAND_CONV filter));

(*--- ---*)

val COND_RAND_CONV = FILTER_COND_RAND_CONV (fn t => true);

val COND_RAND_RULE =
  CONV_RULE(DEPTH_CONV COND_RAND_CONV);

val COND_RAND_TAC =
  CONV_TAC(DEPTH_CONV COND_RAND_CONV);

(*------------------- COND_EQ ---------------------------------------------*)

val COND_EQ_thm =
  prove(--`!A:bool.!x:'a.!y:'a.!z:'a.((A => x|y) = z) = (A => x=z|y=z)`--,
   REPEAT GEN_TAC THEN BOOL_CASES_TAC (--`A:bool`--) THEN REWRITE_TAC []);

(*--- FILTER ---*)

fun FILTER_COND_EQ_CONV filter t =
 let
  fun error() =
   raise HOL_ERR
   {message          = ("term\n"^(term_to_string t)^
                       "\n has not the form: (A => x|y) = z"),
    origin_function  = "FILTER_COND_EQ_CONV",
    origin_structure = "cond"}
 in
  if (is_eq t) then
   let
    val {lhs = Axy, rhs = z} = dest_eq t
   in
    if is_cond Axy then
     if filter z then
      let
       val {cond = A, larm = x, rarm = y} = dest_cond Axy
      in
       ISPECL [A,x,y,z] COND_EQ_thm
      end
     else
      raise HOL_ERR
      {message = ("the supplied filter is not true for\n"^
                 (term_to_string z)^"\n"),
       origin_function = "FILTER_COND_EQ_CONV",
       origin_structure = "cond"}
    else
     error()
   end
  else
   error()
 end;

fun FILTER_COND_EQ_RULE filter =
  CONV_RULE (TOP_DEPTH_CONV (FILTER_COND_EQ_CONV filter));

fun FILTER_COND_EQ_TAC filter =
  CONV_TAC (TOP_DEPTH_CONV (FILTER_COND_EQ_CONV filter));

(*--- ---*)

val COND_EQ_CONV = FILTER_COND_EQ_CONV (fn t => true);

val COND_EQ_RULE =
 CONV_RULE (TOP_DEPTH_CONV COND_EQ_CONV);

val COND_EQ_TAC =
 CONV_TAC (TOP_DEPTH_CONV COND_EQ_CONV);

(*------------------- EQ_COND ---------------------------------------------*)

val EQ_COND_thm =
  prove(--`!A:bool.!x:'a.!y:'a.!z:'a.(A => x=z|y=z) = ((A => x|y) = z)`--,
   REPEAT GEN_TAC THEN BOOL_CASES_TAC (--`A:bool`--) THEN REWRITE_TAC []);

(*--- FILTER ---*)

fun FILTER_EQ_COND_CONV filter t =
 let
  fun error() =
   raise HOL_ERR
   {message          = ("term\n"^(term_to_string t)^
                       "\n has not the form: A => x=z|y=z\n"),
    origin_function  = "FILTER_EQ_COND_CONV",
    origin_structure = "cond"}
 in
  if (is_cond t) then
   let
    val {cond = A, larm = xz, rarm = yz} = dest_cond t
   in
    if (is_eq xz) andalso (is_eq yz) then
     let
      val {lhs = x, rhs = z1} = dest_eq xz
      val {lhs = y, rhs = z2} = dest_eq yz
     in
      if z1=z2 then
       if filter z1 then
        ISPECL [A,x,y,z1] EQ_COND_thm
       else
        raise HOL_ERR
        {message = ("the supplied filter is not true for\n"^
                   (term_to_string z1)^"\n"),
         origin_function  = "FILTER_EQ_COND_CONV",
         origin_structure = "cond"}
      else
       error()
     end
    else
     error()
   end
  else
   error()
 end;

fun FILTER_EQ_COND_RULE filter =
  CONV_RULE (TOP_DEPTH_CONV (FILTER_EQ_COND_CONV filter));

fun FILTER_EQ_COND_TAC filter =
  CONV_TAC (TOP_DEPTH_CONV (FILTER_EQ_COND_CONV filter));

(*--- ---*)

val EQ_COND_CONV = FILTER_EQ_COND_CONV (fn t => true);

val EQ_COND_RULE =
 CONV_RULE (TOP_DEPTH_CONV EQ_COND_CONV);

val EQ_COND_TAC =
 CONV_TAC (TOP_DEPTH_CONV EQ_COND_CONV);

(*---------------------- COND_bool -----------------------------------------*)

val COND_bool_thm1 =
    prove(--`!A B.(A => T|B) = (A\/B)`--,
    REPEAT GEN_TAC THEN BOOL_CASES_TAC (--`A:bool`--) THEN REWRITE_TAC []);

val COND_bool_thm2 =
    prove(--`!A B.(A => F|B) = (~A/\B)`--,
    REPEAT GEN_TAC THEN BOOL_CASES_TAC (--`A:bool`--) THEN REWRITE_TAC []);

val COND_bool_thm3 =
    prove(--`!A B.(A => B|T) = A ==> B`--,
    REPEAT GEN_TAC THEN BOOL_CASES_TAC (--`A:bool`--) THEN REWRITE_TAC []);

val COND_bool_thm4 =
    prove(--`!A B.(A => B|F) = A /\ B`--,
    REPEAT GEN_TAC THEN BOOL_CASES_TAC (--`A:bool`--) THEN REWRITE_TAC []);

val COND_bool_thm5 =
    prove(--`!A.(A => T|F) = A`--,
    GEN_TAC THEN BOOL_CASES_TAC (--`A:bool`--) THEN REWRITE_TAC []);

val COND_bool_thm6 =
    prove(--`!A.(A => F|T) = ~A`--,
    GEN_TAC THEN BOOL_CASES_TAC (--`A:bool`--) THEN REWRITE_TAC []);

val COND_bool_thm7 =
    prove(--`!A.(A => T|T) = T`--,
    GEN_TAC THEN BOOL_CASES_TAC (--`A:bool`--) THEN REWRITE_TAC []);

val COND_bool_thm8 =
    prove(--`!A.(A => F|F) = F`--,
    GEN_TAC THEN BOOL_CASES_TAC (--`A:bool`--) THEN REWRITE_TAC []);

fun COND_bool_CONV t =
 let
  fun error () =
   HOL_ERR
   {origin_function  = "COND_bool_CONV",
    origin_structure = "cond",
    message          = "term:\n"^(term_to_string t)^
    "\nis not a conditional with at least one of its arms being F or T\n"}
 in
  if (is_cond t) andalso ((type_of t) = (==`:bool`==)) then
   let
    val {cond = A, larm = l, rarm = r} = dest_cond t
    val F = (--`F`--)
    val T = (--`T`--)
   in
    if l=T then
     if r=T then
      SPEC A COND_bool_thm7
     else 
      if r=F then
       SPEC A COND_bool_thm5
      else
       SPECL [A,r] COND_bool_thm1
    else
     if l=F then
      if r=T then
       SPEC A COND_bool_thm6
      else
       if r=F then
        SPEC A COND_bool_thm8
       else
        SPECL [A,r] COND_bool_thm2
     else
      if r=T then
       SPECL [A,l] COND_bool_thm3
      else
       if r=F then
        SPECL [A,l] COND_bool_thm4
       else
        raise (error())
   end
  else
   raise (error())
 end;

val COND_bool_RULE =
  CONV_RULE (TOP_DEPTH_CONV COND_bool_CONV);

val COND_bool_TAC =
  CONV_TAC (TOP_DEPTH_CONV COND_bool_CONV);

(*----------------------- COND_COND ---------------------------------------*)

val COND_COND_thm1 =
  prove(--`!A (x:'a) y z.(A => (A => x|y)|z) = (A => x|z)`--,
  REPEAT GEN_TAC THEN BOOL_CASES_TAC (--`A:bool`--) THEN REWRITE_TAC []);

val COND_COND_thm2 =
  prove(--`!A (x:'a) y z.(A => (~A => x|y)|z) = (A => y|z)`--,
  REPEAT GEN_TAC THEN BOOL_CASES_TAC (--`A:bool`--) THEN REWRITE_TAC []);

fun COND_COND_CONV t =
 let
  fun error () =
   HOL_ERR
   {origin_function  = "COND_COND_CONV",
    origin_structure = "cond",
    message          = ("term:\n"^(term_to_string t)^
    "\nhas not the form: (A => (A x|y)|z) or (A => (~A => x|y)|z))\n")}
 in
  if is_cond t then
   let
    val {cond = A, larm = c2, rarm = z} = dest_cond t
   in
    if is_cond c2 then
     let
      val {cond = A', larm = x, rarm = y} = dest_cond c2
     in
      if A=A' then
       ISPECL [A,x,y,z] COND_COND_thm1
      else if (is_neg A')andalso(A=(dest_neg A')) then
       ISPECL [A,x,y,z] COND_COND_thm2
      else
       raise (error())
     end
    else
     raise (error())
   end
  else
   raise (error())
 end;

val COND_COND_RULE =
  CONV_RULE(DEPTH_CONV COND_COND_CONV);

val COND_COND_TAC =
  CONV_TAC(DEPTH_CONV COND_COND_CONV);

(*------------------------- SWAP_COND --------------------------------------*)

val SWAP_COND_thm =
    prove(--`!A B (x:'a) y z.(A => (B => x|y)|z) = (A/\B => x|(A => y|z))`--,
    REPEAT GEN_TAC THEN BOOL_CASES_TAC (--`A:bool`--) THEN REWRITE_TAC []);

fun SWAP_COND_CONV t =
 let
  fun error () =
   HOL_ERR
   {origin_function  = "SWAP_COND_CONV",
    origin_structure = "cond",
    message          = ("term:\n"^(term_to_string t)^
    "\nis not of the form: A => (B => x | y) | z\n")}
 in
  if is_cond t then
   let
    val {cond = A, larm = c2, rarm = z} = dest_cond t
   in
    if is_cond c2 then
     let
      val {cond = B, larm = x, rarm = y} = dest_cond c2
     in
      ISPECL [A,B,x,y,z] SWAP_COND_thm
     end
    else
     raise (error())
   end
  else
   raise(error())
 end; 

val SWAP_COND_RULE =
  CONV_RULE(TOP_DEPTH_CONV SWAP_COND_CONV);

val SWAP_COND_TAC =
  CONV_TAC(TOP_DEPTH_CONV SWAP_COND_CONV);

(*------------------------ COND_SUBS ---------------------------------------*)

val cond_subs_thm =
  prove
  (--`!x (f:'a) fT g gF.((x ==> (f=fT)) /\ (~x ==> (g=gF))) ==>
      ((x => f|g) = ( x => fT|gF))`--,
  REPEAT GEN_TAC THEN ASM_CASES_TAC (--`x:bool`--) THEN ASM_REWRITE_TAC []);

fun COND_SUBS_CONV t =
 if is_cond t then
  let 
   val tc = dest_cond t
   val x  = #cond tc
   val f  = #larm tc
   val g  = #rarm tc
   val xT = EQT_INTRO (ASSUME x)
   val xF = EQF_INTRO (ASSUME (mk_neg x))
   val fT = 
    DISCH x
    (RIGHT_CONV_RULE (ONCE_DEPTH_CONV COND_SUBS_CONV)
    (RIGHT_CONV_RULE(TOP_DEPTH_CONV COND_CONV)
    (SUBST_CONV [{var=x,thm=xT}] f f)))
   val res_fT = (#rhs(dest_eq(#conseq(dest_imp(concl fT)))))
   val gF =
    DISCH (mk_neg x)
    (RIGHT_CONV_RULE (ONCE_DEPTH_CONV COND_SUBS_CONV)
    (RIGHT_CONV_RULE(TOP_DEPTH_CONV COND_CONV)
    (SUBST_CONV [{var=x,thm=xF}] (#rarm tc) (#rarm tc))))
   val res_gF = (#rhs(dest_eq(#conseq(dest_imp(concl gF)))))
  in
   if (res_fT=f)andalso(res_gF=g) then
    raise HOL_ERR{message         ="Nothing has changed",
                  origin_function ="COND_SUBS_CONV",
                  origin_structure="cond"}
   else
    MP
    (ISPECL [x,f,res_fT,g,res_gF] cond_subs_thm)
    (CONJ fT gF)
  end
 else
  raise HOL_ERR{message         ="term is not a conditional",
                origin_function ="COND_SUBS_CONV",
                origin_structure="cond"};
   

val COND_SUBS_RULE = CONV_RULE (ONCE_DEPTH_CONV COND_SUBS_CONV);

val COND_SUBS_TAC = CONV_TAC (ONCE_DEPTH_CONV COND_SUBS_CONV);

(*-------------------- CHAIN_COND_CONV --------------------------------*)

val bool_COND_thm1 =
    prove(--`!A:'a.!B.(T => A|B) = A`--,
    REWRITE_TAC []);

val bool_COND_thm2 =
    prove(--`!A:'a.!B.(F => A|B) = B`--,
    REWRITE_TAC []);

(*
  substitutes the condition of the conditional term t by the right side of th
*)
fun SUBST_cond_CONV th t =
  RATOR_CONV(RATOR_CONV(RAND_CONV (fn te => th))) t;

fun CHAIN_COND_CONV cond_EQ_CONV t =
  if is_cond t then
    let
      val c               = dest_cond t
      val cond            = #cond c
      val larm            = #larm c
      val rarm            = #rarm c
      val solved_cond_thm = cond_EQ_CONV cond
      val solved_cond     = #rhs(dest_eq(concl solved_cond_thm))
    in
      if solved_cond = (--`T`--) then
        TRANS
        (SUBST_cond_CONV solved_cond_thm t)
        (ISPECL [larm,rarm] bool_COND_thm1)
      else 
        if solved_cond = (--`F`--) then
          if is_cond rarm then
            TRANS
             (TRANS
              (SUBST_cond_CONV solved_cond_thm t)
              (ISPECL [larm,rarm] bool_COND_thm2))
             (CHAIN_COND_CONV cond_EQ_CONV rarm)
          else
            TRANS
            (SUBST_cond_CONV solved_cond_thm t)
            (ISPECL [larm,rarm] bool_COND_thm2)
        else
          raise HOL_ERR{message
                      =("supplied cond_EQ_CONV couldn't solve the condition\n"
                       ^(term_to_string cond)),
                        origin_function ="CHAIN_COND_CONV",
                        origin_structure="cond"}   
    end
  else
    raise HOL_ERR{message         ="supplied term is not a conditional",
                  origin_function ="CHAIN_COND_CONV",
                  origin_structure="cond"};

(*------------ CHAIN_EQ_COND_CONV ----------------------------------------*)

val COND_CASES_mp_th1 =
  prove(--`!A.A ==> !(f:'a) g.(A => f|g) = f`--,
    EVERY [
      REPEAT GEN_TAC,
      DISCH_TAC,
      ASM_REWRITE_TAC []
    ]);
val COND_CASES_mp_th2 =
  prove(--`!g1 g2.(g1=g2) ==> !A (f:'a).(A => f|g1)=(A => f|g2)`--,
    EVERY [
      REPEAT GEN_TAC,
      DISCH_TAC,
      ASM_REWRITE_TAC []
    ]);
val COND_CASES_mp_th3 =
  prove(--`!A.~A ==> !g1 g2.(g1=g2) ==> !f:'a.(A => f|g1)=g2`--,
    EVERY [
      REPEAT GEN_TAC,
      DISCH_TAC,
      ASM_REWRITE_TAC [],
      REPEAT GEN_TAC,
      DISCH_TAC,
      ASM_REWRITE_TAC []
    ]);
val COND_CASES_mp_th4 =
  prove(--`!A t.t ==> (A ==> t)`--,
    EVERY [
      REPEAT GEN_TAC,
      DISCH_TAC,
      ASM_REWRITE_TAC []
    ]);
val COND_CASES_mp_th5 =
  prove(--`!(x:'b) xk.(x=xk) ==>
           !g1 g2.(g1=g2) ==> 
           !xi.((xk=xi)=F) ==> !f:'a.((x=xi) => f|g1)=g2`--,
    EVERY [
     REPEAT (REPEAT GEN_TAC THEN DISCH_TAC),
     ASM_REWRITE_TAC []
    ]);

fun CHAIN_COND_CASES_CONV x_EQ_CONV c t =
 let
  val {lhs = x, rhs = xk} = dest_eq c
  val mp_th1 = UNDISCH (ISPEC c COND_CASES_mp_th1)
  val mp_th2 = UNDISCH (ISPECL [x,xk] COND_CASES_mp_th5)
  (*
    Global Input:
      a term xk of the form --`xk`--
      a term c of the form --`x=xk`-- 
      a theorem mp_th1 of the form [x=xk]|-!f g.((x=xk)=>f|g)=f,
      a theorem mp_th2 of the form [x=xk]|-!
    Input:
      a term --`x=x1 => f1|x=x2 => f2|...|x=xm => fm|fn`--
    Output:
      a theorem with the given term on the left and the following term
      on the right side of an equation: a simplified t with assumputon [x=xk]
  *)
  fun SUBST_condT_CONV t =
   if is_cond t then
    let
     val t1 = dest_cond t
    in
     if (#cond t1)=c then
      ISPECL [#larm t1,#rarm t1] mp_th1
     else
      let
       val g1g2_th = SUBST_condT_CONV (#rarm t1)
       val xi      = #rhs(dest_eq (#cond t1))
       val eq_th   = x_EQ_CONV (mk_eq{lhs=xk,rhs=xi})
       (* observe, that because of ((#cond t1)=c)=false, the result of
          x_EQ_CONV here should be F *)
      in
       ISPEC (#larm t1)
       (MP
       (ISPEC xi
        (MP(ISPECL [#rarm t1,#rhs(dest_eq(concl g1g2_th))] mp_th2) g1g2_th))
       eq_th)
      end
    end
   else
    UNDISCH (MP (ISPECL [c,mk_eq{lhs=t,rhs=t}] COND_CASES_mp_th4) (REFL t))
  val mp_th3 = (UNDISCH (ISPEC c COND_CASES_mp_th3))
  (*
    Global Input:
      a term c of the form --`A`-- 
      a theorem mp_th3 [~A]|-!g1 g2.(g1=g2) ==> !f.(A=>f|g1)=g2 
    Input:
      a term --`A1 => f1|A2 => f2|...|Am => fm|fn`--
    Output:
      a theorem with the given term on the left and the following term
      on the right side of an equation:
      if any Ai of the given term is A, then a simplified term with
      assumption [~A], else the term itself
  *)
  fun SUBST_condF_CONV t =
   if is_cond t then
    let
     val t1  = dest_cond t
     val th1 = SUBST_condF_CONV (#rarm t1)
    in
     if (#cond t1)=c then
      ISPEC (#larm t1)
      (MP
      (ISPECL [#rarm t1,#rhs(dest_eq(concl th1))] mp_th3)
      th1)
     else
      ISPECL [#cond t1,#larm t1]
       (MP
       (ISPECL [#rarm t1,#rhs(dest_eq(concl th1))] COND_CASES_mp_th2)
       th1)
    end
   else
    UNDISCH 
    (MP (ISPECL [mk_neg c,mk_eq{lhs=t,rhs=t}] COND_CASES_mp_th4) (REFL t))
 in
  CONJ
   (DISCH c (SUBST_condT_CONV t))
   (DISCH (mk_neg c) (SUBST_condF_CONV t))
 end;

(*----------------------- COND_EQ_COND_TAC --------------------------------*)

val COND_EQ_COND_TAC =
 let
  val th = prove(--`
         
           (
            (~t1 /\ ~t4 ==> (t3=t6))
            /\ 
            (t1 /\ t4 ==> (t2=t5))
            /\
            (t1=t4)
           ) 
           ==>
           ((t1 => t2|t3) = (t4 => t5|(t6:'a)))
            
           `--,
           EVERY [
            STRIP_TAC
            ,
            POP_ASSUM (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th]) THEN
            ASSUME_TAC th)
            ,
            ASM_CASES_TAC (--`t4:bool`--) THEN ASM_REWRITE_TAC [] THEN
            EVERY [
             RES_TAC,
             ASM_REWRITE_TAC []
            ]
           ]) 
  val tac = MATCH_MP_TAC th
 in
  tac THEN REPEAT STRIP_TAC
 end;

end; (* struct *)

(* preparing some examples in /help/*.doc

load_library_in_place (find_library "arith");

val th = prove(--`~(SUC (A => (SUC (B => 1|2))|3) = 0)`--,
  BOOL_CASES_TAC (--`A:bool`--) THEN
  BOOL_CASES_TAC (--`B:bool`--) THEN
  CONV_TAC ARITH_CONV);

th;

RATOR_COND_RULE th;
FILTER_RATOR_COND_RULE (fn t => #Name(dest_const t) = "SUC") th;

val th = prove(--`~(\x.~x) (T => (\x.x) (F => F|T)|F)`--,
 EVERY [
  REWRITE_TAC [],
  BETA_TAC,
  REWRITE_TAC []
 ]);

FILTER_RATOR_COND_RULE (fn t => (--`\x:bool.x`--) = t) it;

th;

val th = prove(--`~(((A => SUC|(\x.x+2)) 3) = ((A => SUC|(\x.x+2)) 5))`--,
  BOOL_CASES_TAC (--`A:bool`--) THEN
  BOOL_CASES_TAC (--`B:bool`--) THEN
  REWRITE_TAC [] THEN BETA_TAC THEN
  CONV_TAC ARITH_CONV);

th;

RAND_COND_RULE th;

val th = prove(--`~((A => (B => (C => 5|6)|7)|8) = 0)`--,
  BOOL_CASES_TAC (--`A:bool`--) THEN
  BOOL_CASES_TAC (--`B:bool`--) THEN
  BOOL_CASES_TAC (--`C:bool`--) THEN
  REWRITE_TAC [] THEN
  CONV_TAC ARITH_CONV);

SWAP_COND_RULE th;

val th = prove(--`~((A => 5| ((B => 5|6) = 5) => 7|8) = 6)`--,
  BOOL_CASES_TAC (--`A:bool`--) THEN
  BOOL_CASES_TAC (--`B:bool`--) THEN
  REWRITE_TAC [] THEN
  CONV_TAC ARITH_CONV);

FILTER_COND_EQ_RULE (fn t => t=(--`5`--))  th;

*)
