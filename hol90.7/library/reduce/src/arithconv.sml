(*===========================================================================
== LIBRARY:     reduce (part II)                                           ==
==                                                                         ==
== DESCRIPTION: Conversions to reduce arithmetic constant expressions      ==
==                                                                         ==
== AUTHOR:      John Harrison                                              ==
==              University of Cambridge Computer Laboratory                ==
==              New Museums Site                                           ==
==              Pembroke Street                                            ==
==              Cambridge CB2 3QG                                          ==
==              England.                                                   ==
==                                                                         ==
==              jrh@cl.cam.ac.uk                                           ==
==                                                                         ==
== DATE:        18th May 1991                                              ==
==                                                                         ==
== TRANSLATOR:  Kim Dam Petersen (kimdam@tfl.dk)                           ==
============================================================================*)

functor Arithconv_funct (structure Dest : Dest_sig) : Arithconv_sig =
struct

fun failwith function = raise HOL_ERR{origin_structure = "Arithconv",
                                      origin_function = function,
                                      message = ""};

open Dest;
open Rsyntax;
val num_ty   = mk_type{Tyop= "num", Args= []};
val bool_ty  = mk_type{Tyop= "bool", Args= []};
val fun_ty   = fn (op_ty,arg_ty) => mk_type{Tyop="fun", Args=[op_ty,arg_ty]};
val b_b_ty   = fun_ty(bool_ty,bool_ty);
val b_b_b_ty = fun_ty(bool_ty,b_b_ty);
val n_b_ty   = fun_ty(num_ty,bool_ty);
val n_n_b_ty = fun_ty(num_ty,n_b_ty);
val xv       = mk_var {Name= "x", Ty=num_ty};
val yv       = mk_var {Name= "y", Ty=num_ty};
val zv       = mk_var {Name= "z", Ty=num_ty};
val pv       = mk_var {Name= "p", Ty=num_ty};
val qv       = mk_var {Name= "q", Ty=num_ty};
val rv       = mk_var {Name= "r", Ty=num_ty};
val beqop    = mk_const{Name= "=", Ty= b_b_b_ty};
val neqop    = mk_const{Name= "=", Ty= n_n_b_ty};
val ltop     = mk_const{Name= "<", Ty= n_n_b_ty};
val gtop     = mk_const{Name= ">", Ty= n_n_b_ty};
val leop     = mk_const{Name= "<=", Ty= n_n_b_ty};
val geop     = mk_const{Name= ">=", Ty= n_n_b_ty};

(*-----------------------------------------------------------------------*)
(* provelt x y = |- [x] < [y], if true, else undefined.                  *)
(*-----------------------------------------------------------------------*)

infix :==
fun r :== v = (r := v; v)

val provelt =
  let val ltstep = prove((--`!x. (z = SUC y) ==> (x < y) ==> (x < z)`--),
			 GEN_TAC THEN DISCH_THEN SUBST1_TAC THEN
			 MATCH_ACCEPT_TAC (theorem "prim_rec" "LESS_SUC"))
      and ltbase  = prove((--`(y = SUC x) ==> (x < y)`--),
			  DISCH_THEN SUBST1_TAC THEN
			  MATCH_ACCEPT_TAC
			  (theorem "prim_rec" "LESS_SUC_REFL"))
      and bistep = prove((--`(SUC x < SUC y) = (x < y)`--),
			 MATCH_ACCEPT_TAC
			 (theorem "arithmetic" "LESS_MONO_EQ"))
      and bibase = prove((--`!x. 0 < (SUC x)`--),
			 MATCH_ACCEPT_TAC (theorem "prim_rec" "LESS_0"))
      and rhs = (--`x < y`--)
      and Lo = (--`$< 0`--)
  in
  fn (x:int) => fn (y:int) =>
    let val xn = term_of_int x
	and yn = term_of_int y
    in
        if 4*(y - x) < 5*x then
         let val x' = x + 1
	     val xn' = term_of_int x'
	     val step = SPEC xn ltstep
	     val z = ref x'
	     val zn = ref xn'
	     val zn' = ref xn'
	     val th = ref (MP (INST [{residue= xn, redex= xv},
				     {residue= xn', redex= yv}] ltbase)
			   (num_CONV xn'))
	 in
	     while (!z) < y do
		 (zn':=term_of_int(z:==(!z)+1),
		  th := MP (MP (INST [{residue= !zn, redex= yv},
				      {residue= !zn', redex= zv}] step)
			    (num_CONV (!zn'))) (!th),
		  zn:=(!zn'));
		 (!th)
	 end
        else
         let val lhs = mk_comb{Rator= mk_comb{Rator= ltop, Rand= xn}, Rand= yn}
	     val pat = mk_comb{Rator= mk_comb{Rator= beqop, Rand= lhs},
			       Rand= rhs}
	     val w = ref x
	     val z = ref y
	     val wn = ref xn
	     val zn = ref yn
	     val th = ref (REFL lhs)
	 in
	     while ((!w) > 0) do
		 (th :=
		  let val tran = TRANS (SUBST [{thm= num_CONV (!wn),
						var= xv},
					       {thm= num_CONV (!zn),
						var= yv}] pat (!th))
		  in tran (INST[{residue= (wn:==term_of_int(w:==((!w)-1))),
				 redex= xv},
				{residue= (zn:==term_of_int(z:==((!z)-1))),
				 redex= yv}] bistep)
		  end);
		 EQ_MP (SYM (TRANS (!th) (AP_TERM Lo (num_CONV (!zn)))))
		 (SPEC (term_of_int((!z)-1)) bibase)
	 end
    end
  end;

(*-----------------------------------------------------------------------*)
(* NEQ_CONV "[x] = [y]" = |- ([x] = [y]) = [x=y -> T | F]                *)
(*-----------------------------------------------------------------------*)

val NEQ_CONV =
let val eq1 = prove
    ((--`(x < y) ==> ((x = y) = F)`--),
	ONCE_REWRITE_TAC[] THEN
	MATCH_ACCEPT_TAC (theorem "prim_rec" "LESS_NOT_EQ"))
    and eq2 = prove
	((--`(y < x) ==> ((x = y) = F)`--),
	    ONCE_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[EQ_SYM_EQ] THEN
	    MATCH_ACCEPT_TAC (theorem "prim_rec" "LESS_NOT_EQ"))
in
  fn tm =>
  (let val [xn,yn] = dest_op neqop tm
       val x = int_of_term xn
       and y = int_of_term yn
   in
       if x = y then EQT_INTRO (REFL xn)
       else if x < y then MP (INST [{residue= xn, redex= xv},
				    {residue= yn, redex= yv}] eq1)
	   (provelt x y)
       else MP (INST [{residue= xn, redex= xv},
		      {residue= yn, redex= yv}] eq2)
	   (provelt y x)
   end) handle _ => failwith "NEQ_CONV"
end;

(*-----------------------------------------------------------------------*)
(* LT_CONV "[x] < [y]" = |- ([x] < [y]) = [x<y -> T | F]                 *)
(*-----------------------------------------------------------------------*)

val LT_CONV =
let val lt1 = prove((--`!x. (x < x) = F`--),
		    REWRITE_TAC[theorem "prim_rec" "LESS_REFL"])
    and lt2 = prove((--`(y < x) ==> ((x < y) = F)`--),
		    PURE_ONCE_REWRITE_TAC[EQ_CLAUSES] THEN
		    REPEAT DISCH_TAC THEN
		    IMP_RES_TAC (theorem "arithmetic" "LESS_ANTISYM"))
in
  fn tm =>
  (let val [xn,yn] = dest_op ltop tm
       val x = int_of_term xn
       and y = int_of_term yn
   in
       if x < y then EQT_INTRO (provelt x y)
       else if x = y then SPEC xn lt1
       else MP (INST [{residue= xn, redex= xv},
		      {residue= yn, redex= yv}] lt2)
	   (provelt y x)
   end) handle _ => failwith "LT_CONV"
end;

(*-----------------------------------------------------------------------*)
(* GT_CONV "[x] > [y]" = |- ([x] > [y]) = [x>y -> T | F]                 *)
(*-----------------------------------------------------------------------*)

val GT_CONV =
let val gt1 = prove((--`!x. (x > x) = F`--),
		    REWRITE_TAC[theorem "prim_rec" "LESS_REFL",
				definition "arithmetic" "GREATER"])
    and gt2 = prove((--`(x < y) ==> ((x > y) = F)`--),
		    PURE_REWRITE_TAC
		    [EQ_CLAUSES, definition "arithmetic" "GREATER"]
		    THEN REPEAT DISCH_TAC THEN
		    IMP_RES_TAC (theorem "arithmetic" "LESS_ANTISYM"))
    and gt3 = prove((--`(y < x) ==> ((x > y) = T)`--),
		    DISCH_THEN (SUBST1_TAC o SYM o EQT_INTRO) THEN
		    MATCH_ACCEPT_TAC (definition "arithmetic" "GREATER"))
in
  fn tm =>
  (let val [xn,yn] = dest_op gtop tm
       val x = int_of_term xn
       and y = int_of_term yn
   in
       if x = y then SPEC xn gt1
       else if x < y then MP (INST [{residue= xn, redex= xv},
				    {residue= yn, redex= yv}] gt2)
	   (provelt x y)
       else MP (INST [{residue= xn, redex= xv},
		      {residue= yn, redex= yv}] gt3)
	   (provelt y x)
   end) handle _ => failwith "GT_CONV"
end;

(*-----------------------------------------------------------------------*)
(* LE_CONV "[x] <= [y]" = |- ([x]<=> [y]) = [x<=y -> T | F]              *)
(*-----------------------------------------------------------------------*)

val LE_CONV =
let val le1 = prove((--`!x. (x <= x) = T`--),
		    REWRITE_TAC[theorem "arithmetic" "LESS_EQ_REFL"])
    and le2 = prove((--`(x < y) ==> ((x <= y) = T)`--),
		    DISCH_THEN (ACCEPT_TAC o EQT_INTRO o MATCH_MP
				(theorem "arithmetic" "LESS_IMP_LESS_OR_EQ")))
    and le3 = prove((--`(y < x) ==> ((x <= y) = F)`--),
		    PURE_ONCE_REWRITE_TAC[EQ_CLAUSES] THEN
		    REPEAT DISCH_TAC THEN
		    IMP_RES_TAC (theorem "arithmetic" "LESS_EQ_ANTISYM"))
in
  fn tm =>
  (let val [xn,yn] = dest_op leop tm
       val x = int_of_term xn
       and y = int_of_term yn
   in
       if x = y then SPEC xn le1
       else if x < y then MP (INST [{residue= xn, redex= xv},
				    {residue= yn, redex= yv}] le2)
	   (provelt x y)
       else MP (INST [{residue= xn, redex= xv},
		      {residue= yn, redex= yv}] le3)
	   (provelt y x)
   end) handle _ => failwith "LE_CONV"
end;

(*-----------------------------------------------------------------------*)
(* GE_CONV "[x] >= [y]" = |- ([x] >= [y]) = [x>=y -> T | F]              *)
(*-----------------------------------------------------------------------*)

val GE_CONV =
let val ge1 = prove((--`!x. (x >= x) = T`--),
		    REWRITE_TAC[definition "arithmetic" "GREATER_OR_EQ"])
    and ge2 = prove((--`(y < x) ==> ((x >= y) = T)`--),
		    DISCH_TAC THEN
		    ASM_REWRITE_TAC[definition "arithmetic" "GREATER_OR_EQ",
				    definition "arithmetic" "GREATER"])
    and ge3 = prove((--`(x < y) ==> ((x >= y) = F)`--),
		    PURE_REWRITE_TAC (EQ_CLAUSES ::
				      (map (definition "arithmetic")
				       ["GREATER_OR_EQ", "GREATER"])) THEN
		    PURE_ONCE_REWRITE_TAC[EQ_SYM_EQ] THEN
		    REPEAT STRIP_TAC THEN
		    IMP_RES_TAC (PURE_REWRITE_RULE
				 [definition "arithmetic" "LESS_OR_EQ"]
				 (theorem "arithmetic" "LESS_EQ_ANTISYM")))
in
  fn tm =>
  (let val [xn,yn] = dest_op geop tm
       val x = int_of_term xn
       and y = int_of_term yn
   in
       if x = y then SPEC xn ge1
       else if x < y then MP (INST [{residue= xn, redex= xv},
				    {residue= yn, redex= yv}] ge3)
	   (provelt x y)
       else MP (INST [{residue= xn, redex= xv},
		      {residue= yn, redex= yv}] ge2)
	   (provelt y x)
   end) handle _ => failwith "GE_CONV"
end;

(*-----------------------------------------------------------------------*)
(* SUC_CONV "SUC [x]" = |- SUC [x] = [x+1]                               *)
(*-----------------------------------------------------------------------*)

val SUC_CONV =
  let val sucop = (--`SUC`--) in
      fn tm =>
      (let val [xn] = dest_op sucop tm in
	   SYM (num_CONV (term_of_int (1 + (int_of_term xn))))
       end) handle _ => failwith "SUC_CONV"
  end;

(*-----------------------------------------------------------------------*)
(* PRE_CONV "PRE [n]" = |- PRE [n] = [n-1]                               *)
(*-----------------------------------------------------------------------*)

val PRE_CONV =
  let val preop = (--`PRE`--)
      and zero = (--`0`--)
      and spree = prove((--`(x = SUC y) ==> (PRE x = y)`--),
			DISCH_TAC THEN
			ASM_REWRITE_TAC[theorem "prim_rec" "PRE"])
      and szero = prove((--`PRE 0 = 0`--),
			REWRITE_TAC[theorem "prim_rec" "PRE"])
  in
  fn tm =>
  (let val [xn] = dest_op preop tm
   in
       if xn = zero then szero
       else MP (INST[{residue= xn,
		      redex= xv},
		     {residue= term_of_int((int_of_term xn) - 1),
		      redex= yv}] spree)
	   (num_CONV xn)
   end) handle _ => failwith "PRE_CONV"
end;

(*-----------------------------------------------------------------------*)
(* SBC_CONV "[x] - [y]" = |- ([x] - [y]) = [x - y]                       *)
(*-----------------------------------------------------------------------*)

val SBC_CONV =
let val subm = prove((--`(x < y) ==> (x - y = 0)`--),
		     PURE_ONCE_REWRITE_TAC[theorem "arithmetic" "SUB_EQ_0"]
		     THEN MATCH_ACCEPT_TAC
		     (theorem "arithmetic" "LESS_IMP_LESS_OR_EQ"))
    and step = prove((--`(SUC x) - (SUC y) = x - y`--),
		     MATCH_ACCEPT_TAC (theorem "arithmetic" "SUB_MONO_EQ"))
    and base1 = prove((--`!x. x - 0 = x`--),
		      REWRITE_TAC[theorem "arithmetic" "SUB_0"])
    and base2 = prove((--`!x. x - x = 0`--),
                    MATCH_ACCEPT_TAC(theorem "arithmetic" "SUB_EQUAL_0"))
    and less0 = prove((--`!x. 0 < SUC x`--),
		      REWRITE_TAC[theorem "prim_rec" "LESS_0"])
    and swap = prove((--`(x - z = y) ==> (0 < y) ==> (x - y = z)`--),
		     let val [sub_less_0, sub_sub, less_imp_less_or_eq,
			      add_sym, add_sub] =
			 map (theorem "arithmetic")
			 ["SUB_LESS_0", "SUB_SUB", "LESS_IMP_LESS_OR_EQ",
			  "ADD_SYM", "ADD_SUB"]
		     in
			 DISCH_THEN (SUBST1_TAC o SYM) THEN
			 PURE_ONCE_REWRITE_TAC
			 [SYM (SPEC_ALL sub_less_0)] THEN
			 DISCH_THEN (SUBST1_TAC o SPEC (--`x:num`--) o
				     MATCH_MP sub_sub o
				     MATCH_MP less_imp_less_or_eq) THEN
			 PURE_ONCE_REWRITE_TAC [add_sym] THEN
			 PURE_ONCE_REWRITE_TAC[add_sub] THEN REFL_TAC
		     end)
    and lop = (--`$< 0`--)
    and minusop = (--`$-`--)
    and rhs = (--`x - y`--)
    fun sprove (x:int) (y:int) =
      let val xn = term_of_int x
	  and yn = term_of_int y
	  val lhs = mk_comb{Rator= mk_comb{Rator= minusop, Rand= xn}, Rand= yn}
	  val pat = mk_comb{Rator= mk_comb{Rator= neqop, Rand= lhs}, Rand= rhs}
	  val w = ref x
	  val z = ref y
	  val wn = ref xn
	  val zn = ref yn
	  val th = ref (REFL lhs)
      in
	  while ((!z) > 0) do
	      (th :=
	       let val tran = TRANS (SUBST [{thm= num_CONV (!wn), var= xv},
					    {thm= num_CONV (!zn), var= yv}]
				     pat (!th))
	       in
		   tran (INST [{residue= (wn :== term_of_int(w:==((!w)-1))),
				redex= xv},
			       {residue= (zn :== term_of_int(z:==((!z)-1))),
				redex= yv}] step)
	       end);
	      TRANS (!th) (SPEC (!wn) base1)
      end
in
  fn tm =>
  (let val [xn,yn] = dest_op minusop tm
       val x = int_of_term xn
       and y = int_of_term yn
   in
       if x < y then MP (INST[{residue= xn, redex= xv},
			      {residue= yn, redex= yv}] subm)
	   (provelt x y)
       else if y = 0 then SPEC xn base1
       else if x = y then SPEC xn base2
       else if y < (x - y) then sprove x y
       else
	   let val z = x - y
	       val zn = term_of_int z
	   in
	       MP (MP
		   (INST[{residue= xn, redex= xv},
			 {residue= yn, redex= yv},
			 {residue= zn, redex= zv}] swap)
		   (sprove x z))
			   (EQ_MP (AP_TERM lop (SYM (num_CONV yn)))
			    (SPEC (term_of_int (y-1)) less0))
	   end
   end) handle _ => failwith "SBC_CONV"
end;

(*-----------------------------------------------------------------------*)
(* ADD_CONV "[x] + [y]" = |- [x] + [y] = [x+y]                           *)
(*-----------------------------------------------------------------------*)

val ADD_CONV =
let val subadd =
    prove ((--`(z - y = x) ==> 0 < x ==> (x + y = z)`--),
	   DISCH_THEN (SUBST1_TAC o SYM) THEN
	   PURE_ONCE_REWRITE_TAC[SYM (SPEC_ALL (theorem "arithmetic"
						"SUB_LESS_0"))] THEN
	   DISCH_THEN (SUBST1_TAC o MATCH_MP
		       (theorem "arithmetic" "SUB_ADD") o
		       MATCH_MP (theorem "arithmetic"
				 "LESS_IMP_LESS_OR_EQ")) THEN
	   REFL_TAC)
    and [raz, laz] =
	CONJUNCTS(prove((--`(!x. x + 0 = x) /\ (!y. 0 + y = y)`--),
			REWRITE_TAC[definition "arithmetic" "ADD",
				    theorem "arithmetic" "ADD_0"]))
    and lo = prove((--`!n. 0 < SUC n`--),
		   MATCH_ACCEPT_TAC(theorem "prim_rec" "LESS_0"))
    and plusop = (--`$+`--)
    and minusop = (--`$-`--)
    and lop = (--`$< 0`--)
in
  fn tm =>
  (let val [xn,yn] = dest_op plusop tm
       val x = int_of_term xn
       and y = int_of_term yn
   in
       if x = 0 then SPEC yn laz
       else if y = 0 then SPEC xn raz
       else
	   let val zn = term_of_int(x + y)
	       val p1 = SBC_CONV
		   (mk_comb{Rator= mk_comb{Rator= minusop,
					   Rand= zn},
			    Rand= yn})
	       and p2 = EQ_MP (AP_TERM lop (SYM (num_CONV xn)))
		   (SPEC (term_of_int (int_of_term xn - 1)) lo)
	       and chain = INST[{residue= xn, redex= xv},
				{residue= yn, redex= yv},
				{residue= zn, redex= zv}] subadd
	   in
	       MP (MP chain p1) p2
	   end
   end) handle _ => failwith "ADD_CONV"
end;

(*-----------------------------------------------------------------------*)
(* MUL_CONV "[x] * [y]" = |- [x] * [y] = [x * y]                         *)
(*-----------------------------------------------------------------------*)

val MUL_CONV =
let val [mbase, mstep, mzero] =
    CONJUNCTS (prove ((--`(!y. 0 * y = 0) /\
		          (!y x. (SUC x) * y = (x * y) + y) /\
			  (!n. n * 0 = 0)`--),
    REWRITE_TAC[definition "arithmetic" "MULT",
                theorem "arithmetic" "MULT_0"]))
    and msym = prove((--`!m n. m * n = n * m`--),
		     MATCH_ACCEPT_TAC (theorem "arithmetic" "MULT_SYM"))
    and multop = (--`$*`--)
    and zero = (--`0`--)
    and plusop = (--`$+`--)
    and eqop = (--`$= :num->num->bool`--)
    fun mulpr (x:int) (y:int) =
	let val xn = term_of_int x
	    and yn = term_of_int y
	    val step = SPEC yn mstep
	    val pat =
		mk_comb{Rator=
			mk_comb{Rator= eqop,
				Rand= mk_comb{Rator= mk_comb{Rator= multop,
							     Rand= xv},
					      Rand= yn}},
			Rand=
			mk_comb{Rator= mk_comb{Rator= plusop, Rand= pv},
				Rand= yn}}
	    val w = ref 0
	    val wn = ref zero
	    val p = ref 0
	    val th = ref (SPEC yn mbase)
	in
	    while (!w) < x do
		(th := TRANS
                 (let val st = SPEC (!wn) step
		  in
		      SUBST [{thm=
			      SYM (num_CONV(wn:==term_of_int(w:==(!w)+1))),
			      var= xv},
			     {thm= (!th),
			      var= pv}] pat st
		  end)
		      (ADD_CONV (mk_comb{Rator= mk_comb{Rator= plusop,
							Rand= term_of_int(!p)},
					 Rand= yn}));
		      p := (!p) + y);
		(!th)
	end
in
  fn tm =>
  (let val [xn,yn] = dest_op multop tm
       val x = int_of_term xn
       and y = int_of_term yn
   in
       if x = 0 then SPEC yn mbase
       else if y = 0 then SPEC xn mzero
       else if x < y then mulpr x y
       else TRANS (SPECL [xn,yn] msym) (mulpr y x)
   end) handle _ => failwith "MUL_CONV"
end;

(*-----------------------------------------------------------------------*)
(* EXP_CONV "[x] EXP [y]" = |- [x] EXP [y] = [x ** y]                    *)
(*-----------------------------------------------------------------------*)

val EXP_CONV =
let val [ebase, estep] = CONJUNCTS
    (prove
     ((--`(!m. m EXP 0 = 1) /\ (!m n. m EXP (SUC n) = m * (m EXP n))`--),
      REWRITE_TAC[definition "arithmetic" "EXP"]))
    and expop = (--`EXP`--)
    and multop = (--`$*`--)
    and zero = (--`0`--)
    and ev = (--`e:num`--)
    and eqop = (--`$= :num->num->bool`--)
    and yv = (--`y:num`--)
in
    fn tm =>
    (let val [xn,yn] = dest_op expop tm
	 val x = int_of_term xn and y = int_of_term yn
	 and step = SPEC xn estep
	 val pat =
	     mk_comb{Rator= mk_comb{Rator= eqop,
				    Rand= mk_comb{Rator= mk_comb{Rator= expop,
								 Rand= xn},
						  Rand= yv}},
		     Rand= mk_comb{Rator= mk_comb{Rator= multop, Rand= xn},
				   Rand= ev}}
	 val z = ref 0
	 val zn = ref zero
	 val e = ref 1
	 val th = ref (SPEC xn ebase)
     in
	 while (!z) < y do
	     (th := TRANS
	      (let val st = SPEC (!zn) step
	       in
                   SUBST [{thm= SYM (num_CONV(zn:==term_of_int(z:==(!z)+1))),
			   var= yv},
                          {thm= (!th),
			   var= ev}] pat st
	       end)
		   (MUL_CONV (mk_comb{Rator= mk_comb{Rator= multop, Rand= xn},
				      Rand= term_of_int (!e)}));
		   e := x * (!e));
	     (!th)
     end) handle _ => failwith "EXP_CONV"
end;

(*-----------------------------------------------------------------------*)
(* DIV_CONV "[x] DIV [y]" = |- [x] DIV [y] = [x div y]                   *)
(*-----------------------------------------------------------------------*)

val DIV_CONV =
let val divt =
    prove((--`(q * y = p) ==> (p + r = x) ==> (r < y) ==> (x DIV y = q)`--),
	  REPEAT DISCH_TAC THEN
	  MATCH_MP_TAC (theorem "arithmetic" "DIV_UNIQUE") THEN
	  EXISTS_TAC (--`r:num`--) THEN ASM_REWRITE_TAC[])
    and divop = (--`$DIV`--)
    and multop = (--`$*`--)
    and plusop = (--`$+`--)
in
  fn tm =>
  (let val [xn,yn] = dest_op divop tm
       val x = int_of_term xn
       and y = int_of_term yn
       val q = x div y
       val p = q * y
       val r = x - p
       val pn = term_of_int p
       and qn = term_of_int q
       and rn = term_of_int r
       val p1 = MUL_CONV (mk_comb{Rator= mk_comb{Rator= multop, Rand= qn},
				  Rand= yn})
       and p2 = ADD_CONV (mk_comb{Rator= mk_comb{Rator= plusop, Rand= pn},
				  Rand= rn})
       and p3 = provelt r y
       and chain = INST[{residue= xn, redex= xv},
			{residue= yn, redex= yv},
			{residue= pn, redex= pv},
			{residue= qn, redex= qv},
			{residue= rn, redex= rv}] divt
   in
       MP (MP (MP chain p1) p2) p3
   end) handle _ => failwith "DIV_CONV"
end;

(*-----------------------------------------------------------------------*)
(* MOD_CONV "[x] MOD [y]" = |- [x] MOD [y] = [x mod y]                   *)
(*-----------------------------------------------------------------------*)

val MOD_CONV =
let val modt =
    prove((--`(q * y = p) ==> (p + r = x) ==> (r < y) ==> (x MOD y = r)`--),
	  REPEAT DISCH_TAC THEN
	  MATCH_MP_TAC (theorem "arithmetic" "MOD_UNIQUE") THEN
	  EXISTS_TAC (--`q:num`--) THEN ASM_REWRITE_TAC[])
    and modop = (--`$MOD`--)
    and multop = (--`$*`--)
    and plusop = (--`$+`--)
in
  fn tm =>
  (let val [xn,yn] = dest_op modop tm
       val x = int_of_term xn and y = int_of_term yn
       val q = x div y
       val p = q * y
       val r = x - p
       val pn = term_of_int p and qn = term_of_int q and rn = term_of_int r
       val p1 = MUL_CONV (mk_comb{Rator= mk_comb{Rator= multop, Rand= qn},
				  Rand= yn})
       and p2 = ADD_CONV (mk_comb{Rator= mk_comb{Rator= plusop, Rand= pn},
				  Rand= rn})
       and p3 = provelt r y
       and chain = INST[{residue= xn, redex= xv},
			{residue= yn, redex= yv},
			{residue= pn, redex= pv},
			{residue= qn, redex= qv},
			{residue= rn, redex= rv}] modt
   in
       MP (MP (MP chain p1) p2) p3
   end) handle _ => failwith "MOD_CONV"
end;
end
