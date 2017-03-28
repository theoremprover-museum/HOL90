(*===========================================================================*)
(*                               HOL90 Version 7                             *)
(*                                                                           *)
(* FILE NAME:        list_conv1.sml                                          *)
(*                                                                           *)
(* DESCRIPTION:      Defined procedures for list induction and definition    *)
(*                   by primitive recursion on lists.  Derived inference     *)
(*                   rules for reasoning about lists.                        *)
(*                                                                           *)
(*                   The induction/primitive recursion are really only for   *)
(*                   compatibility with old HOL.                             *)
(*                                                                           *)
(* AUTHOR:           T. F. Melham (87.05.30)                                 *)
(*                                                                           *)
(* USES FILES:       ind.ml, prim_rec.ml, numconv.ml                         *)
(*                                                                           *)
(*                   University of Cambridge                                 *)
(*                   Hardware Verification Group                             *)
(*                   Computer Laboratory                                     *)
(*                   New Museums Site                                        *)
(*                   Pembroke Street                                         *)
(*                   Cambridge  CB2 3QG                                      *)
(*                   England                                                 *)
(*                                                                           *)
(* COPYRIGHT:        T. F. Melham 1987 1990                                  *)
(*                                                                           *)
(* REVISION HISTORY: 90.09.08                                                *)
(* TRANSLATED to hol90 (KLS, Dec 20, 1992)                                   *)
(* New conversions/tactics (PC 11/7/94-most translated by BTG from WW HOL88) *)
(* Minor tweak to EL_CONV to take account of swap in quantifiers in defn     *)
(* of EL. (KLS october'94)                                                   *)
(*===========================================================================*)

structure List_conv1 : List_conv1_sig =
struct

fun LIST_CONV_ERR{function,message} = HOL_ERR{origin_structure="List_conv",
                                              origin_function = function,
                                              message = message};
open Rsyntax;

val % = Parse.term_parser;
val alpha_ty = ==`:'a`==
val bool_ty = ==`:bool`==

val list_INDUCT = theorem "List" "list_INDUCT"
val list_Axiom = theorem "list" "list_Axiom";

(* --------------------------------------------------------------------*)
(*   LIST_INDUCT: (thm # thm) -> thm			               *)
(*							               *)
(*     A1 |- t[[]]      A2 |- !tl. t[tl] ==> !h. t[CONS h t]           *)
(* ----------------------------------------------------------          *)
(*                   A1 u A2 |- !l. t[l]			       *)
(*							               *)
(* --------------------------------------------------------------------*)

fun LIST_INDUCT (base,step) =
   let val {Bvar,Body} = dest_forall(concl step)
       val {ant,conseq} = dest_imp Body
       val {Bvar=h,Body=con} = dest_forall conseq
       val P  = %`\^Bvar.^ant` 
       val b1 = genvar bool_ty
       val b2 = genvar bool_ty
       val base'  = EQ_MP (SYM(BETA_CONV (%`^P []`))) base 
       val step'  = DISCH ant (SPEC h (UNDISCH(SPEC Bvar step)))
       val hypth  = SYM(RIGHT_BETA(REFL (%`^P ^Bvar`)))
       val concth = SYM(RIGHT_BETA(REFL (%`^P(CONS ^h ^Bvar)`)))
       val IND    = SPEC P (INST_TYPE [{redex=alpha_ty, residue = type_of h}]
                                      list_INDUCT)
       val th1 = SUBST[{var=b1,thm=hypth},{var=b2,thm=concth}]
                      (%`^(concl step') = (^b1 ==> ^b2)`)
                      (REFL (concl step'))
       val th2 = GEN Bvar (DISCH (%`^P ^Bvar`)
                                 (GEN h(UNDISCH (EQ_MP th1 step'))))
       val th3 = SPEC Bvar (MP IND (CONJ base' th2))
   in
   GEN Bvar (EQ_MP (BETA_CONV(concl th3)) th3)
   end
   handle _ => raise LIST_CONV_ERR{function="LIST_INDUCT", message = ""};


(* --------------------------------------------------------------------*)
(*							               *)
(* LIST_INDUCT_TAC					               *)
(*							               *)
(*             [A] !l.t[l]				               *)
(*  ================================			               *)
(*   [A] t[[]],  [A,t[l]] !h. t[CONS h t]		               *)
(*							               *)
(* --------------------------------------------------------------------*)

val LIST_INDUCT_TAC  = INDUCT_THEN list_INDUCT ASSUME_TAC;

(* --------------------------------------------------------------------*)
(*                                                                     *)
(* SNOC_INDUCT_TAC                                                     *)
(*                                                                     *)
(*             [A] !l.t[l]                                             *)
(*  ================================                                   *)
(*   [A] t[[]],  [A,t[l]] !h. t[SNOC x t]                              *)
(*                                                                     *)
(* --------------------------------------------------------------------*)
(* PC 11/7/94 *)

val SNOC_INDUCT_TAC = 
  let val SNOC_INDUCT = theorem "List" "SNOC_INDUCT"
  in
   INDUCT_THEN SNOC_INDUCT ASSUME_TAC
  end;


(* --------------------------------------------------------------------*)
(* Definition by primitive recursion for lists		               *)
(* (For compatibility of new/old HOL.)			               *)
(* --------------------------------------------------------------------*)

fun new_list_rec_definition (name,tm) =
  new_recursive_definition{name=name,rec_axiom=list_Axiom,def=tm,fixity=Prefix}

fun new_infix_list_rec_definition (name,tm,prec) =
   new_recursive_definition {name=name,rec_axiom=list_Axiom,def=tm,
                             fixity=Infix prec};

fun dcons tm = snd(((fn c => #Name(dest_const c)="CONS")##I)(strip_comb tm))
fun cend tm = if (#Name(dest_const tm) = "NIL") 
              then []
              else raise LIST_CONV_ERR{function="LENGTH_CONV",  
                                       message="list not terminated with NIL"}
fun stripl tm = let val [h,t] = dcons tm 
                in (h::stripl t)
                end handle _ => cend tm;

(* --------------------------------------------------------------------*)
(* LENGTH_CONV: compute the length of a list                           *)
(*                                                                     *)
(* A call to LENGTH_CONV `LENGTH[x1;...;xn]` returns:                  *)
(*                                                                     *)
(*    |- LENGTH [x1;...;xn] = n   where n is a numeral constant        *)
(* --------------------------------------------------------------------*)

local
val LEN = definition "list" "LENGTH"
val suctm = %`SUC`
val numty = (==`:num`==)
fun SUC (i,th) = let val n = mk_const{Name = int_to_string i,Ty = numty}
                 in TRANS (AP_TERM suctm th) (SYM(num_CONV n))
                 end
fun itfn cth h (i,th) = 
   (i+1,TRANS (SPEC (rand(lhs(concl th))) (SPEC h cth)) (SUC (i,th)))
val check = assert(curry (op =) "LENGTH" o #Name o dest_const)
in
fun LENGTH_CONV tm =
   let val {Rator,Rand} = dest_comb tm
       val _ = check Rator
       val {Args=[ty],...} = dest_type(type_of Rand)
       val (Nil,cons) = CONJ_PAIR (INST_TYPE [{redex=alpha_ty,residue=ty}] LEN)
   in
   snd(itlist (itfn cons) (stripl (rand tm)) (1,Nil))
   end
   handle _ => raise LIST_CONV_ERR{function="LENGTH_CONV", message = ""}
end;

(* --------------------------------------------------------------------*)
(* list_EQ_CONV: equality of lists. 			               *)
(*                                                                     *)
(* This conversion proves or disproves the equality of two lists, given*)
(* a conversion for deciding the equality of elements.                 *)
(*                                                                     *)
(* A call to:                                                          *)
(*                                                                     *)
(*    list_EQ_CONV conv `[x1;...;xn] = [y1;...;ym]`                    *)
(*                                                                     *)
(* returns:                                                            *)
(*                                                                     *)
(*    |- ([x1;...;xn] = [y1;...;ym]) = F                               *)
(*                                                                     *)
(* if:                                                                 *)
(*                                                                     *)
(*    1: ~(n=m)  or 2: conv proves |- (xi = yi) = F for any 1<=i<=n,m  *)
(*                                                                     *)
(* and:                                                                *)
(*                                                                     *)
(*   |- ([x1;...;xn] = [y1;...;ym]) = T                                *)
(*                                                                     *)
(* if:                                                                 *)
(*                                                                     *)
(*   1: (n=m) and xi is syntactically identical to yi for 1<=i<=n,m, o *)
(*   2: (n=m) and conv proves  |- (xi=yi)=T for 1<=i<=n,m              *)
(* --------------------------------------------------------------------*)

local
val T = %`T` 
val F = %`F`
val cnil = theorem "List" "NOT_CONS_NIL"
val lne = theorem "List" "LIST_NOT_EQ"
val nel = theorem "List" "NOT_EQ_LIST"
val leq = theorem "List" "EQ_LIST"
fun Cons ty = 
   let val lty = mk_type{Tyop="list",Args=[ty]}
       val cty = mk_type{Tyop="fun",
                         Args=[ty,mk_type{Tyop="fun",Args=[lty,lty]}]}
   in
   fn h => fn t => mk_comb{Rator=mk_comb{Rator=mk_const{Name="CONS",Ty=cty},
                                         Rand=h}, Rand=t}
   end
fun Nil ty = mk_const{Name="NIL",Ty=mk_type{Tyop="list",Args=[ty]}}
fun split n l = 
   if (n=0) 
   then ([],l) 
   else ((curry (op ::) (hd l))##I)(split (n-1) (tl l))
fun itfn cnv [leq,lne,nel] (h1,h2) th =
   if (is_neg (concl th)) 
   then let val {lhs=l1,rhs=l2} = dest_eq(dest_neg (concl th))
        in  SPEC h2 (SPEC h1 (MP (SPEC l2 (SPEC l1 lne)) th))
        end
   else let val {lhs=l1,rhs=l2} = dest_eq(concl th)
            val heq = cnv (mk_eq{lhs=h1,rhs=h2})
        in
        if (rand(concl heq) = T) 
        then let val th1 = MP (SPEC h2 (SPEC h1 leq)) (EQT_ELIM heq) 
             in  MP (SPEC l2 (SPEC l1 th1)) th
             end
        else let val th1 = MP (SPEC h2 (SPEC h1 nel)) (EQF_ELIM heq) 
             in SPEC l2 (SPEC l1 th1)
             end
        end
in
fun list_EQ_CONV cnv tm =
   let val {lhs,rhs} = dest_eq tm
       val l1 = stripl lhs
       val l2 = stripl rhs
   in
   if (l1=l2)
   then EQT_INTRO(REFL (rand tm)) 
   else let val {Args=[ty],...} = dest_type(type_of(rand tm))
            val n = length l1 
            and m = length l2
            val thms = map (INST_TYPE [{redex=alpha_ty,residue=ty}]) 
                           [leq,lne,nel]
            val ifn = itfn cnv thms
        in
        if (n<m) 
        then let val (exd,(x::xs)) = split n l2
                 val rest = itlist (Cons ty) xs (Nil ty)
                 val thm1 = SPEC rest 
                              (SPEC x (INST_TYPE [{redex=alpha_ty,residue=ty}]
                                                 cnil))
             in EQF_INTRO(itlist ifn (combine(l1,exd))(NOT_EQ_SYM thm1)) 
             end
        else if (m<n) 
             then let val (exd,(x::xs)) = split m l1
                      val rest = itlist (Cons ty) xs (Nil ty)
                     val thm1 = SPEC rest 
                                 (SPEC x(INST_TYPE[{residue=ty,redex=alpha_ty}]

                                                   cnil))
                  in EQF_INTRO(itlist ifn (combine(exd,l2)) thm1)
                  end
             else let val thm = itlist ifn (combine(l1,l2)) (REFL (Nil ty))
                  in
                  EQF_INTRO thm handle _ => EQT_INTRO thm
                  end
        end
   end
   handle _ => raise LIST_CONV_ERR{function="list_EQ_CONV", message = ""}
end;

(*---------------------------------------------------------------------*)
(* APPEND_CONV: this conversion maps terms of the form	               *)
(* 							               *)
(*   `APPEND [x1;...;xm] [y1;...;yn]`                                  *)
(* 							               *)
(* to the equation:					               *)
(*							               *)
(* |- APPEND [x1;...;xm] [y1;...;yn] = [x1;...;xm;y1;...;yn]           *)
(*							               *)
(* ADDED: TFM 91.10.26					               *)
(*---------------------------------------------------------------------*)

local
val (th1,th2) = CONJ_PAIR (definition "list" "APPEND")
val th3 = SPECL [%`l1: 'a list`, %`l2: 'a list`] th2
val th4 = GENL  [%`l2: 'a list`,  %`l1: 'a list`] th3
fun check tm = #Name(dest_const tm) = "APPEND"
fun itfn (cns,ath) v th =
   let val th1 = AP_TERM (mk_comb{Rator=cns,Rand=v}) th
       val l = rand(rator(rand(rator(concl th))))
   in TRANS (SPEC v (SPEC l ath)) th1
   end
in
fun APPEND_CONV tm =
   let val (_,[l1,l2]) = (assert check##I) (strip_comb tm)
       val {els,ty} = dest_list l1
   in
   if (null els) 
   then ISPEC l2 th1 
   else let val cns = rator(rator l1)
            val step = ISPEC l2 th4 
            and base = ISPEC l2 th1
        in
        itlist (itfn (cns,step)) els base
        end
   end
   handle _ => raise LIST_CONV_ERR{function="APPEND_CONV", message=""}
end;

(* --------------------------------------------------------------------*)
(* MAP_CONV conv `MAP f [e1;...;en]`.		         [TFM 92.04.16 *)
(*							               *)
(* Returns |- MAP f [e1;...;en] = [r1;...;rn]		               *)
(* where conv `f ei` returns |- f ei = ri for 1 <= i <= n              *)
(* --------------------------------------------------------------------*)

local
val (mn,mc) = CONJ_PAIR(definition "list" "MAP")
fun check c = #Name(dest_const c) = "MAP"
in
fun MAP_CONV conv tm =
   let val (_,[fnn,l]) = (assert check##I) (strip_comb tm)
       val {els,ty} = dest_list l
       val nth = ISPEC fnn mn 
       and cth = ISPEC fnn mc
       val cns = rator(rator(rand(snd(strip_forall(concl cth)))))
       fun APcons t1 t2 = MK_COMB(AP_TERM cns t2,t1)
       fun itfn e th =
          let val t = rand(rand(rator(concl th)))
              val th1 = SPEC t(SPEC e cth)
          in  TRANS th1 (APcons th (conv (mk_comb{Rator=fnn,Rand=e})))
          end
   in  
   itlist itfn els nth
   end
   handle _ => raise LIST_CONV_ERR{function="MAP_CONV",message=""}
end;
(*-==============================================================-*)
(* Based on the hol88 file "list.ml".                             *)
(* Converted to hol90 - 04.03.94 - BtG                            *)
(*                                                                *)
(* NOTE: exception handling                                       *)
(*       ******************                                       *)
(*   Most conversions themselves should not raise exceptions      *)
(* unless applied to inappropriate terms.                         *)
(* Rather than lose the information about what failure originated *)
(* the exception, we choose to propagate the originating message, *)
(* and in addition record the exception handlers involved, so a   *)
(* trace of the exception handling is possible.  We also include  *)
(* some of the character string which originated the exception.   *)
(*                                                                *)
(*-==============================================================-*)

(* -------------------------------------------------------------- *)
(* Following local functions added by WW 31 Jan 94                *)
(* -------------------------------------------------------------- *)

fun check_const name const =
    if (name = (#Name(dest_const const))) then true
    else raise (HOL_ERR{message = ("const Name: "^(#Name(dest_const const))^
				   "is not: "^name),
                       origin_function = "check_const: ",
                       origin_structure = ""});

val int_of_term = string_to_int o #Name o dest_const;

val term_of_int =
    let val ty = (==`:num`==) in
      fn n => mk_const{Name=int_to_string n,Ty=ty}
    end;

(* -------------------------------------------------------------- *)
(* Following local functions added by BtG 14 Mar 94               *)

fun butlast [x] = []
  | butlast (a::b) = a::(butlast b)
  | butlast _ = raise LIST_CONV_ERR{function = "butlast",message = "empty list"};

fun last [x] = x
  | last (a::b) = last b
  | last _ = raise LIST_CONV_ERR{function = "last",message = "empty list"};
 
(* ------------------------------------------------------------------------- *)
(* EQ_LENGTH_INDUCT_TAC : tactic                                             *)
(*  A ?- !l1 l2. (LENGTH l1 = LENGTH l2) ==> t[l1, l2]                       *)
(* ==================================================== EQ_LENGTH_INDUCT_TAC *)
(*  A                       ?- t[ []/l1, []/l2 ]                             *)
(*  A,LENGTH l1 = LENGTH l2 ?- t[(CONS h l1)/l1,(CONS h' l2)/l2]             *)
(* ------------------------------------------------------------------------- *)

val EQ_LENGTH_INDUCT_TAC =
    let val SUC_NOT = theorem "arithmetic" "SUC_NOT"
	and NOT_SUC = theorem "num" "NOT_SUC" 
        and INV_SUC_EQ = theorem "prim_rec" "INV_SUC_EQ" 
        and LENGTH = theorem "List" "LENGTH"
    in
	LIST_INDUCT_TAC THENL[
         LIST_INDUCT_TAC THENL[
          REPEAT (CONV_TAC FORALL_IMP_CONV) THEN DISCH_THEN (K ALL_TAC),
          REWRITE_TAC[LENGTH,SUC_NOT]],
         GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[LENGTH,NOT_SUC,INV_SUC_EQ]
         THEN GEN_TAC THEN REPEAT (CONV_TAC FORALL_IMP_CONV) THEN DISCH_TAC]
    end;

(* ------------------------------------------------------------------------- *)
(* EQ_LENGTH_SNOC_INDUCT_TAC : tactic                                        *)
(* A ?- !l1 l2.(LENGTH l1 = LENGTH l2) ==> t[l1,l2]                          *)
(* =============================================== EQ_LENGTH_SNOC_INDUCT_TAC *)
(*  A                       ?- t[ []/l1, []/l2 ]                             *)
(*  A,LENGTH l1 = LENGTH l2 ?- t[(SNOC h l1)/l1,(SNOC h' l2)/l2]             *)
(* ------------------------------------------------------------------------- *)

val EQ_LENGTH_SNOC_INDUCT_TAC =
    let val SUC_NOT = theorem "arithmetic" "SUC_NOT" 
        and NOT_SUC = theorem "num" "NOT_SUC" 
        and INV_SUC_EQ = theorem "prim_rec" "INV_SUC_EQ" 
        and LENGTH = theorem "List" "LENGTH" 
        and LENGTH_SNOC = theorem "List" "LENGTH_SNOC"
    in
    SNOC_INDUCT_TAC THENL[
     SNOC_INDUCT_TAC THENL[
      REPEAT (CONV_TAC FORALL_IMP_CONV) THEN DISCH_THEN (K ALL_TAC),
      REWRITE_TAC[LENGTH,LENGTH_SNOC,SUC_NOT]],
     GEN_TAC THEN SNOC_INDUCT_TAC
     THEN REWRITE_TAC[LENGTH,LENGTH_SNOC,NOT_SUC,INV_SUC_EQ]
     THEN GEN_TAC THEN REPEAT (CONV_TAC FORALL_IMP_CONV) THEN DISCH_TAC]
    end;

(*-==============================================================-*)
(*- CONVERSIONS added by WW 31 Jan 94                            -*)
(*-==============================================================-*)

(*---------------------------------------------------------------------------*)
(*- Reductions                                                               *)
(*- FOLDR_CONV conv (--`FOLDR f e [a0,...an]`--) --->                        *)
(*    |- FOLDR f e [a0,...an] = tm                                           *)
(*   FOLDR_CONV evaluates the input expression by iteratively apply          *)
(*    the function f the successive element of the list starting from        *)
(*    the end of the list. tm is the result of the calculation.              *)
(*    FOLDR_CONV returns a theorem stating this fact. During each            *)
(*    iteration, an expression (--`f e' ai`--) is evaluated. The user        *)
(*    supplied conversion conv is used to derive a theorem                   *)
(*     |- f e' ai = e'' which is then used to reduce the expression          *)
(*    to e''. For example,                                                   *)
(*                                                                           *)
(*   - FOLDR_CONV ((RATOR_CONV BETA_CONV) THENC BETA_CONV THENC SUC_CONV)    *)
(*         (--`FOLDR (\l x. SUC x) 0 ([(x0:'a);x1;x2;x3;x4;x5])`--);         *)
(*   = val it = |- FOLDR (\l x. SUC x) 0 [x0; x1; x2; x3; x4; x5] = 6 : thm  *)
(*                                                                           *)
(*   In general, if the function f is an explicit lambda abstraction         *)
(*   (\x x'. t[x,x']), the conversion should be in the form                  *)
(*    ((RATOR_CONV BETA_CONV) THENC BETA_CONV THENC conv'))                  *)
(*   where conv' applied to t[x,x'] returns the theorem |-t[x,x'] = e''.     *)
(*---------------------------------------------------------------------------*)


val FOLDR_CONV  =
    let val (bthm,ithm) = CONJ_PAIR (definition "List" "FOLDR") in
  fn conv => fn tm =>
    let val (_,[f,e,l]) = ((check_const"FOLDR")##I)(strip_comb tm) 
	val ithm' = ISPECL[f,e] ithm 
	val {els=els,ty=lty} =  (dest_list l) 
	fun itfn a th =
	    let val [f',e',l'] = snd(strip_comb(lhs(concl th))) 
		val lem = SUBS [th](SPECL[a,l'] ithm')
	    in
		TRANS lem (conv (rhs (concl lem)))
	    end
    in
	(itlist itfn els (ISPECL [f,e] bthm))
    end 
	handle HOL_ERR {origin_structure = "list_conv",
			origin_function = origin_function,
			message = message}
			=> (raise LIST_CONV_ERR{function="FOLDR_CONV",
						 message=(origin_function^": "^message)})
    end;

(*---------------------------------------------------------------------------*)
(* FOLDL_CONV conv (--`FOLDL f e [a0,...an]`--) --->                         *)
(*     |- FOLDL f e [a0,...an] = tm                                          *)
(*   FOLDL_CONV evaluates the input expression by iteratively apply          *)
(*    the function f the successive element of the list starting from        *)
(*    the head of the list. tm is the result of the calculation.             *)
(*    FOLDL_CONV returns a theorem stating this fact. During each            *)
(*    iteration, an expression (--`f e' ai`--) is evaluated. The user        *)
(*    supplied conversion conv is used to derive a theorem                   *)
(*     |- f e' ai = e'' which is then used to reduce the expression          *)
(*    to e''. For example,                                                   *)
(*                                                                           *)
(*   - FOLDL_CONV ((RATOR_CONV BETA_CONV) THENC BETA_CONV THENC SUC_CONV)    *)
(*         (--`FOLDL (\l x. SUC l) 0 ([(x0:'a);x1;x2;x3;x4;x5])`--);         *)
(*   val it = |- FOLDL (\x l. SUC x) 0 [x0; x1; x2; x3; x4; x5] = 6 : thm    *)
(*                                                                           *)
(*   In general, if the function f is an explicit lambda abstraction         *)
(*   (\x x'. t[x,x']), the conversion should be in the form                  *)
(*    ((RATOR_CONV BETA_CONV) THENC BETA_CONV THENC conv'))                  *)
(*   where conv' applied to t[x,x'] returns the theorem |-t[x,x'] = e''.     *)
(*---------------------------------------------------------------------------*)


val FOLDL_CONV  =
    let val (bthm,ithm) = CONJ_PAIR (definition "List" "FOLDL") in
  fn conv => fn tm =>
    let val (_,[f,e,l]) = ((check_const "FOLDL")##I)(strip_comb tm) 
	val ithm' = ISPEC f ithm 
	fun itfn (term) =
	    let val (_,[f,e,l]) = strip_comb term
	    in
		if (is_const l)
		    then let val {Name=nill,Ty} = dest_const l
			 in
			     if not(nill = "NIL")
				 then (raise LIST_CONV_ERR{function="FOLDL_CONV",
					       message=("expecting null list, term is :" ^
						        nill)})
			     else (ISPECL[f,e]bthm)
			 end
		else
		    let val [h,t] = snd(strip_comb l) 
			val th = ISPECL[e,h,t] ithm' 
			val lem = CONV_RULE
			    ((RAND_CONV o RATOR_CONV o RAND_CONV) conv) th
		    in
			(TRANS lem (itfn (rhs(concl lem)))) 
		    end
	    end
    in
	(itfn tm) 
    end
	handle HOL_ERR {origin_structure = "list_conv",
			origin_function = origin_function,
			message = message}
			=> (raise LIST_CONV_ERR{function="FOLDL_CONV",
					        message=(origin_function^": "^message)})
    end;

(* --------------------------------------------------------------------- *)
(* list_FOLD_CONV : thm -> conv -> conv                                  *)
(* list_FOLD_CONV foldthm conv tm                                        *)
(* where cname is the name of constant and foldthm is a theorem of the   *)
(* the following form:                                                   *)
(* |- !x0 ... xn. CONST x0 ... xn = FOLD[LR] f e l                       *)
(* and conv is a conversion which will be passed to FOLDR_CONV or        *)
(* FOLDL_CONV to reduce the right-hand side of the above theorem         *)
(* --------------------------------------------------------------------- *)
val list_FOLD_CONV =
  fn foldthm => fn conv => fn tm =>
   (let val (cname,args) = (strip_comb tm) 
	val fthm = ISPECL args foldthm 
	val {lhs=left,rhs=right} = dest_eq(concl fthm)
	val const = fst(strip_comb left) 
	val f = #Name(dest_const(fst(strip_comb right)))
    in
    if (not(cname = const))
	then raise (LIST_CONV_ERR{function="list_FOLD_CONV",
				  message=("theorem and term are different:"^
				           (term_to_string cname)^" vs "^(term_to_string const))})
    else if (f = "FOLDL") then
        TRANS fthm (FOLDL_CONV conv right)
	 else if (f = "FOLDR") then
	     TRANS fthm (FOLDR_CONV conv right)
    else raise (LIST_CONV_ERR
		{function="list_FOLD_CONV",
		 message=("not FOLD theorem, uses instead: "^f)})
    end)
        handle HOL_ERR {origin_structure = "list_conv",
			origin_function = origin_function,
			message = message}
			=> (raise LIST_CONV_ERR{function="list_FOLD_CONV",
					        message=(origin_function^": "^message)});


(*----------------------------------------------------------------------------*)
(* The following definition of ADD_CONV is copied from num_lib. It was in the *)
(* core in HOL88 but is in the library in HOL90 so cant be used in the core   *)

local
val nv = --`n:num`--
and mv = --`m:num`--
and numty = ==`:num`==
and plus = --`+`--
val asym = SPECL [nv,mv] (theorem "arithmetic" "ADD_SYM") 
val Sth = let val addc = theorem "arithmetic" "ADD_CLAUSES" 
              val (t1,t2) = CONJ_PAIR (CONJUNCT2(CONJUNCT2 addc)) 
          in
          TRANS t1 (SYM t2)
          end
val ladd0 = let val addc = theorem "arithmetic" "ADD_CLAUSES" 
            in
            GEN (--`n:num`--) (CONJUNCT1 addc)
            end
val v1 = genvar (==`:num`==)
and v2 = genvar (==`:num`==)
fun tm_to_int tm = string_to_int(#Name(dest_const tm)) 
and int_to_tm i  = mk_const{Name = int_to_string i, Ty = numty}
val pl = --`$+`--
val lra = mk_comb{Rator = pl, Rand = v1}
fun mk_pat (n,m) = mk_eq{lhs = mk_comb{Rator = lra, Rand = m},
                         rhs = mk_comb{Rator = mk_comb{Rator = pl, Rand = n},
                                       Rand = v2}}
fun trans (c,mi) th =
   let val {Rator,Rand = m} = dest_comb(rand(concl th))
       val n = rand Rator
       val nint = int_to_tm c 
       and mint = int_to_tm mi
       val nth = SYM(num_CONV n) 
       and mth = SYM(num_CONV mint)
       val thm1 = INST [mv |-> nint, nv |-> m] Sth
   in
   SUBST [{var=v1,thm=nth},{var=v2,thm=mth}] (mk_pat(nint,m)) thm1
   end
val zconv = RAND_CONV(REWR_CONV ladd0)
fun conv th (n,m) =
   let val (thm,count,mint) = (ref th, ref n, ref m)
   in
   ( while (!count <> 0)
     do ( Ref.dec count;
          Ref.inc mint;
          thm := TRANS (!thm) (trans (!count, !mint) (!thm))
        );
     CONV_RULE zconv (!thm)
   )
   end

fun ADD_CONV tm =
   let val (c,[n,m]) = (assert (fn c => (c = plus)) ## I) (strip_comb tm)
       val nint = tm_to_int n 
       and mint = tm_to_int m 
   in
   if not(mint < nint)
   then conv (REFL tm) (nint,mint) 
   else let val th1 = conv(REFL(mk_comb{Rator=mk_comb{Rator=c,Rand=m},Rand=n}))
                          (mint,nint) 
        in
        TRANS (INST [nv |-> n, mv |-> m] asym) th1
        end
   end
   handle _ => raise LIST_CONV_ERR{function = "ADD_CONV",message = ""}
in
 val SUM_CONV =
    list_FOLD_CONV (theorem "List" "SUM_FOLDR") ADD_CONV;
end;

(*---------------------------------------------------------------------*)
(* Filter                                                              *)
(* FILTER_CONV conv (--`FILTER P [a0,...an]`--) --->                   *)
(*    |- FILTER P [a0,...,an] = [...,ai,...]                           *)
(*    where conv (--`P ai`--) returns a theorem |- P ai = T for all ai *)
(*    in the resulting list.                                           *)
(*---------------------------------------------------------------------*)
val FILTER_CONV =
    let val (bth,ith) = CONJ_PAIR (definition "List" "FILTER") in
  fn conv => fn tm =>
    (let val (_,[P,l]) =
         ((check_const "FILTER") ## I) (strip_comb tm) 
	 val bth' = ISPEC P bth and ith' = ISPEC P ith 
	 val lis = #els(dest_list l) 
	 fun ffn x th =
	     let val {lhs=left,rhs=right} = dest_eq(concl th) 
		 val (_,[p,ls]) = strip_comb left 
		 val fthm = SPECL [x,ls] ith' and cthm = conv (--`^P ^x`--)
	     in
		 (CONV_RULE (RAND_CONV COND_CONV) (SUBS[cthm,th]fthm))
	     end
     in
     (itlist ffn lis bth')
     end) 
        handle HOL_ERR {origin_structure = "list_conv",
			origin_function = origin_function,
			message = message}
			=> (raise LIST_CONV_ERR{function="FILTER_CONV",
					        message=(origin_function^": "^message)})
     end;

(*----------------------------------------------------------------*)
(* SNOC_CONV : conv                                               *)
(*   SNOC_CONV (--`SNOC x [x0,...xn]`--) --->                     *)
(*    |- SNOC x [x0,...xn] = [x0,...,xn,x]                        *)
(*----------------------------------------------------------------*)
val SNOC_CONV =
    let val (bthm,sthm) = CONJ_PAIR (definition "List" "SNOC") in
  fn tm =>
    (let val (_,[d,lst]) =
        ((check_const "SNOC") ## I) (strip_comb tm) 
	 val ty = type_of lst 
	 val {els=lst',ty=ety} = (dest_list lst) 
	 val EMP = (--`[]:^(ty_antiq ty)`--)
	 and CONS = (--`CONS:^(ty_antiq ety) -> ^(ty_antiq ty) ->^(ty_antiq ty)`--) 
	 fun itfn x (lst,ithm) =
	     (mk_comb{Rator=mk_comb{Rator=CONS,Rand=x},Rand=lst},
	      (SUBS[ithm](ISPECL[d,x,lst]sthm)))
     in
	 snd(itlist itfn lst' (EMP,(ISPEC d bthm)))
     end)
	 handle HOL_ERR {origin_structure = "list_conv",
			origin_function = origin_function,
			message = message}
			=> (raise LIST_CONV_ERR{function="SNOC_CONV",
					        message=(origin_function^": "^message)})
    end;
    

(*----------------------------------------------------------------*)
(* REVERSE_CONV : conv                                            *)
(*   REVERSE_CONV (--`REVERSE [x0,...,xn]`--) --->                *)
(*   |- REVERSE [x0,...,xn] = [xn,...,x0]                         *)
(*----------------------------------------------------------------*)
val REVERSE_CONV =
    let val fthm = theorem "List" "REVERSE_FOLDL"
	val conv = ((RATOR_CONV BETA_CONV) THENC BETA_CONV)
    in
  fn tm =>
    (let val (_,[lst]) = ((check_const "REVERSE") ## I) (strip_comb tm) 
	 val fthm' = ISPEC lst fthm
     in
	 TRANS fthm' (FOLDL_CONV conv (rhs(concl fthm')))
     end)
	 handle HOL_ERR {origin_structure = "list_conv",
			origin_function = origin_function,
			message = message}
			=> (raise LIST_CONV_ERR{function="REVERSE_CONV",
					        message=(origin_function^": "^message)})
     end;
					       
(*----------------------------------------------------------------*)
(* FLAT_CONV : conv                                               *)
(*   FLAT_CONV (--`FLAT [[x00,...,x0n],...,[xm0,...xmn]]`--) ---> *)
(*   |- (--`FLAT [[x00,...,x0n],...,[xm0,...xmn]]`--) =           *)
(*        [x00,...,x0n,...,xm0,...xmn]                            *)
(*----------------------------------------------------------------*)
val FLAT_CONV =
    let val lem = prove((--`APPEND = (\x1 x2:'a list. APPEND x1 x2)`--),
			CONV_TAC FUN_EQ_CONV THEN GEN_TAC THEN BETA_TAC
			THEN CONV_TAC FUN_EQ_CONV THEN GEN_TAC
			THEN BETA_TAC THEN REFL_TAC) 
	val ffthm = theorem "List" "FLAT_FOLDR" 
	val afthm = theorem "List" "APPEND_FOLDR" 
	val fthm = REWRITE_RULE[afthm](SUBS[lem] ffthm) 
	val conv = (RAND_CONV (FOLDR_CONV ((RATOR_CONV BETA_CONV)
                        THENC BETA_CONV THENC (FOLDR_CONV ALL_CONV))))
    in
  fn tm =>
    (let val (_,[lst]) = ((check_const "FLAT") ## I) (strip_comb tm) 
	 val fthm' = ISPEC lst fthm
     in
	 CONV_RULE conv fthm'
     end)
        handle HOL_ERR {origin_structure = "list_conv",
			origin_function = origin_function,
			message = message}
			=> (raise LIST_CONV_ERR{function="FLAT_CONV",
					        message=(origin_function^": "^message)})
    end;
					       

(*-----------------------------------------------------------------------*)
(* EL_CONV : conv                                                        *)
(* The argument to this conversion should be in the form of              *)
(*   (--`EL k [x0, x1, ..., xk, ..., xn]`--)                             *)
(* It returns a theorem                                                  *)
(*  |- EL k [x0, x1, ..., xk, ..., xn] = xk                              *)
(* iff 0 <= k <= n, otherwise failure occurs.                            *)
(*-----------------------------------------------------------------------*)
val EL_CONV =
let val (bthm,ithm) = CONJ_PAIR (theorem "List" "EL"); 
    val HD = theorem "List" "HD";
    val TL = theorem "List" "TL";
    fun dec n =
       let val nn = int_of_term n in
       mk_const{Name=int_to_string(nn - 1), Ty=(==`:num`==)}
       end;
    fun tail lst = hd(tl(snd(strip_comb lst)));
    fun iter ct N bits =
       let val (n',m',lst') = (ref(ct-1), ref(dec N), ref(tail bits));
           val sthm = ref(PURE_ONCE_REWRITE_RULE[TL](ISPECL [!m',bits] ithm));
       in (while (0 < !n') do
            (n' :=  !n' - 1;
             sthm := TRANS (RIGHT_CONV_RULE(RATOR_CONV(RAND_CONV num_CONV))
                                           (!sthm))
                           (SUBS[ISPECL(snd(strip_comb (!lst')))TL]
                                (ISPECL[dec (!m'), !lst'] ithm));
             lst' := tail (!lst');
             m' := dec (!m'))
           ;
            (TRANS (!sthm) (SUBS [ISPECL(snd(strip_comb (!lst')))HD]
                                 (ISPEC(!lst') bthm))))
      end;
in
fn tm =>
    let val (_,[N,bits]) = ((check_const "EL") ## I) (strip_comb tm);
	val n = int_of_term N;
	val lst = bits and m = N;
     in
	if (n = 0) then
(* This fix would give purer behaviour. It has been left alone to mirror the
 *   definition EL 0 l == HD l
 *            if (length(#els(dest_list bits)) = 0) then
 *               (raise LIST_CONV_ERR{function="EL_CONV",
 *				    message=("index too large: 0")})
 *            else
 *)
	     (PURE_ONCE_REWRITE_RULE[HD](ISPEC bits bthm))
	 else if (n < length(#els(dest_list bits))) then
	     (SUBS [SYM (num_CONV N)](iter n N bits))
	      else raise LIST_CONV_ERR{function = "EL_CONV",
                                message = "index too large: "^int_to_string n}
     end
     handle HOL_ERR {origin_structure = "list_conv",origin_function, message}
     => raise LIST_CONV_ERR{function = "EL_CONV",
                            message = origin_function^": "^message}
end;

(*-----------------------------------------------------------------------*)
(* ELL_CONV : conv                                                       *)
(* It takes a term of the form (--`ELL k [x(n-1), ... x0]`--) and returns*)
(* |- ELL k [x(n-1), ..., x0] = x(k)                                     *)
(*-----------------------------------------------------------------------*)
val ELL_CONV =
    let val bthm = theorem "List" "ELL_0_SNOC"
	and ithm = theorem "List" "ELL_SUC_SNOC" 
	fun iter count (d,lst) elty =
	    let val n = (ref count) and x = (ref d) and l = (ref lst)
		val th = ref (ISPECL[(term_of_int (!n)), !x,
				     mk_list{els=(!l),ty=elty}]ithm)
	    in
		(while (not(!n = 0)) do
		    (n := !n - 1;
		     x := (last (!l));
		     l := butlast (!l);
		     th := TRANS (RIGHT_CONV_RULE ((RATOR_CONV o RAND_CONV)
						   num_CONV) (!th)) 
		     (CONV_RULE ((RATOR_CONV o RAND_CONV o RAND_CONV)SNOC_CONV)
		      (ISPECL[(term_of_int (!n)), (!x), mk_list{els=(!l),ty=elty}]ithm)))
		    ;
		    (x := last(!l); l := butlast(!l);
		     (TRANS (!th)
		      (CONV_RULE
		       ((RATOR_CONV o RAND_CONV o RAND_CONV) SNOC_CONV)
		       (ISPECL [mk_list{els=(!l),ty=elty},!x] bthm)))))
	    end
    in
  fn tm =>
    (let val (_,[N,lst]) = ((check_const"ELL") ## I)(strip_comb tm)
	 val ty = type_of lst
	 val {els=lst',ty=ety} = (dest_list lst)
	 val n =  int_of_term N
     in
	 if not(n < (length lst'))
	     then raise LIST_CONV_ERR{function="ELL_CONV",
				       message=("index too large: "^(int_to_string n))}
	 else if (n = 0)
		  then
		      (CONV_RULE ((RATOR_CONV o RAND_CONV o RAND_CONV)SNOC_CONV)
		       (ISPECL[mk_list{els=butlast lst',ty=ety},(last lst')]bthm))
	      else
		  SUBS_OCCS[([1],SYM (num_CONV N))]
		  (CONV_RULE ((RATOR_CONV o RAND_CONV o RAND_CONV)SNOC_CONV)
		   (iter (n - 1) ((last lst'), (butlast lst')) ety))
     end)
        handle HOL_ERR {origin_structure = "list_conv",
			origin_function = origin_function,
			message = message}
			=> (raise LIST_CONV_ERR{function="ELL_CONV",
					        message=(origin_function^": "^message)})
    end;
    
(* --------------------------------------------------------------------- *)
(* MAP2_CONV conv (--`MAP2 f [x1,...,xn] [y1,...,yn]`--)                 *)
(*                                                                       *)
(* Returns |- MAP2 f [x1,...,xn] [y1,...,yn] = [r1,...,rn]               *)
(* where conv (--`f xi yi`--) returns |- f xi yi = ri for 1 <= i <= n    *)
(* --------------------------------------------------------------------- *)
val MAP2_CONV =
    let val (mn,mc) = CONJ_PAIR(theorem "List" "MAP2") in
  fn conv => fn tm =>
     (let val (_,[fnc,l1,l2]) = ((check_const"MAP2") ## I) (strip_comb tm) 
	  val {els=el1s,ty=ty1} = dest_list l1
	  and {els=el2s,ty=ty2} = dest_list l2 
	  val els = combine (el1s,el2s) 
	  val nth = ISPEC fnc mn and cth = ISPEC fnc mc 
	  val cns = rator(rator(rand(snd(strip_forall(concl cth))))) 
	  fun itfn (e1,e2) th =
	      let val (_,[f,t1,t2]) = strip_comb(lhs(concl th))
		  val th1 = SPECL [e1, t1, e2, t2] cth 
		  val r = conv (mk_comb{Rator=mk_comb{Rator=fnc,Rand=e1},Rand=e2})
	      in
		  (SUBS[r,th]th1)
	      end
      in
	  itlist itfn els nth
      end)
	  handle HOL_ERR {origin_structure = "list_conv",
			  origin_function = origin_function,
			  message = message}
	                   => (raise LIST_CONV_ERR{function="MAP2_CONV",
						   message=(origin_function^": "^message)})
    end;

(* --------------------------------------------------------------------- *)
(* ALL_EL_CONV : conv -> conv                                            *)
(* ALL_EL_CONV conv (--`ALL_EL P [x0,...,xn]`--) --->                    *)
(* |- ALL_EL P [x0,...,xn] = T                                           *)
(*                       iff conv (--`P xi`--)---> |- P xi = T for all i *)
(* |- ALL_EL P [x0,...,xn] = F otherwise                                 *)
(* --------------------------------------------------------------------- *)
val ALL_EL_CONV =
    let val (bth,ith) = CONJ_PAIR (definition "List" "ALL_EL") 
	val AND_THM = mk_set(flatten(map (CONJ_LIST 5)
            [(SPEC (--`T`--) AND_CLAUSES),(SPEC (--`F`--) AND_CLAUSES)]))
    in
  fn conv => fn tm =>
    (let val (_,[P,l]) = ((check_const"ALL_EL") ## I)(strip_comb tm) 
	 val bth' = ISPEC P bth and ith' = ISPEC P ith
	 val lis = #els(dest_list l) 
	 fun ffn x th =
	     let val {lhs=left,rhs=right} = dest_eq(concl th) 
		 val (_,[p,ls]) = strip_comb left 
		 val fthm = SPECL [x,ls] ith'
		 and cthm = conv (mk_comb{Rator=P,Rand=x})
	     in
		 SUBS AND_THM (SUBS[cthm,th]fthm)
	     end
     in
	 (itlist ffn lis bth') 
     end)
	 handle HOL_ERR {origin_structure = "list_conv",
			 origin_function = origin_function,
			 message = message}
	                 => (raise LIST_CONV_ERR{function="ALL_EL_CONV",
						 message=(origin_function^": "^message)})
    end;

(* --------------------------------------------------------------------- *)
(* SOME_EL_CONV : conv -> conv                                           *)
(* SOME_EL_CONV conv (--`SOME_EL P [x0,...,xn]`--) --->                  *)
(* |- SOME_EL P [x0,...,xn] = F                                          *)
(*                        iff conv (--`P xi`--)---> |- P xi = F for all i*)
(* |- SOME_EL P [x0,...,xn] = F otherwise                                *)
(* --------------------------------------------------------------------- *)
val SOME_EL_CONV =
    let val (bth,ith) = CONJ_PAIR (definition "List" "SOME_EL")
	val OR_THM = mk_set(flatten(map (CONJ_LIST 5)
	    [(SPEC (--`T`--) OR_CLAUSES),(SPEC (--`F`--) OR_CLAUSES)]))
    in
  fn conv => fn tm =>
    (let val (_,[P,l]) = ((check_const"SOME_EL") ## I)(strip_comb tm) 
	 val bth' = ISPEC P bth and ith' = ISPEC P ith 
	 val lis = #els(dest_list l) 
	 fun ffn x th =
	     let val {lhs=left,rhs=right} = dest_eq(concl th) 
		 val (_,[p,ls]) = strip_comb left 
		 val fthm = SPECL [x,ls] ith' and cthm = conv (--`^P ^x`--)
	     in
		 SUBS OR_THM (SUBS[cthm,th]fthm)
	     end
     in
	 (itlist ffn lis bth')
     end)
	 handle HOL_ERR {origin_structure = "list_conv",
			 origin_function = origin_function,
			 message = message}
	                 => (raise LIST_CONV_ERR{function="SOME_EL_CONV",
						 message=(origin_function^": "^message)})
    end;

(* --------------------------------------------------------------------- *)
(* IS_EL_CONV : conv -> conv                                             *)
(* IS_EL_CONV conv (--`IS_EL P [x0,...,xn]`--) --->                      *)
(* |- IS_EL x [x0,...,xn] = T iff conv (--`x = xi`--) --->               *)
(*                                    |- (x = xi) = F for an i           *)
(* |- IS_EL x [x0,...,xn] = F otherwise                                  *)
(* --------------------------------------------------------------------- *)
val IS_EL_CONV =
    let val bth = (definition "List" "IS_EL_DEF") in
  fn conv => fn tm =>
    (let val (_,[x,l]) = ((check_const"IS_EL") ## I)(strip_comb tm) 
	 val bth' = ISPECL[x,l] bth 
	 val right = rhs (concl bth')
     in
	 TRANS bth' (SOME_EL_CONV conv right)
     end)
	 handle HOL_ERR {origin_structure = "list_conv",
			 origin_function = origin_function,
			 message = message}
	                 => (raise LIST_CONV_ERR{function="IS_EL_CONV",
						 message=(origin_function^": "^message)})
    end;

(* --------------------------------------------------------------------- *)
(* LAST_CONV : conv                                                      *)
(* LAST_CONV (--`LAST [x0,...,xn]`--) ---> |- LAST [x0,...,xn] = xn      *)
(* --------------------------------------------------------------------- *)
val LAST_CONV =
    let val bth = theorem "List" "LAST" in
  fn tm =>
    (let val (_,[l]) = ((check_const"LAST") ## I) (strip_comb tm) 
	 val {els=l',ty=lty} = dest_list l
     in
	 if ((length l') = 0) then raise (LIST_CONV_ERR{function="LAST_CONV",
					       message="empty list"})
	 else
	     (let val x = last l' and lis = mk_list{els=(butlast l'),ty=lty}
		  val bth' = ISPECL[x,lis] bth
	      in
		  CONV_RULE ((RATOR_CONV o RAND_CONV o RAND_CONV)SNOC_CONV) bth'
	      end)
     end)
        handle HOL_ERR {origin_structure = "list_conv",
			origin_function = origin_function,
			message = message}
			=> (raise LIST_CONV_ERR{function="LAST_CONV",
					        message=(origin_function^": "^message)})
    end;
    
(* --------------------------------------------------------------------- *)
(* BUTLAST_CONV : conv                                                   *)
(* BUTLAST_CONV (--`BUTLAST [x0,...,xn-1,xn]`--) --->                    *)
(* |- BUTLAST [x0,...,xn-1,xn] = [x0,...,xn-1]                           *)
(* --------------------------------------------------------------------- *)
val BUTLAST_CONV =
    let val bth = theorem "List" "BUTLAST" in
  fn tm =>
    (let val (_,[l]) = ((check_const"BUTLAST") ## I) (strip_comb tm)
	 val {els=l',ty=lty} = dest_list l
     in
	 if ((length l') = 0) then raise (LIST_CONV_ERR{function="BUTLAST_CONV",
							message="empty list"} )
	 else
	     (let val x = last l' and lis = mk_list{els=(butlast l'),ty=lty} 
		  val bth' = ISPECL[x,lis] bth
	      in
		  CONV_RULE ((RATOR_CONV o RAND_CONV o RAND_CONV)SNOC_CONV) bth'
	      end)
     end)
        handle HOL_ERR {origin_structure = "list_conv",
			origin_function = origin_function,
			message = message}
			=> (raise LIST_CONV_ERR{function="BUTLAST_CONV",
					        message=(origin_function^": "^message)})
    end;
    
(*----------------------------------------------------------------*)
(* This is not needed, but might be when this is placed into      *)
(* the core system, if it is not defined yet ...                  *)
(* Note it isn't saved via the signature here.                    *)

val SUC_CONV =
    let val numty = mk_type{Tyop="num",Args=[]} in
  fn tm =>
    let val {Rator=SUC,Rand} = dest_comb tm
	val {Name=n,Ty} = dest_const Rand
	val n' = int_to_string(1 + (string_to_int n))
    in
	SYM (num_CONV (mk_const{Name=n', Ty=numty}))
    end end;

(*---------------------------------------------------------------*)
(* SEG_CONV : conv                                               *)
(* SEG_CONV (--`SEG m k [x0,...,xk,...,xm+k,...xn]`--) --->      *)
(* |- SEG m k [x0,...,xk,...,xm+k,...xn] = [xk,...xm+k-1]        *)
(*---------------------------------------------------------------*)
val SEG_CONV =
    let val [bthm,mthm,kthm] = CONJ_LIST 3 (definition "List" "SEG") 
	val SUC = (--`SUC`--)
	fun mifn mthm' x th =
	    let val [M',_,L] = snd(strip_comb(lhs(concl th))) in
		SUBS[(SUC_CONV(mk_comb{Rator=SUC,Rand=M'})),th](SPECL[M',x,L]mthm')
	    end
	fun kifn kthm' x th =
	    let val [_,K',L] = snd(strip_comb(lhs(concl th))) in
		SUBS[(SUC_CONV(mk_comb{Rator=SUC,Rand=K'})),th](SPECL[K',x,L]kthm')
	    end
    in
  fn tm =>
   (let val (_,[M,K,L]) = ((check_const"SEG")## I)(strip_comb tm) 
	val {els=lis,ty=lty} = dest_list L
	val m = int_of_term M and k = int_of_term K
    in
	if ((m + k) > (length lis))
	    then raise (LIST_CONV_ERR{function="SEG_CONV",
				      message=("indexes too large: "^(int_to_string m)^
					       " and "^(int_to_string k))})
	else if (m = 0) then (ISPECL [K,L] bthm)
	     else
		 let val mthm' = INST_TYPE [{residue=lty,redex=(==`:'a`==)}] mthm in
		     if (k = 0) then
			 let val (ls,lt) = Lib.split_after m lis 
			     val bthm' = ISPECL[(--`0`--),(mk_list{els=lt,ty=lty})] bthm in
				 (itlist (mifn mthm') ls bthm')
			 end
		     else
			 let val (lk,(ls,lt)) = (I ##(Lib.split_after m))(Lib.split_after k lis)
			     val bthm' = ISPECL[(--`0`--),(mk_list{els=lt,ty=lty})] bthm 
			     val kthm' = SUBS[SYM(num_CONV M)]
				 (INST_TYPE[{residue=lty,redex=(==`:'a`==)}](SPEC (term_of_int(m-1)) kthm)) 
			     val bbthm = itlist (mifn mthm') ls bthm' in
				 (itlist (kifn kthm') lk bbthm)
			 end
		 end
    end)
	 handle HOL_ERR {origin_structure = "list_conv",
			 origin_function = origin_function,
			 message = message}
	                 => (raise LIST_CONV_ERR{function="SEG_CONV",
						 message=(origin_function^": "^message)})
    end;

(*-----------------------------------------------------------------------*)
(* LASTN_CONV : conv                                                     *)
(* It takes a term (--`LASTN k [x0, ..., x(n-k), ..., x(n-1)]`--)        *)
(* and returns the following theorem:                                    *)
(* |- LASTN k [x0, ..., x(n-k), ..., x(n-1)] = [x(n-k), ..., x(n-1)]     *)
(*-----------------------------------------------------------------------*)
val LASTN_CONV =
    let val LASTN_LENGTH_APPEND = theorem "List" "LASTN_LENGTH_APPEND"
	and bthm = CONJUNCT1 (definition "List" "LASTN") 
        and ithm = (theorem "List" "LASTN_LENGTH_ID") 
	fun len_conv ty lst =
	    LENGTH_CONV(mk_comb{Rator=(--`LENGTH:(^(ty_antiq ty))list -> num`--),Rand=lst})
    in
  fn tm =>
    (let val (_,[N,lst]) = ((check_const"LASTN") ## I) (strip_comb tm) 
	 val n = int_of_term N
     in
	 if (n = 0) then (ISPEC lst bthm)
	 else
	     (let val {els=bits,ty=lty} = (dest_list lst) 
		  val len = (length bits)
	      in
		  if (n > len)
		      then raise (LIST_CONV_ERR{function="SEG_CONV",
						message=("index too large"^(int_to_string n))})
	     else if (n = len) then
		 (SUBS[(len_conv lty lst)](ISPEC lst ithm))
	     else
		 (let val (l1,l2) = (Lib.split_after (len - n) bits) 
		      val l1' = mk_list{els=l1,ty=lty}
		      and l2' = mk_list{els=l2,ty=lty} 
		      val APP = (--`APPEND:(^(ty_antiq lty))list -> (^(ty_antiq lty))list -> (^(ty_antiq lty))list`--)
		      val thm2 = len_conv lty l2' 
		      val thm3 = APPEND_CONV (mk_comb{Rator=mk_comb{Rator=APP,Rand=l1'},Rand=l2'})
		  in
		      SUBS[thm2,thm3](ISPECL [l2',l1'] LASTN_LENGTH_APPEND)
		  end)
	      end)
     end)
        handle HOL_ERR {origin_structure = "list_conv",
			origin_function = origin_function,
			message = message}
			=> (raise LIST_CONV_ERR{function="SEG_CONV",
					        message=(origin_function^": "^message)})
    end;
    
(*-----------------------------------------------------------------------*)
(* BUTLASTN_CONV : conv                                                  *)
(* It takes a term  (--`BUTLASTN k [x0,x1,...,x(n-k),...,x(n-1)]`--)     *)
(* and returns the following theorem:                                    *)
(* |- BUTLASTN k  [x0, x1, ..., x(n-k),...,x(n-1)] = [x0, ..., x(n-k-1)] *)
(*-----------------------------------------------------------------------*)
val BUTLASTN_CONV =
    let val bthm = CONJUNCT1 (definition "List" "BUTLASTN") 
	val lthm = (theorem "List" "BUTLASTN_LENGTH_NIL") 
	val athm = (theorem "List" "BUTLASTN_LENGTH_APPEND") 
	fun len_conv ty lst =
	    LENGTH_CONV(mk_comb{Rator=(--`LENGTH:(^(ty_antiq ty))list -> num`--),Rand=lst})
    in
  fn tm =>
    (let val (_,[N,lst]) = ((check_const"BUTLASTN") ## I) (strip_comb tm) 
	 val n = int_of_term N
     in
	 if (n = 0) then (ISPEC lst bthm)
     else
      (let val {els=bits,ty=lty} = (dest_list lst) 
	   val len = (length bits)
       in
	   if (n > len) then
	       raise (LIST_CONV_ERR{function="BUTLASTN_CONV",
				    message=("index too large: "^(int_to_string n))})
	   else if (n = len) then
	       let val thm1 = len_conv lty lst in
		   (SUBS[thm1](ISPEC lst lthm))
	       end
		else
		    (let val (l1,l2) = (Lib.split_after (len - n) bits) 
			 val l1' = mk_list{els=l1,ty=lty}
			 and l2' = mk_list{els=l2,ty=lty }
			 val APP =
			     (--`APPEND:(^(ty_antiq lty))list
			                -> (^(ty_antiq lty))list
			                 -> (^(ty_antiq lty))list`--) 
			 val thm2 = len_conv lty l2' 
			 val thm3 = APPEND_CONV
			     (mk_comb{Rator=mk_comb{Rator=APP, Rand=l1'},Rand=l2'})
		     in
			 (SUBS[thm2,thm3](ISPECL [l2',l1'] athm))
		     end)
       end)
     end)
        handle HOL_ERR {origin_structure = "list_conv",
			origin_function = origin_function,
			message = message}
			=> (raise LIST_CONV_ERR{function="BUTLASTN_CONV",
					        message=(origin_function^": "^message)})
    end;
    

(*-----------------------------------------------------------------------*)
(* BUTFIRSTN_CONV : conv                                                 *)
(* BUTFIRSTN_CONV (--`BUTFIRSTN k [x0,...,xk,...,xn]`--) --->                  *)
(* |- BUTFIRSTN k [x0,...,xk,...,xn] = [xk,...,xn]                       *)
(*-----------------------------------------------------------------------*)
val BUTFIRSTN_CONV =
    let val (bthm,ithm) = CONJ_PAIR (definition "List" "BUTFIRSTN") 
	val SUC = (--`SUC`--) 
	fun itfn ithm' x th =
	    let val (_,[N',L']) = strip_comb(lhs(concl th)) in
		SUBS[(SUC_CONV(mk_comb{Rator=SUC,Rand=N'})),th](SPECL[N',x,L']ithm')
	    end
    in
  fn tm =>
   (let val (_,[K,L]) = ((check_const"BUTFIRSTN")## I)(strip_comb tm) 
	val k = int_of_term K and {els=lis,ty=lty} = dest_list L  in
	    if (k > (length lis))
		then raise (LIST_CONV_ERR{function="BUTFIRSTN_CONV",
					  message=("index too large: "^(int_to_string k))})
	    else if (k = 0) then (ISPEC L bthm)
		 else
		     let val (ll,lr) = Lib.split_after k lis 
			 val bthm' = ISPEC (mk_list{els=lr,ty=lty}) bthm 
			 val ithm' = INST_TYPE[{residue=lty,redex=(==`:'a`==)}]ithm
		     in
			 itlist (itfn ithm') ll bthm'
		     end
    end)
        handle HOL_ERR {origin_structure = "list_conv",
			origin_function = origin_function,
			message = message}
			=> (raise LIST_CONV_ERR{function="BUTFIRSTN_CONV",
					        message=(origin_function^": "^message)})
    end;
    

(*-----------------------------------------------------------------------*)
(* FIRSTN_CONV : conv                                                    *)
(* FIRSTN_CONV (--`FIRSTN k [x0,...,xk,...,xn]`--) --->                  *)
(* |- FIRSTN k [x0,...,xk,...,xn] = [x0,...,xk]                          *)
(*-----------------------------------------------------------------------*)
val FIRSTN_CONV =
    let val (bthm,ithm) = CONJ_PAIR (definition "List" "FIRSTN") 
	val SUC = (--`SUC`--) 
	fun itfn ithm' x th =
	    let val (_,[N',L']) = strip_comb(lhs(concl th)) in
		SUBS[(SUC_CONV(mk_comb{Rator=SUC,Rand=N'})),th](SPECL[N',x,L']ithm')
	    end
    in
  fn tm =>
   (let val (_,[K,L]) = ((check_const"FIRSTN")## I)(strip_comb tm) 
	val k = int_of_term K and {els=lis,ty=lty} = dest_list L
    in
	if (k > (length lis)) then raise LIST_CONV_ERR{function="FIRSTN_CONV",
					       message=("index too large: "^(int_to_string k))}
    else if (k = 0) then (ISPEC L bthm)
    else
        let val (ll,lr) = Lib.split_after k lis 
	    val bthm' = ISPEC (mk_list{els=lr,ty=lty}) bthm 
	    val ithm' = INST_TYPE[{residue=lty,redex=(==`:'a`==)}]ithm
	in
	    itlist (itfn ithm') ll bthm'
	end
    end)
        handle HOL_ERR {origin_structure = "list_conv",
			origin_function = origin_function,
			message = message}
			=> (raise LIST_CONV_ERR{function="FIRSTN_CONV",
					        message=(origin_function^": "^message)})
    end;
		  
(*-----------------------------------------------------------------------*)
(* SCANL_CONV : conv -> conv                                             *)
(* SCANL_CONV conv (--`SCANL f e [x0,...,xn]`--) --->                    *)
(* |- SCANL f e [x0,...,xn] = [e, t0, ..., tn]                           *)
(* where conv (--`f ei xi`--) ---> |- f ei xi = ti                       *)
(*-----------------------------------------------------------------------*)
val SCANL_CONV =
    let val (bthm,ithm) = CONJ_PAIR (definition "List" "SCANL") in
  fn conv => fn tm =>
   (let val (_,[f,e,l]) = ((check_const"SCANL")##I)(strip_comb tm) 
	val bthm' = ISPEC f bthm and ithm' = ISPEC f ithm 
	fun scan_conv  tm' =
	    let val ([_,E,L]) = snd(strip_comb tm')
	    in
		if (is_const L) then (SPEC E bthm')
		else
		    let val ([x,l]) = snd(strip_comb L) 
			val th1 = conv (mk_comb{Rator=mk_comb{Rator=f,Rand=E},Rand=x}) 
			val th2 = SUBS[th1](SPECL[E,x,l] ithm') 
			val th3 = scan_conv (last(snd(strip_comb(rhs(concl th2)))))
		    in
			SUBS[th3]th2
		    end
	    end
    in
	(scan_conv tm)
    end)
        handle HOL_ERR {origin_structure = "list_conv",
			origin_function = origin_function,
			message = message}
			=> (raise LIST_CONV_ERR{function="SCANL_CONV",
					        message=(origin_function^": "^message)})
    end;
    
(*-----------------------------------------------------------------------*)
(* SCANR_CONV : conv -> conv                                             *)
(* SCANR_CONV conv (--`SCANR f e [x0,...,xn]`--) --->                    *)
(* |- SCANR f e [x0,...,xn] = [t0, ..., tn, e]                           *)
(* where conv (--`f xi ei`--) ---> |- f xi ei = ti                       *)
(*-----------------------------------------------------------------------*)
val SCANR_CONV =
    let val (bthm,ithm) = CONJ_PAIR (definition "List" "SCANR") 
	val HD = theorem "List" "HD" in
  fn conv => fn tm =>
   (let val (_,[f,e,l]) = ((check_const"SCANR")##I)(strip_comb tm) 
	val bthm' = ISPEC f bthm and ithm' = ISPEC f ithm 
	fun scan_conv  tm' =
	    let val ([_,E,L]) = snd(strip_comb tm')
	    in
		if (is_const L) then (SPEC E bthm')
		else
		    let val ([x,l]) = snd(strip_comb L) 
			val th2 = (SPECL[E,x,l] ithm') 
			val th3 = scan_conv (last(snd(strip_comb(rhs(concl th2))))) 
			val th4 = PURE_ONCE_REWRITE_RULE[HD](SUBS[th3]th2) 
			val th5 = conv (hd(snd(strip_comb(rhs(concl th4)))))
		    in
			SUBS[th5]th4
		    end
	    end
    in
	(scan_conv tm)
    end)
        handle HOL_ERR {origin_structure = "list_conv",
			origin_function = origin_function,
			message = message}
			=> (raise LIST_CONV_ERR{function="SCANR_CONV",
					        message=(origin_function^": "^message)})
    end;
(*-----------------------------------------------------------------------*)
(* REPLICATE_CONV : conv                                                 *)
(* REPLICATE conv (--`REPLICATE n x`--) --->                             *)
(*  |- REPLICATE n x = [x, ..., x]                                       *)
(*-----------------------------------------------------------------------*)
val REPLICATE_CONV  =
    let val (bthm,ithm) = CONJ_PAIR (definition "List" "REPLICATE")
	fun dec n = term_of_int((int_of_term n) - 1) 
	fun repconv (bthm', ithm') tm =
	    let val [n,_] = snd(strip_comb tm) in
		if ((int_of_term n) = 0) then bthm'
		else let val th1 = SUBS_OCCS [([1],SYM (num_CONV n))](SPEC (dec n) ithm')
		     in
			 CONV_RULE ((RAND_CONV o RAND_CONV)(repconv(bthm',ithm')))
			 th1
		     end
	    end
    in
  fn tm =>
   (let val (_,[n,x]) = ((check_const"REPLICATE")##I)(strip_comb tm) 
	val bthm' = ISPEC x bthm
        val nv = mk_var{Name="n",Ty=(==`:num`==)}
	val ithm' = GEN nv (ISPECL[nv,x] ithm)
    in
	(repconv (bthm',ithm') tm)
    end)
	 handle HOL_ERR {origin_structure = "list_conv",
			 origin_function = origin_function,
			 message = message}
	                 => (raise LIST_CONV_ERR{function="REPLICATE_CONV",
						 message=(origin_function^": "^message)})
    end;

(*-----------------------------------------------------------------------*)
(* GENLIST_CONV : conv -> conv                                           *)
(* GENLIST conv (--`GENLIST f n`--) --->                                 *)
(*                         |- GENLIST f n = [f 0,f 1, ...,f(n-1)]        *)
(*-----------------------------------------------------------------------*)
val GENLIST_CONV =
    let val (bthm,ithm) = CONJ_PAIR (definition "List" "GENLIST") 
	fun dec n = term_of_int((int_of_term n) - 1) 
	fun genconv (bthm,ithm) conv tm =
	    let val n = last(snd(strip_comb tm))
	    in
		if ((int_of_term n) = 0) then CONV_RULE(ONCE_DEPTH_CONV conv) bthm
		else (let val th1 = SUBS[SYM (num_CONV n)](SPEC (dec n) ithm) 
			  val th2 = RIGHT_CONV_RULE ((RATOR_CONV o RAND_CONV) conv) th1 in
			      RIGHT_CONV_RULE (RAND_CONV (genconv (bthm,ithm) conv)) th2
		      end)
	    end
    in
  fn conv => fn tm =>
   (let val (_,[f,n]) = ((check_const"GENLIST") ## I) (strip_comb tm)
	val bthm' = ISPEC f bthm and ithm' = ISPEC f ithm
    in
	RIGHT_CONV_RULE (TOP_DEPTH_CONV SNOC_CONV)(genconv (bthm',ithm') conv tm)
    end)
        handle HOL_ERR {origin_structure = "list_conv",
			origin_function = origin_function,
			message = message}
			=> (raise LIST_CONV_ERR{function="GENLIST_CONV",
					        message=(origin_function^": "^message)})
    end;
    

(* PC 11/7/94 *)

(* --------------------------------------------------------------------- *)
(* AND_EL_CONV : conv                                                    *)
(* AND_EL_CONV (--`AND_EL [x0,...,xn]`--) --->                           *)
(* |- AND_EL [x0,...,xn] = T  iff  |- xi = T for all i                   *)
(* |- AND_EL [x0,...,xn] = F otherwise                                   *)
(* --------------------------------------------------------------------- *)

val AND_EL_CONV =
    list_FOLD_CONV (theorem "List" "AND_EL_FOLDR") (REWRITE_CONV[AND_CLAUSES]);

(* --------------------------------------------------------------------- *)
(* OR_EL_CONV : conv                                                     *)
(* OR_EL_CONV (--`OR_EL [x0,...,xn]`--) --->                             *)
(* |- OR_EL [x0,...,xn] = T  iff  |- xi = T for any i                    *)
(* |- OR_EL [x0,...,xn] = F otherwise                                    *)
(* --------------------------------------------------------------------- *)

val OR_EL_CONV =
    list_FOLD_CONV (theorem "List" "OR_EL_FOLDR") (REWRITE_CONV[OR_CLAUSES]);

end; (* List_conv1 *)
