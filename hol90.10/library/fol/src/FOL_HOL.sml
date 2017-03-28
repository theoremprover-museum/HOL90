(* ========================================================================= 
 * FOL <---> HOL
 * ========================================================================= *)

structure FOL_HOL : FOL_HOL_sig = 
struct

type term = CoreHol.Term.term;

open liteLib;
open Exception;
open LiteLib FOL CoreHol;
open Type Term Dsyntax Psyntax Parse;

val mem = Lib.mem;
val subtract = Lib.subtract;
    
(* ------------------------------------------------------------------------- *)
(* Translate a term (in NNF) into the shadow syntax.                         *)
(* ------------------------------------------------------------------------- *)

local val vstore = ref ([]:(term*int) list)
      and gstore = ref ([]:(term*int) list)
      and vcounter = ref 0 
      fun inc_vcounter() =
	    let val n = !vcounter 
		val m = n + 1 
	    in 
		if m >= offinc 
                then failwith "inc_vcounter: too many variables"
		else (vcounter := m; n) 
	    end
       fun currentvars() = !vstore
in
fun reset_vars() = (vstore := []; gstore := []; vcounter := 0)
fun fol_of_var v =
   (assoc v (currentvars())
       handle Subscript =>
		    let val n = inc_vcounter()
		    in (vstore := (v,n)::currentvars(); n) end)
		
fun hol_of_var v =
    rev_assoc v (currentvars())
    handle Subscript => rev_assoc v (!gstore)
	handle Subscript => failwith "hol_of_var"
fun hol_of_bumped_var v =
    hol_of_var v 
    handle HOL_ERR _ => 
	let val v' = v mod offinc 
	    val hv' = hol_of_var v' 
	    val gv = genvar(type_of hv') 
	in (gstore := (gv,v)::(!gstore); gv)
	end
end;
    
val false_tm = (--`F`--);

local val cstore = ref ([(false_tm,1)]:(term * int)list)
      and ccounter = ref 2
in
fun reset_consts() = (cstore := [(false_tm,1)]; ccounter := 2)
fun fol_of_const c =
  let val currentconsts = !cstore
  in assoc c currentconsts 
      handle Subscript => 
	  let val n = !ccounter 
	  in (ccounter := n + 1; cstore := (c,n)::currentconsts; n)
	  end
  end
fun hol_of_const c = 
  rev_assoc c (!cstore) handle Subscript => failwith "hol_of_const"
end;;

fun fol_of_term env consts tm =
  if is_var tm andalso not (mem tm consts) then
    Var(fol_of_var tm)
  else
    let val (f,args) = strip_comb tm
    in if mem f env then failwith "fol_of_term: higher order" 
       else let val ff = fol_of_const f
	    in Fnapp(ff,map (fol_of_term env consts) args)
	    end
    end;;

fun fol_of_atom env consts tm =
  let val (f,args) = strip_comb tm
  in if mem f env then failwith "fol_of_atom: higher order" else
      let val ff = fol_of_const f
      in (ff,map (fol_of_term env consts) args)
      end
  end;;

fun fol_of_literal env consts tm =
    let val tm' = dest_neg tm 
	val (p,a) = fol_of_atom env consts tm'
    in (~p,a)
    end
    handle HOL_ERR _ => fol_of_atom env consts tm;;

fun fol_of_form env consts tm =
  let val (v,bod) = dest_forall tm 
      val fv = fol_of_var v 
      val fbod = fol_of_form (v::env) (subtract consts [v]) bod 
  in  Forall(fv,fbod)
  end
  handle HOL_ERR _ => 
      let val (l,r) = dest_conj tm 
	  val fl = fol_of_form env consts l
	  and fr = fol_of_form env consts r 
      in Conj(fl,fr)
      end
  handle HOL_ERR _ => 
      let val (l,r) = dest_disj tm 
	  val fl = fol_of_form env consts l
	  and fr = fol_of_form env consts r 
      in Disj(fl,fr)
      end
  handle HOL_ERR _ =>
      Atom(fol_of_literal env consts tm);;

(* ------------------------------------------------------------------------- *)
(* Conversion of a FOL shadow term back into HOL.                            *)
(* ------------------------------------------------------------------------- *)

fun hol_of_term tm =
  case tm of
    Var v => hol_of_var v
  | Fnapp(f,args) => list_mk_comb(hol_of_const f,map hol_of_term args);;

(* ------------------------------------------------------------------------- 
 * Further translation functions for HOL formulas.                           
 *
 * ------------------------------------------------------------------------- *)

fun hol_of_atom (p,args) =
  list_mk_comb(hol_of_const p,map hol_of_term args);;

fun hol_of_literal (p,args) =
  if p < 0 then mk_neg(hol_of_atom(~p,args))
  else hol_of_atom (p,args);;


end (* struct *)
