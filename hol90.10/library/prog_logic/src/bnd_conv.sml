signature BND_CONV =
sig

 (* utilities *)
  val SUBS_CONV  : CoreHol.Thm.thm -> CoreHol.Term.term -> CoreHol.Thm.thm

 (* conversions *)
  val BND_CONV   : Abbrev.conv
end;

functor Bnd_Conv (S:SYNTAX) : BND_CONV =
struct

  open stringLib;
  open Lib CoreHol;
  open Term Dsyntax Thm Theory Drule;

    val BND_THM1  = theorem "semantics" "BND_THM1"
    val BND_THM2  = theorem "semantics" "BND_THM2"

    fun SUBS_CONV th t =
	let val x = genvar(type_of t)
	    val t1 = mk_eq{lhs=x,rhs=t}
	    val th1 = DISCH t1 (SUBS [th] (ASSUME t1))
	in
	    MP(INST [{redex=x,residue=t}] th1)(REFL t)
	end  

    fun BND_CONV t =
	let val [x,n,s,y] = (snd o strip_comb) t
	in
	    if x = y 
		then SPECL [n,x,s] BND_THM1
	    else let val yx = mk_eq{lhs=y,rhs=x}
		 in
		     MP (SPECL [n,x,s,y] BND_THM2)
		     (EQ_MP (el 4 (CONJUNCTS (SPEC yx EQ_CLAUSES)))
		      (string_EQ_CONV yx))
		 end
	end

    end (* Functor Bnd_Conv() *)

