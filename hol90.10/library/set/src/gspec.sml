(* =====================================================================*)
(* FILE		: gspec.ml						*)
(* DESCRIPTION  : Generalized set specification : {tm[xi...xn] | P}	*)
(*								        *)
(* REWRITTEN    : T Melham						*)
(* DATE		: 90.07.30						*)
(* TRANSLATOR   : Konrad Slind, University of Calgary                   *)
(* =====================================================================*)


structure Gspec : Gspec_sig =
struct

type conv = Abbrev.conv;
open Exception Lib CoreHol Parse;
open Type Term Dsyntax Thm Theory Drule Conv Let_conv;

infix THENC ORELSEC;
infix ##;

fun GSPEC_ERR{function,message} = HOL_ERR{origin_structure = "Gspec",
                                          origin_function = function,
                                          message = message};
open Rsyntax;
(* --------------------------------------------------------------------- *)
(* Local function: MK_PAIR						 *)
(*									 *)
(* A call to:								 *)
(* 									 *)
(*     MK_PAIR "[x1;x2;...;xn]" "v:(ty1 # ty2 # ... # tyn)"		 *)
(*									 *)
(* returns:								 *)
(*									 *)
(*     |- v = FST v, FST(SND v), ..., SND(SND...(SND v))		 *)
(* --------------------------------------------------------------------- *)

local
val alpha = ==`:'a`==
val beta = ==`:'b`==
val PAIR = theorem "pair" "PAIR"
in
fun MK_PAIR [_] v = REFL v
  | MK_PAIR vs v =
      let val vty = type_of v
          val {Args = [ty1,ty2],...} = dest_type vty
          val inst = SYM(SPEC v (INST_TYPE [{residue = ty1,redex = alpha},
				            {residue = ty2,redex = beta}]
				           PAIR))
          val {fst,snd} = dest_pair(rhs(concl inst))
          val thm = MK_PAIR (tl vs) snd 
          val gv = genvar ty2 
      in
      SUBST [{thm=thm,var=gv}] (mk_eq{lhs=v,rhs=mk_pair{fst=fst,snd=gv}}) inst 
      end
end;

(* --------------------------------------------------------------------- *)
(* Local function: EXISTS_TUPLE_CONV					 *)
(*									 *)
(* A call to:								 *)
(* 									 *)
(*  EXISTS_TUPLE_CONV ["x1";...;"xn"] "?v. tm' = (\(x1,...,xn). tm) v	 *)  
(*									 *)
(* returns:								 *)
(*									 *)
(*  |- (?v. tm' = (\(x1,...,xn). tm) v ) = ?x1...xn. tm' = tm		 *)
(* --------------------------------------------------------------------- *)

fun itlist2 f ([],[]) x = x
  | itlist2 f ((h1::t1),(h2::t2)) x = f (h1,h2) (itlist2 f (t1,t2) x)
  | itlist2 _ _ _ = raise GSPEC_ERR{function = "itlist2", 
                                    message = "lists don't have same length"};

local
fun EX(v,tm) th =
      EXISTS (mk_exists{Bvar =v,
			Body = subst[{residue=v,redex=tm}](concl th)},
	      tm)
             th
fun CH tm th = CHOOSE (tm,ASSUME (mk_exists{Bvar=tm,Body=hd(hyp th)})) th
val conv = RAND_CONV (BETA_CONV ORELSEC PAIRED_BETA_CONV)
in
fun EXISTS_TUPLE_CONV vs tm =
   let val tup = end_itlist (fn fst => fn snd => mk_pair{fst=fst,snd=snd}) vs 
       val {Bvar=v,Body} = dest_exists tm 
       val tupeq = MK_PAIR vs v
       val asm1 = SUBST [{thm=tupeq,var=v}] Body (ASSUME Body)
       val comp = Dsyntax.strip_pair (rand(concl tupeq))
       val thm1 = itlist2 EX (vs,comp) asm1
       val imp1 = DISCH tm (CHOOSE (v,ASSUME tm) thm1)
       val asm2 = ASSUME (subst [{residue=tup,redex=v}] Body)
       val thm2 = itlist CH vs (EXISTS (tm,tup) asm2)
       val imp2 = DISCH (hd(hyp thm2)) thm2
       val eq = IMP_ANTISYM_RULE imp1 imp2
       val beta = conv (snd(strip_exists(rhs(concl eq)))) 
   in
   TRANS eq (itlist EXISTS_EQ vs beta)
   end
end;

(* --------------------------------------------------------------------- *)
(* Local function: PAIR_EQ_CONV.					 *)
(*									 *)
(* A call to PAIR_EQ_CONV "?x1...xn. a,b = c,T" returns:		 *)
(*									 *)
(*    |- (?x1...xn. a,T = b,c) = (?x1...xn. (a = b) /\ c)		 *)
(* --------------------------------------------------------------------- *)

local
val alpha = ==`: 'a `==
val EQT = el 1 (CONJUNCTS (SPEC (--`c:bool`--) EQ_CLAUSES))
val PAIR_EQ = theorem "pair" "PAIR_EQ"
val inst = INST_TYPE [{residue = (==`:bool`==),redex = (==`:'b`==)}] 
                     (GENL [(--`x:'a`--),(--`y:'b`--),
                            (--`a:'a`--),(--`b:'b`--)] PAIR_EQ)
val spec = SPECL [(--`a:'a`--),(--`T`--),(--`b:'a`--),(--`c:bool`--)] inst
val PEQ = GENL [(--`a:'a`--),(--`b:'a`--),(--`c:bool`--)] (SUBS [EQT] spec)
in
fun PAIR_EQ_CONV tm =
   let val (vs,body) = strip_exists tm
       val ({fst=a,snd=T},{fst=b,snd=c}) =
	     (fn {lhs,rhs} => (dest_pair lhs, dest_pair rhs)) (dest_eq body)
       val th = SPEC c(SPEC b(SPEC a(INST_TYPE [{residue = type_of a,
						 redex = alpha}] PEQ)))
   in
   itlist EXISTS_EQ vs th
   end
end

(* --------------------------------------------------------------------- *)
(* Local function: ELIM_EXISTS_CONV.					 *)
(*									 *)
(* ELIM_EXISTS_CONV "?x. (x = tm) /\ P[x]" returns:			 *)
(*									 *)
(*   |- (?x. x = tm /\ P[x]) = P[tm/x]					 *)
(* --------------------------------------------------------------------- *)

fun ELIM_EXISTS_CONV tm = 
   let val {Bvar = x,Body = conj} = dest_exists tm
       val {conj1 = eq,conj2 = body} = dest_conj conj
       val (asm1,asm2) = (SYM ## I) (CONJ_PAIR (ASSUME conj))
       val imp1 = DISCH tm (CHOOSE 
			    (x,ASSUME tm)
			    (SUBST [{thm = asm1, var = x}] body asm2))
       val r = lhs eq
       val asm = subst [{residue = r,redex = x}] body
       val imp2 = DISCH asm (EXISTS (tm,r) (CONJ (REFL r) (ASSUME asm))) 
   in
   IMP_ANTISYM_RULE imp1 imp2
   end;


(* --------------------------------------------------------------------- *)
(* Local function: PROVE_EXISTS.					 *)
(*									 *)
(* PROVE_EXISTS "?x. tm" (x not free in tm) returns:			 *)
(*									 *)
(*   |- ?x.tm = tm							 *)
(* --------------------------------------------------------------------- *)

fun PROVE_EXISTS tm = 
   let val {Bvar,Body} = dest_exists tm
       val v = genvar (type_of Bvar)
       val imp1 = DISCH tm (CHOOSE (v,ASSUME tm) (ASSUME Body))
       val imp2 = DISCH Body (EXISTS (tm,v) (ASSUME Body))
   in
   IMP_ANTISYM_RULE imp1 imp2
   end;

(* --------------------------------------------------------------------- *)
(* Internal function: list_variant					 *)
(*									 *)
(* makes variants of the variables in l2 such that they are all not in	 *)
(* l1 and are all different.						 *)
(* --------------------------------------------------------------------- *)
fun list_variant _ [] = []
  | list_variant l1 (h::t) =
      let val v = variant l1 h
      in
      (v::list_variant (v::l1) t)
      end;

(* --------------------------------------------------------------------- *)
(* SET_SPEC_CONV: implements the axiom of specification for generalized	 *)
(* set specifications.							 *)
(*									 *)
(* There are two cases:							 *)
(*									 *)
(*   1) SET_SPEC_CONV "t IN {v | p[v]}"    (v a variable, t a term)	 *)
(* 									 *)
(*      returns:							 *)
(*									 *)
(*      |- t IN {v | p[v]} = p[t/v]					 *)
(*									 *)
(*									 *)
(*   2) SET_SPEC_CONV "t IN {tm[x1;...;xn] | p[x1;...xn]}"		 *)
(*									 *)
(*      returns:							 *)
(*									 *)
(*      |- t IN {tm[x1;...;xn] | p[x1;...xn]} 				 *)
(*	     =								 *)
(*         ?x1...xn. t = tm[x1;...;xn] /\ p[x1;...xn]			 *)
(*									 *)
(* Note that {t[x1,...,xm] | p[x1,...,xn]} means:			 *)
(*									 *)
(*   GGSPEC (\(x1,...,xn). (t[x1,...,xn], p[x1,...,xn]))		 *)
(* --------------------------------------------------------------------- *)

local
val alpha = (==`:'a`==)
val beta = (==`:'b`==)
fun check name = assert (fn tm => #Name(dest_const tm) = name)
val GSPEC = let val th = theorem "set" "GSPECIFICATION"
                val vs = fst(strip_forall (concl th))
            in
            GENL (rev vs) (SPECL vs th) 
            end
val RAconv = RAND_CONV o ABS_CONV
val conv = RAND_CONV(RAconv(RAND_CONV BETA_CONV))
val conv2 = RAND_CONV (PAIR_EQ_CONV THENC PROVE_EXISTS)
fun mktup tm = 
   let val (x,(xs,res)) =
             (fn {Bvar,Body} => (Bvar, mktup Body)) (dest_abs(rand tm))
   in 
   ((x::xs),res) 
   end
   handle HOL_ERR _ =>
       let val (x,res) =
	     (fn {Bvar,Body} => (Bvar,(#fst(dest_pair Body)))) (dest_abs tm) 
               in 
               ([x],res)
               end
in
fun SET_SPEC_CONV tm = 
   let val (_,[v,set]) = (check "IN" ## I) (strip_comb tm)
       val (_,f) = (fn{Rator,Rand}=>(check "GSPEC" Rator, Rand))(dest_comb set)
       val vty = type_of v 
       val {Args=[uty,_],...} = dest_type(type_of f)
       val inst = SPEC v (INST_TYPE [{residue=vty,redex=alpha},
                                     {redex=beta,residue=uty}] GSPEC)
       val (vs,res) = mktup f 
   in 
   if (all ((op not) o (C free_in res)) vs) 
   then let val spec = CONV_RULE conv (SPEC f inst)
            val thm1 = CONV_RULE conv2 spec 
        in  thm1
        end
   else if (is_var res) 
        then let val spec = CONV_RULE conv (SPEC f inst)
                 val thm1 = CONV_RULE (RAND_CONV PAIR_EQ_CONV) spec 
             in
             TRANS thm1 (ELIM_EXISTS_CONV (rhs(concl thm1)))
             end
        else let val spec = SPEC f inst
                 val nvs = list_variant (free_vars v) vs
                 val thm = EXISTS_TUPLE_CONV nvs (rhs(concl spec)) 
             in
             TRANS spec (CONV_RULE (RAND_CONV PAIR_EQ_CONV) thm)
             end
   end
   handle _ => raise GSPEC_ERR{function = "SET_SPEC_CONV", message = ""}
end;

end; (* Gspec *)
