(* ===================================================================== *)
(* FILE          : resolve.sml                                           *)
(* DESCRIPTION   : HOL-style resolution (MP + pattern matching).         *)
(*                 Translated from hol88 version 1.12.                   *)
(*                                                                       *)
(* AUTHOR        : (c) Tom Melham, University of Cambridge               *)
(* TRANSLATOR    : Konrad Slind, University of Calgary                   *)
(* DATE          : September 11, 1991                                    *)
(* UPDATED       : (to 2.01); change to RES_CANON                        *)
(* ===================================================================== *)


structure Resolve : Resolve_sig =
struct
open Base_logic;
open Tactical;
  infix THEN;
  infix THENL;
  infix ORELSE;
open Term_io.Parse;

structure Thm = Base_logic.Thm

fun RESOLVE_ERR{function,message} = HOL_ERR{origin_structure = "Resolve",
					    origin_function = function,
					    message = message}

(* ---------------------------------------------------------------------*)
(* Search among a list of implications to perform Modus Ponens		*)
(* Used nowhere --- deleted until found useful [TFM 90.04.24]		*)
(* let MULTI_MP impl ante =						*)
(*     tryfind (\imp. MATCH_MP imp ante) impl  ?  failwith `MULTI_MP`;  *)
(* ---------------------------------------------------------------------*)

(* ---------------------------------------------------------------------*)
(* Forwards chaining by Modus Ponens					*)
(* Used nowhere --- deleted until found useful [TFM 90.04.24]		*)
(* let MP_CHAIN = REDEPTH_CHAIN o MULTI_MP;				*)
(* ---------------------------------------------------------------------*)

(* ---------------------------------------------------------------------*)
(* Accept a theorem that, properly instantiated, satisfies the goal     *)
(* ---------------------------------------------------------------------*)
fun MATCH_ACCEPT_TAC thm : tactic =
    let val fmatch = Conv.PART_MATCH I thm 
        fun atac (asl,w) = ([], K (fmatch w))
    in
    REPEAT Tactic.GEN_TAC THEN atac
    end
    handle _ => raise RESOLVE_ERR{function = "MATCH_ACCEPT_TAC",message = ""};

(* ---------------------------------------------------------------------*)
(* Basic unit for resolution tactics					*)
(* DELETED: TFM 88.03.31 (not used anywhere)				*)
(*									*)
(* let MATCH_MP_TAC impth = STRIP_ASSUME_TAC o (MATCH_MP impth);	*)
(* ---------------------------------------------------------------------*)

(* ---------------------------------------------------------------------*)
(* Resolve implicative assumptions with an antecedent			*)
(* ---------------------------------------------------------------------*)
fun ANTE_RES_THEN ttac ante : tactic =
   ASSUM_LIST (EVERY o (mapfilter (fn imp => ttac (Conv.MATCH_MP imp ante))));

(* ---------------------------------------------------------------------*)
(* Old versions of RESOLVE_THEN etc.			[TFM 90.04.24]  *)
(* 									*)
(* letrec RESOLVE_THEN antel ttac impth : tactic =			*)
(*     let answers = mapfilter (MATCH_MP impth) antel in		*)
(*     EVERY (mapfilter ttac answers)					*)
(*     THEN								*)
(*     (EVERY (mapfilter (RESOLVE_THEN antel ttac) answers));		*)
(* 									*)
(* let OLD_IMP_RES_THEN ttac impth =					*)
(*  ASSUM_LIST								*)
(*     (\asl. EVERY (mapfilter (RESOLVE_THEN asl ttac) 			*)
(*		  	      (IMP_CANON impth)));			*)
(* 									*)
(* let OLD_RES_THEN ttac = 						*)
(*     ASSUM_LIST (EVERY o (mapfilter (OLD_IMP_RES_THEN ttac)));	*)
(* ---------------------------------------------------------------------*)

(* ---------------------------------------------------------------------*)
(* A trick tactic for solving existential/disjunctive goals		*)
(* Too tricky, and depends on obsolete version of IMP_RES_THEN		*)
(* Deleted: TFM 90.04.24						*)
(* let SELF_RES_TAC (asl,w) = 						*)
(*    OLD_IMP_RES_THEN ACCEPT_TAC					*)
(*       (DISCH w (itlist ADD_ASSUM asl (ASSUME w))) (asl,w);		*)
(* ---------------------------------------------------------------------*)

(* ---------------------------------------------------------------------*)
(* Resolution tactics from LCF - uses IMP_CANON and GSPEC 		*)
(* 									*)
(* Deleted: TFM 90.04.24						*)
(*									*)
(* let OLD_IMP_RES_TAC = OLD_IMP_RES_THEN STRIP_ASSUME_TAC;		*)
(* let OLD_RES_TAC = OLD_RES_THEN STRIP_ASSUME_TAC;			*)
(* ---------------------------------------------------------------------*)

(* =====================================================================*)
(* Resolution tactics for HOL - uses RES_CANON and SPEC_ALL 		*)
(* =====================================================================*)

(* ---------------------------------------------------------------------*)
(* Put a theorem 							*)
(*									*)
(*	 |- !x. t1 ==> !y. t2 ==> ... ==> tm ==>  t 			*)
(*									*)
(* into canonical form for resolution by splitting conjunctions apart   *)
(* (like IMP_CANON but without the stripping out of quantifiers and only*)
(* outermost negations being converted to implications).		*)
(*									*)
(*   ~t            --->          t ==> F        (at outermost level)	*)
(*   t1 /\ t2	  --->		t1,   t2				*)
(*   (t1/\t2)==>t  --->		t1==> (t2==>t)				*)
(*   (t1\/t2)==>t  --->		t1==>t, t2==>t				*)
(*									*)
(*									*)
(* Modification provided by David Shepherd of Inmos to make resolution   *)
(* work with equalities as well as implications. HOL88.1.08,23 jun 1989. *)
(*									*)
(*   t1 = t2      --->          t1=t2, t1==>t2, t2==>t1			*)
(*									*)
(* Modification provided by T Melham to deal with the scope of 		*)
(* universal quantifiers. [TFM 90.04.24]				*)
(*									*)
(*   !x. t1 ==> t2  --->  t1 ==> !x.t2   (x not free in t1)		*)
(*									*)
(* The old code is given below:						*)
(* 									*)
(*    letrec RES_CANON_FUN th =						*)
(*     let w = concl th in						*)
(*     if is_conj w 							*)
(*     then RES_CANON_FUN(CONJUNCT1 th)@RES_CANON_FUN(CONJUNCT2 th)	*)
(*     else if is_imp w & not(is_neg w) then				*)
(* 	let ante,conc = dest_imp w in					*)
(* 	if is_conj ante then						*)
(* 	    let a,b = dest_conj ante in					*)
(* 	    RES_CANON_FUN 						*)
(* 	    (DISCH a (DISCH b (MP th (CONJ (ASSUME a) (ASSUME b)))))	*)
(* 	else if is_disj ante then					*)
(* 	    let a,b = dest_disj ante in					*)
(* 	    RES_CANON_FUN (DISCH a (MP th (DISJ1 (ASSUME a) b))) @	*)
(* 	    RES_CANON_FUN (DISCH b (MP th (DISJ2 a (ASSUME b))))	*)
(* 	else								*)
(* 	map (DISCH ante) (RES_CANON_FUN (UNDISCH th))			*)
(*     else [th];							*)
(* 									*)
(* This version deleted for HOL 1.12 (see below)	[TFM 91.01.17]  *)
(*									*)
(* let RES_CANON = 							*)
(*     letrec FN th = 							*)
(*       let w = concl th in						*)
(*       if (is_conj w) then FN(CONJUNCT1 th) @ FN(CONJUNCT2 th) else	*)
(*       if ((is_imp w) & not(is_neg w)) then				*)
(*       let ante,conc = dest_imp w in					*)
(*       if (is_conj ante) then						*)
(*          let a,b = dest_conj ante in					*)
(* 	   let ath = ASSUME a and bth = ASSUME b in			*)
(*                   FN (DISCH a (DISCH b (MP th (CONJ ath bth)))) else *)
(*          if is_disj ante then					*)
(*         let a,b = dest_disj ante in					*)
(*        let ath = ASSUME a and bth = ASSUME b in			*)
(* 	          FN (DISCH a (MP th (DISJ1 ath b))) @			*)
(*                 FN (DISCH b (MP th (DISJ2 a bth))) else		*)
(*            map (GEN_ALL o (DISCH ante)) (FN (UNDISCH th)) else	*)
(*        if is_eq w then						*)
(*        let l,r = dest_eq w in					*)
(*            if (type_of l = ":bool") then				*)
(*            let (th1,th2) = EQ_IMP_RULE th in				*)
(*                (GEN_ALL th) . ((FN  th1) @ (FN  th2)) 		*)
(*                else [GEN_ALL th]					*)
(*            else [GEN_ALL th] in					*)
(*     \th. (let vars,w = strip_forall(concl th) in			*)
(*           let th1 = if (is_neg w)	 				*)
(* 	  		then NOT_ELIM(SPEC_ALL th) 			*)
(* 			else (SPEC_ALL th) in				*)
(*               map GEN_ALL (FN th1) ? failwith `RES_CANON`);		*)
(* ---------------------------------------------------------------------*)

(* ---------------------------------------------------------------------*)
(* New RES_CANON for version 1.12.			 [TFM 90.12.07] *)
(* 									*)
(* The complete list of transformations is now:				*)
(*									*)
(*   ~t              --->        t ==> F        (at outermost level)	*)
(*   t1 /\ t2	    --->	t1, t2	       (at outermost level)	*)
(*   (t1/\t2)==>t    --->	t1==>(t2==>t), t2==>(t1==>t)		*)
(*   (t1\/t2)==>t    --->	t1==>t, t2==>t				*)
(*   t1 = t2         --->        t1==>t2, t2==>t1			*)
(*   !x. t1 ==> t2   --->        t1 ==> !x.t2   (x not free in t1)	*)
(*   (?x.t1) ==> t2  --->	!x'. t1[x'/x] ==> t2			*)
(*									*)
(* The function now fails if no implications can be derived from the 	*)
(* input theorem.							*)
(* ---------------------------------------------------------------------*)

local
val bool_ty = ==`:bool`==
fun not_elim th = 
   if (Dsyntax.is_neg (Thm.concl th))
   then (true, Drule.NOT_ELIM th)
   else (false,th)
fun canon (fl,th) = 
   let val w = Thm.concl th 
   in
   if (Dsyntax.is_conj w) 
   then let val (th1,th2) = Drule.CONJ_PAIR th 
        in 
        (canon(fl,th1) @ canon(fl,th2)) 
        end
   else if ((Dsyntax.is_imp w) andalso not(Dsyntax.is_neg w)) 
        then let val {ant,...} = Dsyntax.dest_imp w 
             in
             if (Dsyntax.is_conj ant) 
             then let val {conj1,conj2} = Dsyntax.dest_conj ant 
	              val cth = Thm.MP th (Drule.CONJ (Thm.ASSUME conj1)
                                                      (Thm.ASSUME conj2)) 
	              val th1 = Thm.DISCH conj2 cth 
                      and th2 = Thm.DISCH conj1 cth 
                  in
                  (canon(true,Thm.DISCH conj1 th1)
                   @
                   canon(true,Thm.DISCH conj2 th2))
                  end
             else if (Dsyntax.is_disj ant) 
                  then let val {disj1,disj2} = Dsyntax.dest_disj ant 
	                   val ath = Drule.DISJ1 (Thm.ASSUME disj1) disj2 
                           and bth = Drule.DISJ2 disj1 (Thm.ASSUME disj2) 
                           val th1 = Thm.DISCH disj1 (Thm.MP th ath)
                           and th2 = Thm.DISCH disj2 (Thm.MP th bth) 
                       in
                       (canon(true,th1)@canon(true,th2)) 
                       end
                  else if (Dsyntax.is_exists ant) 
                       then let val {Bvar,Body} = Dsyntax.dest_exists ant 
	                        val newv = Term.variant(Thm.thm_free_vars th) 
                                           Bvar 
	                        val newa=Term.subst[{redex=Bvar,residue=newv}]
                                                   Body 
	                        val th1 = Thm.MP th (Drule.EXISTS (ant,newv)
                                                             (Thm.ASSUME newa))
                            in
	                    canon(true,Thm.DISCH newa th1)
                            end
                       else map (Drule.GEN_ALL o (Thm.DISCH ant))
                                (canon(true,Drule.UNDISCH th)) 
             end
        else if (Dsyntax.is_eq w 
                 andalso 
                 (Term.type_of (Term.rand w) = bool_ty))
             then let val (th1,th2) = Drule.EQ_IMP_RULE th 
                  in
                  (if fl then [Drule.GEN_ALL th] else []) @ canon(true,th1) @ 
                  canon(true,th2)
                 end
             else if (Dsyntax.is_forall w) 
                  then let val (vs,_) = Dsyntax.strip_forall w 
                       in 
                       canon(fl,Drule.SPECL vs th) 
                       end
                  else if fl 
                       then [Drule.GEN_ALL th] 
                       else [] 
   end
in
fun RES_CANON th =
   let val imps = 
          rev_itlist(fn th => fn accum =>
                       accum @ (map Drule.GEN_ALL
                                    (canon(not_elim(Drule.SPEC_ALL th)))))
                    (Drule.CONJUNCTS (Drule.SPEC_ALL th)) []
   in
   assert ((op not) o null) imps
   end
   handle _ => raise RESOLVE_ERR{function = "RES_CANON",
                        message = "No implication is derivable from input thm"}
end;


(* --------------------------------------------------------------------- *)
(* Definitions of the primitive:					*)
(*									*)
(* IMP_RES_THEN: Resolve all assumptions against an implication.	*)
(*									*)
(* The definition uses two auxiliary (local)  functions:		*)
(*									*)
(*     MATCH_MP     : like the built-in version, but doesn't use GSPEC.	*)
(*     RESOLVE_THEN : repeatedly resolve an implication			*)
(* 									*)
(* This version deleted for HOL version 1.12   		 [TFM 91.01.17]	*)
(*									*)
(* begin_section IMP_RES_THEN;						*)
(*									*)
(* let MATCH_MP impth =							*)
(*     let sth = SPEC_ALL impth in					*)
(*     let pat = fst(dest_imp(concl sth)) in				*)
(*     let matchfn = match pat in					*)
(*        (\th. MP (INST_TY_TERM (matchfn (concl th)) sth) th);		*)
(* 									*)
(* letrec RESOLVE_THEN antel ttac impth : tactic =			*)
(*        let answers = mapfilter (MATCH_MP impth) antel in		*)
(*            EVERY (mapfilter ttac answers) THEN			*)
(*           (EVERY (mapfilter (RESOLVE_THEN antel ttac) answers));	*)
(* 									*)
(* let IMP_RES_THEN ttac impth =					*)
(*     ASSUM_LIST (\asl. 						*)
(*      EVERY (mapfilter (RESOLVE_THEN asl ttac) (RES_CANON impth))) ? 	*)
(*     failwith `IMP_RES_THEN`;						*)
(*									*)
(* IMP_RES_THEN;							*)
(* 									*)
(* end_section IMP_RES_THEN;						*)
(* 									*)
(* let IMP_RES_THEN = it;						*)
(* ---------------------------------------------------------------------*)

(* ---------------------------------------------------------------------*)
(* Definition of the primitive:						*)
(*									*)
(* IMP_RES_THEN: Resolve all assumptions against an implication.	*)
(*									*)
(* The definition uses an auxiliary (local) function, MATCH_MP, which is*)
(* just like the built-in version, but doesn't use GSPEC.		*)
(* 									*)
(* New implementation for version 1.12: fails if no MP-consequences can *)
(* be drawn, and does only one-step resolution.		[TFM 90.12.07]  *)
(* ---------------------------------------------------------------------*)

fun MATCH_MP impth =
   let val sth = Drule.SPEC_ALL impth 
       val matchfn = Match.match_term (#ant(Dsyntax.dest_imp(Thm.concl sth))) 
   in
   fn th => Thm.MP (Conv.INST_TY_TERM (matchfn (Thm.concl th)) sth) th
   end;

(* ---------------------------------------------------------------------*)
(* check ex l : Fail with ex if l is empty, otherwise return l.		*)
(* ---------------------------------------------------------------------*)

fun check ex [] = raise ex
  | check ex l = l;

(* ---------------------------------------------------------------------*)
(* IMP_RES_THEN  : Resolve an implication against the assumptions.	*)
(* ---------------------------------------------------------------------*)

fun IMP_RES_THEN ttac impth =
   let val ths = RES_CANON impth 
                 handle _ => raise RESOLVE_ERR{function = "IMP_RES_THEN",
                                               message = "No implication"}
   in
   ASSUM_LIST 
     (fn asl => let val l = itlist(fn th => append(mapfilter(MATCH_MP th) asl))
                                  ths [] 
                    val res = check (RESOLVE_ERR{function = "IMP_RES_THEN",
                                                 message = "No resolvents"}) l 
                    val tacs = check (RESOLVE_ERR{function = "IMP_RES_THEN",
						  message = "No tactics"})
                                     (mapfilter ttac res) 
                in
                Tactical.EVERY tacs
                end)
   end;

(* ---------------------------------------------------------------------*)
(* RES_THEN    : Resolve all implicative assumptions against the rest.	*)
(* ---------------------------------------------------------------------*)
fun RES_THEN ttac (asl,g) =
    let val aas = map Thm.ASSUME asl 
        val ths = itlist append (mapfilter RES_CANON aas) [] 
        val imps = check (RESOLVE_ERR{function = "RES_THEN",
				      message = "No implication"}) ths 
        val l = itlist (fn th => append (mapfilter (Conv.MATCH_MP th) aas))
                       imps [] 
        val res = check (RESOLVE_ERR{function = "RES_THEN",
				     message = "No resolvents"}) l 
        val tacs = check (RESOLVE_ERR{function = "RES_THEN",
				      message = "No tactics"})
                         (mapfilter ttac res) 
    in
    Tactical.EVERY tacs (asl,g)
    end;

(* ---------------------------------------------------------------------*)
(* Definition of the standard resolution tactics IMP_RES_TAC and RES_TAC*)
(*									*)
(* The function SA is like STRIP_ASSUME_TAC, except that it does not    *)
(* strip off existential quantifiers. And ST is like STRIP_THM_THEN, 	*)
(* except that it also does not strip existential quantifiers.		*)
(*									*)
(* Old version: deleted for HOL version 1.12 		 [TFM 91.01.17]	*)
(*									*)
(* let (IMP_RES_TAC,RES_TAC) = 						*)
(*    let ST = FIRST_TCL [CONJUNCTS_THEN; DISJ_CASES_THEN] in		*)
(*    let SA = (REPEAT_TCL ST) CHECK_ASSUME_TAC in			*)
(*        (IMP_RES_THEN SA, RES_THEN SA);				*)
(* ---------------------------------------------------------------------*)

(* ---------------------------------------------------------------------*)
(* New versions of IMP_RES_TAC and RES_TAC: repeatedly resolve, and then*)
(* add FULLY stripped, final, result(s) to the assumption list.		*)
(* ---------------------------------------------------------------------*)

fun IMP_RES_TAC th g =
   IMP_RES_THEN (Thm_cont.REPEAT_GTCL IMP_RES_THEN Tactic.STRIP_ASSUME_TAC) 
                th g 
   handle _ => ALL_TAC g;

fun RES_TAC g =
    RES_THEN (Thm_cont.REPEAT_GTCL IMP_RES_THEN Tactic.STRIP_ASSUME_TAC) g 
    handle _ => ALL_TAC g;

(* ---------------------------------------------------------------------*)
(* Used to be for compatibility with the old system. 			*)
(* Deleted: TFM 90.04.24						*)
(* let HOL_IMP_RES_THEN = IMP_RES_THEN					*)
(* and HOL_RES_THEN     = RES_THEN;					*)
(* ---------------------------------------------------------------------*)


(* ---------------------------------------------------------------------*)
(* MATCH_MP_TAC: Takes a theorem of the form 				*)
(*									*)
(*       |- !x1..xn. A ==> !y1 ... ym. B 				*)
(* 									*)
(* and matches B to the goal, reducing it to the subgoal consisting of 	*)
(* some existentially-quantified instance of A:				*)
(*									*)
(*      !v1...vi. B							*)
(* ======================= MATCH_MP_TAC |- !x1...1n. A ==> !y1...ym. B  *)
(*      ?z1...zp. A							*)
(* 									*)
(* where {z1,...,zn} is the subset of {x1,...,xn} whose elements do not *)
(* appear free in B.							*)
(*									*)
(* Added: TFM 88.03.31							*)
(* Revised: TFM 91.04.20						*)
(*									*)
(* Old version:								*)
(*									*)
(* let MATCH_MP_TAC thm:tactic (gl,g) =					*)
(*     let imp = ((PART_MATCH (snd o dest_imp) thm) g) ? 		*)
(* 	       failwith `MATCH_MP_TAC` in				*)
(*     ([gl,(fst(dest_imp(concl imp)))], \thl. MP imp (hd thl));	*)
(* ---------------------------------------------------------------------*)
local
fun efn v (tm,th) =
   let val ntm = Dsyntax.mk_exists{Bvar = v,Body = tm} 
   in 
   (ntm,Drule.CHOOSE (v, Thm.ASSUME ntm) th)
   end
in
fun MATCH_MP_TAC thm :tactic =
   let val (gvs,imp) = Dsyntax.strip_forall (Thm.concl thm) 
       val {ant,conseq} = Dsyntax.dest_imp imp 
                       handle _ => raise RESOLVE_ERR{function = "MATCH_MP_TAC",
                                                message = "Not an implication"}
       val (cvs,con) = Dsyntax.strip_forall conseq
       val th1 = Drule.SPECL cvs (Drule.UNDISCH (Drule.SPECL gvs thm))
       val (vs,evs) = partition (C Term.free_in con) gvs 
       val th2 = uncurry Thm.DISCH (itlist efn evs (ant,th1))
   in
   fn (A,g) => let val (vs,gl) = Dsyntax.strip_forall g
                   val ins = Match.match_term con gl 
                     handle _ => raise RESOLVE_ERR{function = "MATCH_MP_TAC",
                                                   message = "No match"}
                   val ith = Conv.INST_TY_TERM ins th2 
                   val ant = #ant(Dsyntax.dest_imp(Thm.concl ith)) 
                   val gth = Drule.GENL vs (Drule.UNDISCH ith) 
                      handle _ => raise RESOLVE_ERR{function = "MATCH_MP_TAC",
                                               message = "Generalized var(s)."}
               in
               ([(A,ant)], fn thl => Thm.MP (Thm.DISCH ant gth) (hd thl))
               end
   end
end;


end; (* Resolve *)
