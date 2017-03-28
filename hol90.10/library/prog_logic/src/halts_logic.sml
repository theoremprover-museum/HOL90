signature HALTS_LOGIC =
sig
 type term = CoreHol.Term.term
 type thm = CoreHol.Thm.thm
 type tactic = Abbrev.tactic

        (* forward proof rules *)

	val ASSIGN_AX  : term -> term -> thm

	val SEQ_RULE   : thm * thm -> thm
	val SEQL_RULE  : thm list -> thm
	val IF1_RULE   : thm * thm -> thm
	val IF2_RULE   : thm * thm -> thm
        val WHILE_RULE : thm -> thm

	val PRE_STRENGTH_RULE : thm * thm -> thm
	val POST_WEAK_RULE    : thm * thm -> thm

        (* tactics *)

	val SKIP_TAC   : tactic
	val ASSIGN_TAC : tactic
	val SEQ_TAC    : tactic
	val IF1_TAC    : tactic
	val IF2_TAC    : tactic
        val WHILE_TAC  : tactic
	val VC_TAC     : tactic
end;

(* ========================================================================= *)
(*  FILE          : halts_logic.sml                                          *)
(*  DESCRIPTION   : Provides rules and tactics for Hoare Logic, using        *)
(*                  theorems in theory "halts_thms". The halts theory is     *)
(*                  the theory of TOTAL CORRECTNESS specification.           *)
(*                                                                           *)
(*  AUTHOR        : Matthew Morley, University of Edinburgh                  *)
(*  DATE          : January 1993                                             *)
(*  HISTORY       : Specialised to HOL90 from HOL88 prog_lib library.        *)
(*                  Assignment Axiom now deals with multi-assignment.        *)
(* ========================================================================= *)

functor Halts_Logic (structure Syntax : SYNTAX
                     structure Trans  : TRANSLATION
                     structure Holm   : HOL_MATCH
                     structure Bnd    : BND_CONV) : HALTS_LOGIC =
    struct

 type term = CoreHol.Term.term
 type thm = CoreHol.Thm.thm
 type tactic = Abbrev.tactic
 type goal = Abbrev.goal;

    structure Char = Portable.Char;
    structure String = Portable.String

    structure S = Syntax
    structure T = Trans
    structure B = Bnd
    
    exception FAIL
    
  open Lib Exception CoreHol Parse;
  open Term Dsyntax Thm Theory Drule Tactical Tactic Conv
  infix THEN ORELSE;

    fun LOGIC_ERR{function,message} = 
	HOL_ERR{origin_structure="Halts_Logic",
		origin_function=function,
		message=message}

    open Rsyntax;
    val SKIP_THM    = theorem "halts_thms" "SKIP_T_THM"
    val ASSIGN_THM  = theorem "halts_thms" "ASSIGN_T_THM"
    val SEQ_THM     = theorem "halts_thms" "SEQ_T_THM"
    val IF1_THM     = theorem "halts_thms" "IF1_T_THM"
    val IF2_THM     = theorem "halts_thms" "IF2_T_THM"
    val WHILE_THM   = theorem "halts_thms" "WHILE_T_THM"

    val PRE_STRENGTH_THM = theorem "halts_thms" "PRE_STRENGTH_T_THM"
    val POST_WEAK_THM    = theorem "halts_thms" "POST_WEAK_T_THM"
	
    val TRANS_THM = T.TRANS_THM
    val HOL_MATCH_MP = Holm.HOL_MATCH_MP

    (* ****************************************************************** *)
    (*                                                                    *)
    (* Forward proof rules for total correctness are much the same as for *)
    (* partial correcness dealt with in hoare_logic.sml. The WHILE_RULE   *)
    (* is where the differences become apparent, of course.               *)
    (*                                                                    *)
    (* ****************************************************************** *)


    fun ASSIGN_AX p c = 
	let val (x,e) = S.dest_assign c
	    val th1 = SPECL [p,x,e] ASSIGN_THM
	    val (p',_,_) = (S.dest_t_spec o concl) th1
	    val t1 = (#Body o dest_abs ) p'
	    val t2 = (hd o tl o snd o strip_comb o #Rand o dest_comb) t1
	    val th2 = RIGHT_CONV_RULE (B.SUBS_CONV (BETA_CONV t2)) 
		(BETA_CONV t1)
	    val th3 = RIGHT_CONV_RULE (ONCE_DEPTH_CONV B.BND_CONV) th2
	    val th4 = ABS (--`s:string -> num`--) th3
	in 
	    SUBS [th4] th1
	end


    fun SEQ_RULE(hth1,hth2) = MATCH_MP SEQ_THM (CONJ hth1 hth2)


    fun SEQL_RULE thl =
	if thl = [] then raise FAIL
	else if (tl thl) = [] then hd thl
	     else SEQL_RULE(SEQ_RULE(hd thl,hd(tl thl))::tl(tl thl))
		 handle FAIL => 
                   raise LOGIC_ERR{function= "SEQL_RULE",
				   message="Empty command sequence."}


    fun PRE_STRENGTH_RULE (th,hth) = 
	HOL_MATCH_MP PRE_STRENGTH_THM (CONJ (TRANS_THM th) hth)


    fun POST_WEAK_RULE(hth,th) = 
	HOL_MATCH_MP POST_WEAK_THM (CONJ hth (TRANS_THM th))


    fun IF1_RULE(hth,th) = HOL_MATCH_MP IF1_THM (CONJ hth (TRANS_THM th))


    fun IF2_RULE (hth1,hth2) = HOL_MATCH_MP IF2_THM (CONJ hth1 hth2)


    (* ****************************************************************** *)
    (*                                                                    *)
    (* While-rule WHILE_RULE:                                             *)
    (*                                                                    *)
    (*   |- T_SPEC({P /\ B /\ X=n},C,{P /\ X<n})                          *)
    (*  -----------------------------------------                         *)
    (*  |- T_SPEC({P},MK_WHILE({B},C),{P /\ ~B})                          *)
    (*                                                                    *)
    (* ****************************************************************** *)


    fun WHILE_RULE hth =
        let val (p,_,_) = S.dest_t_spec(concl(SPEC_ALL hth))
            val {lhs,rhs} = dest_eq(#conj2(dest_conj(
                                    #conj2(dest_conj(#Body(dest_abs p))))))
            val hth1 = GEN (--`n:num`--) 
                         (INST [{residue=(--`n:num`--),redex=rhs}] hth)
        in
	    HOL_MATCH_MP WHILE_THM hth1
        end

    (* ****************************************************************** *)
    (*                                                                    *)
    (* Tactics are defined here for generating verification conditions    *)
    (* from annotated partial correctness specifications. The idea is     *)
    (* that a goal (with annotations)                                     *)
    (*                                                                    *)
    (*     T_SPEC([P],C,[Q])                                              *)
    (*                                                                    *)
    (* is achieved by a theorem (without annotations)                     *)
    (*                                                                    *)
    (*     |- T_SPEC([P],[C],[Q])                                         *)
    (*                                                                    *)
    (* The validations of these tactics use the derived rules of Hoare    *)
    (* logic above. Note that the theorems generated do not technically   *)
    (* achieve the goal, since they do not contain the annotations.       *)
    (*                                                                    *)
    (* ****************************************************************** *)
    (* ****************************************************************** *)
    (*
       TACTICS PROVIDED
       ################


                         [P] SKIP [Q]
       SKIP_TAC          ============
                           P ==> Q

                         [P] X:=E [Q]
       ASSIGN_TAC        ============
                         P ==> Q[E/X]


                         [P] C1; ...  Cn; X:=E [Q]
       SEQ_TAC           =========================
                          [P] C1; ... Cn [Q[E/X]] 

    
                          [P] C1; ... Cn; ASSERT R; C [Q]
       SEQ_TAC           =================================
                         [P] C1; ... Cn [R]  ,   [R] C [Q]


                                [P] IF B THEN C [Q]
       IF1_TAC           ==================================
                         [P /\ B] C [Q]   ,   P /\ ~B ==> Q


                              [P] IF B THEN C1 ELSE C2 [Q]
       IF2_TAC           ======================================
                         [P /\ B] C1 [Q]   ,   [P /\ ~B] C2 [Q]


       WHILE_T_TAC

                 [P] WHILE B SEQ [INVARIANT R; VARIANT X; C] [Q]
         ==============================================================
         P ==> R   ,   [R /\ B /\ X=n] C [R /\ X<n]   ,   R /\ ~B ==> Q
                                                                          *)
    (*                                                                    *)
    (* ****************************************************************** *)

    fun SKIP_TAC ((asl,t):goal) =
	let val (p,skip,q) = S.dest_t_spec t
	    val SKIP = (--`MK_SKIP`--)
	    val p' = T.untrans_term p
	    and q' = T.untrans_term q
		
	    val just = fn [th] => POST_WEAK_RULE(SPEC p SKIP_THM, th)
	in
	    if skip = SKIP
		then ([(asl,(--`^p' ==> ^q'`--))],just)
	    else raise FAIL
	end

    fun ASSIGN_TAC ((asl,t):goal) =
	let val (p,c,q) = S.dest_t_spec t
	    val (x,e) = S.dest_assign c
	    val p' = T.untrans_term p
	    and q' = T.untrans_term q
	    val s_list = [{residue= T.untrans_term e, redex= T.unprime x}]

	    val just = fn [th] => PRE_STRENGTH_RULE(th, ASSIGN_AX q c)
	in
	    ([(asl,mk_imp{ant=p', conseq= subst s_list q'})],just)
	end


    fun SEQ_TAC ((asl,t):goal) =
	(let val (P,SEQ,Q) = S.dest_t_spec t 
	     val (c::seql) = (rev o S.dest_seql) SEQ    
	     val (x,e) = S.dest_assign c
	     val {Bvar=s,Body=q} = dest_abs Q
	     val {Bvar=v,Body=e'} = dest_abs e
	     val s_list = [{residue= e', redex= mk_comb{Rator=v,Rand=x}}]
		
	     val Q' = mk_abs{Bvar=s,Body= subst s_list q}
	     val just = fn [hth] => SEQ_RULE(hth, ASSIGN_AX Q c)
	 in
	     if null(tl seql)
		 then ([(asl,(--`T_SPEC(^P, ^(hd seql), ^Q')`--))],just)
	     else ([(asl,(--`T_SPEC(^P, 
				    ^(S.mk_seql (rev seql)), ^Q')`--))]
		   ,just)
	 end) handle _ => 
	(let val (P,SEQ,Q) = S.dest_t_spec t 
	     val (c::seql) = (rev o S.dest_seql) SEQ    
	     val (seql',R) = ((tl seql),S.dest_assert(hd seql))
		 
	     val just = fn [th1,th2] => SEQ_RULE(th1,th2)
	 in
	     if null(tl seql')
		 then
		     ([(asl,(--`T_SPEC(^P, ^(hd seql'), ^R)`--)),
		       (asl,(--`T_SPEC(^R, ^c, ^Q)`--))],just)
	     else
		 ([(asl,(--`T_SPEC(^P, ^(S.mk_seql (rev seql')), ^R)`--)),
		   (asl,(--`T_SPEC(^R, ^c, ^Q)`--))],just)
	 end)

    fun IF1_TAC ((asl,t):goal) =
	let val (P,IF1,Q) = S.dest_t_spec t 
	    val (B,c) = S.dest_if1 IF1
	    val p = T.untrans_term P
	    and q = T.untrans_term Q
	    and b = T.untrans_term B
	    val {Bvar=s,Body=p'} = dest_abs P
	    and {Body=b',...} = dest_abs B
	in
	    ([(asl,(--`T_SPEC((\^s.^p' /\ ^b'), ^c, ^Q)`--)),
	      (asl,(--`^p /\ ~^b ==> ^q`--))],
	     fn [hth,th] => IF1_RULE(hth,th))
	end


    fun IF2_TAC ((asl,t):goal) =
	let val (P,IF2,Q) = S.dest_t_spec t 
	    val (B,c,c') = S.dest_if2 IF2
	    val {Bvar=s,Body=p'} = dest_abs P
	    and {Body=b',...}    = dest_abs B
	in
	    ([(asl,(--`T_SPEC((\^s. ^p' /\ ^b'), ^c, ^Q)`--)),
	      (asl,(--`T_SPEC((\^s. ^p' /\ ~^b'), ^c', ^Q)`--))],
	     fn [hth1,hth2] => IF2_RULE(hth1,hth2))
	end

    fun WHILE_TAC ((asl,t):goal) =
	let val (p,W,q) = S.dest_t_spec t 
            val (b,body) = S.dest_while W
            val cl = S.dest_seql body
            val r = S.dest_invariant(hd cl)
            and v = S.dest_variant(hd (tl cl))

            val c = if null(tl(tl(tl cl))) then hd(tl(tl cl)) 
		    else S.mk_seql(tl(tl cl))

            val p'     = T.untrans_term p
	    and q'     = T.untrans_term q
	    and r'     = T.untrans_term r
	    and v'     = T.untrans_term v
	    and b'     = T.untrans_term b
	    and {Bvar=sr,Body=r''} = dest_abs r
	    and {Bvar=sv,Body=v''} = dest_abs v
	    and {Bvar=sb,Body=b''} = dest_abs b

            val n = variant (free_varsl [p,W,q]) 
		(mk_var{Name=
			String.str
			(Char.chr
			 (32 + Char.ord
			  (hd(String.explode
			      ((#Name o dest_var) v'))))),
                        Ty=(==`:num`==)})
  
            val just = fn [th1,th2,th3] => 
                  POST_WEAK_RULE(PRE_STRENGTH_RULE(th1, WHILE_RULE th2), th3)
	in
	    ([(asl,(--`^p' ==> ^r'`--)),
	      (asl,(--`T_SPEC((\^sr. ^r'' /\ ^b'' /\ (^v'' = ^n)), 
                               ^c, 
                               (\^sr. ^r'' /\ (^v'' < ^n)))`--)),
	      (asl,(--`^r' /\ ~^b' ==> ^q'`--))],just)
	end

    val VC_TAC =
	REPEAT(ASSIGN_TAC 
	   ORELSE SKIP_TAC 
	   ORELSE SEQ_TAC 
	   ORELSE IF1_TAC 
	   ORELSE IF2_TAC
           ORELSE WHILE_TAC)

    end (* Functor Halts_Logic() *)
