(* ===================================================================== *)
(* FILE          : prim_rec.sml                                          *)
(* DESCRIPTION   : Primitive recursive definitions on arbitrary recursive*)
(*                 types.  Assumes the type is defined by an axiom of    *)
(*                 the form proved by the recursive types package.       *)
(*                 Translated from hol88.                                *)
(*                                                                       *)
(* AUTHOR        : (c) T. F. Melham, University of Cambridge             *)
(* DATE	         : 87.08.23                                              *)
(* TRANSLATOR    : Konrad Slind, University of Calgary                   *)
(* DATE          : September 11, 1991                                    *)
(* ===================================================================== *)


structure Prim_rec : Prim_rec_sig =
struct
open CoreHol;
open Thm Drule Term Dsyntax Match;
open Tactical Tactic;
  infix THEN;
  infix THENL;
  infix ORELSE;
open Const_spec;
open Rewrite Conv;
open Resolve;
open Lib;
open Exception;

type goal = Abbrev.goal;

infix ##
  infix |->;

fun PRIM_REC_ERR{function,message} = 
         HOL_ERR{origin_structure = "Prim_rec",
                 origin_function = function,
                 message = message}

(* remove x satisfying p from l.... giving x and the thing and rest of l*)
fun pr_remove p [] = raise PRIM_REC_ERR{function = "pr_remove",message = "[]"}
  | pr_remove p (a::A) = 
     if p a then (a, A) else (I##(fn r => (a :: r))) (pr_remove p A);


(*----------------------------------------------------------------------*)
(* derive_existence_thm th tm						*)
(*									*)
(* If th is a rec type axiom and tm is a term giving a prim rec 	*)
(* definition, derive an existence theorem for doing the definition.	*)
(* The existence theorem has cases corresponding to those in tm and	*)
(* is suitably type-instantiated.					*)
(*									*)
(* E.g. Input								*)
(*									*)
(* |- !f0 f1 f2 e. ?! fn.						*)
(*    (!x0 x1 t t'. fn(C1 t x0 t' x1) = f0(fn t)(fn t')x0 x1 t t') /\	*)
(*    (!t. fn(C2 t) = f1(fn t)t) /\             			*)
(*    (!x. fn(C3 x) = f2 x) /\     					*)
(*     (fn C4 = e)							*)
(*									*)
(*  "(!n b. Fn n C4 b = ...) /\						*)
(*   (!b n m t x t'. Fn n (C1 t' b t m) x = ...) /\			*)
(*   (!m x q. Fn m (C3 x) q = ...)"					*)
(*									*)
(* Output:								*)
(*									*)
(* |- !e f0 f2. ?fn.							*)
(*    (!g1 g2. fn C4 g1 g2 = e g1 g2) /\				*)
(*    (!g3 g4 g5 g6 g7 g8. fn(C1 g5 g3 g6 g4) g7 g8 = 			*)
(*		       f0(fn g5)(fn g6)g3 g4 g5 g6) g7 g8 /\	        *)
(*    (!g9 g10 g11. fn(C3 g9) g10 g11 = f2 g9 g10 g11)			*)
(*									*)
(* Note: the g's are genvars	(so are e ... f2)			*)
(*----------------------------------------------------------------------*)


(* val derive_existence_thm = fn : thm -> term -> thm   *)

fun derive_existence_thm th tm : thm =
   let val vars = map (genvar o type_of) (Lib.fst(strip_forall(concl th)))
       val exists = CONJUNCT1(CONV_RULE EXISTS_UNIQUE_CONV(SPECL vars th)) 
       val e_fn = #Bvar(dest_exists(concl exists))
       and conjs = strip_conj tm 
       fun splt (h::t) = 
              if (is_var h) 
              then let val (bv,C,av) = splt t
                   in ((h::bv), C, av)
                   end
              else if (is_const h orelse is_comb h)
                   then ([], h, t)
                   else raise PRIM_REC_ERR{function = "derive_existence_thm",
                                           message = "1"}
       val(bv,Con,av) = splt(snd(strip_comb(lhs(snd(strip_forall(hd conjs))))))
       val rhsfn = let val cv = genvar(type_of Con) 
                       val r = rhs(snd(strip_forall(hd conjs)))
                   in list_mk_abs(cv::(bv @ av),r) 
                   end 
       val th_inst = INST_TYPE (Lib.snd(Match.match_term e_fn rhsfn)) exists 
       fun get_c t =
          let val args = Lib.snd(strip_comb(lhs(Lib.snd(strip_forall t))))
              val c = Lib.fst(strip_comb(Lib.first (fn t=> is_const t orelse is_comb t)
                                           args))
          in if (is_const c) then c 
           else raise PRIM_REC_ERR{function="derive_existence_thm",message="2"}
          end 
       val cs  = map get_c conjs 
       and exl = CONJUNCTS (SELECT_RULE th_inst) 
       and fn1 = #Bvar(dest_exists(concl th_inst)) 
       fun same_c c cl = 
          (c = fst (strip_comb (rand (lhs (snd (strip_forall (concl cl)))))))
       fun get_ths [] exl = []
         | get_ths (a::A) exl = 
              let val (c, ex) = pr_remove (same_c a) exl
              in (c :: (get_ths A ex)) 
              end
       val ths = get_ths cs exl
       val argvars = map (genvar o type_of) (bv @ av) 
       fun ap_ths th = 
          let val v = map (genvar o type_of) (Lib.fst(strip_forall(concl th))) 
              val th1 = Lib.rev_itlist (Lib.C AP_THM) argvars (SPECL v th)
          in
          GENL (v @ argvars) th1
          end
       val th1 = LIST_CONJ (map ap_ths ths) 
       val sel = mk_select(dest_exists (concl th_inst)) 
   in
   GEN_ALL(EXISTS(mk_exists{Bvar = fn1, Body = subst[sel |-> fn1] (concl th1)},
                  sel) th1)
   end handle (e as HOL_ERR{origin_structure = "Prim_rec",
                            origin_function = "derive_existence_thm",...}) 
               => raise e
        | _ => raise PRIM_REC_ERR{function = "derive_existence_thm",
                                  message = ""};



(* mk_fn: make the function for the rhs of a clause in the existence thm  *)
(*                                                                        *)
(* returns:  1) the function                                              *)
(*      2) a list of variables that the clause should be SPECL            *)
(*      3) a pre-done beta-conversion of the rhs.                         *)

fun mk_fn (cl, Fn, bv, C, ((av, r):goal)) = 
   let val (lcl::lclvars) = Lib.snd (strip_comb (lhs (Lib.snd (strip_forall cl))))
       val m = (Lib.fst(Match.match_term lcl C))@(Lib.map2 (fn res => fn red =>
                                                {redex=red, residue=res})
                                             (bv@av) lclvars)
       val cl'= subst m (Lib.snd(strip_forall cl)) 
       val z1 = Lib.snd(strip_comb(rhs cl'))
       val nonrec = Lib.filter (is_var)  z1
       and rec1 = Lib.filter (is_comb) z1
       val recvars = map (genvar o type_of) rec1 
       val basepat = list_mk_comb(Fn, (map (genvar o type_of) bv)) 
       fun find t = 
            find_terms 
              (fn tm => Lib.can(Match.match_term(mk_comb{Rator=basepat,Rand=t})) tm
                        andalso (Lib.fst (strip_comb tm) = Fn) 
                        andalso (rand tm = t))
       fun do_subst (new,old) tm = 
          if (tm = old) 
          then new 
          else if (is_abs tm) 
               then let val {Bvar,Body} = dest_abs tm
                    in mk_abs{Bvar = Bvar, Body = do_subst(new,old) Body} 
                    end
               else if (is_comb tm) 
                    then let val {Rator,Rand} = dest_comb tm
                             val f = do_subst(new,old)
                         in mk_comb{Rator = f Rator, Rand = f Rand}
                         end 
                    else tm 
       fun mk_substs (rc,rcv) t = 
          let val occs = find (rand rc) t 
              fun args tm = Lib.snd(strip_comb (rator tm)) 
              val news = map (fn tm => list_mk_comb(rcv,args tm)) occs
          in itlist do_subst (zip news occs) t 
          end
       val r'= Lib.itlist mk_substs (Lib.zip rec1 recvars) r
       val varsub = map (fn v => {redex = v, residue = genvar (type_of v)})
                        (recvars @ nonrec) 
       val fn1 = list_mk_abs(map #residue varsub,subst varsub r') 
       fun subst_assoc _ [] = NONE
         | subst_assoc v ({redex,residue}::L) = 
                if (v = redex)
                then SOME residue
                else subst_assoc v L
       val specl = 
             map (fn v => case (subst_assoc v m) of (SOME x) => x | NONE => v)
                 (fst(strip_forall cl)) 
       val beta = LIST_BETA_CONV(list_mk_comb(fn1,snd(strip_comb(rhs cl'))))
   in
   (fn1, specl, beta) 
   end;


fun MK_FN (cl, (Fn, bv, C, g)) = mk_fn (cl, Fn, bv, C, g);


(* instantiate_existence_thm eth tm : instantiate eth to match tm   *)
(*                                                                  *)
(* E.g. INPUT:                                                      *)
(*                                                                  *)
(* |- !e f0 f2. ?fn.                                                *)
(*    (!g1 g2. fn C4 g1 g2 = e g1 g2) /\                            *)
(*    (!g3 g4 g5 g6 g7 g8. fn(C1 g5 g3 g6 g4) g7 g8 =               *)
(*           f0(fn g5)(fn g6)g3 g4 g5 g6) g7 g8 /\                  *)
(*    (!g9 g10 g11. fn(C3 g9) g10 g11 = f2 g9 g10 g11)              *)
(*                                                                  *)
(*                                                                  *)
(*  "(!n b. Fn n C4 b = ...) /\                                     *)
(*   (!b n m t x t'. Fn n (C1 t' b t m) x = ...) /\                 *)
(*   (!m x q. Fn m (C3 x) q = ...)"                                 *)
(*                                                                  *)
(* OUTPUT:                                                          *)
(*  |- ?fn. (!n b. fn C4 n b = ...) /\                              *)
(*          (!b n m t x t'. fn (C1 t' b t m) n x = ...) /\          *)
(*      (!m x q. fn (C3 x) m q = ...)                               *)



local
fun z3 [] A B C = (A, rev B, rev C)
  | z3 ((a, b, c)::L) A B C = z3 L (a::A) (b::B) (c::C)
in
fun unzip3 L = z3 L [] [] []
end;

fun instantiate_existence_thm eth tm :thm = 
   let val cls = map (Lib.snd o strip_forall) (strip_conj tm) 
       fun splt [] = raise PRIM_REC_ERR{function = "instantiate_existence_thm",
                                        message = "splt.[]"}
         | splt (a::A) = 
             if (is_var a)
             then let val (bv,C,av) = splt A 
                  in ((a :: bv),C,av)
                  end
             else if (is_const a) orelse (is_comb a) 
                  then ([], a, A) 
                  else raise PRIM_REC_ERR{function="instantiate_existence_thm",
                                          message = "splt.non-empty"}
       fun dest tm = 
          let val {lhs,rhs = r} = dest_eq tm
              val (Fn,(bv,C,av)) = ((I ## splt) o strip_comb) lhs
          in (Fn,bv,C,((av,r):goal))
          end
       val destcl = (map dest cls) 
       val ecls = strip_conj(#Body(dest_exists(Lib.snd(strip_forall(concl eth))))) 
       val (fns,spec,beta) = unzip3 (map MK_FN (Lib.zip ecls destcl))
       val ethsp = SPECL fns eth 
       val conjs = map (Lib.uncurry SPECL) 
                       (Lib.combine(spec,CONJUNCTS(SELECT_RULE ethsp))) 
       fun rule (th1,th2) = CONV_RULE (RAND_CONV (REWR_CONV th1)) th2 
       val th = LIST_CONJ (map (GEN_ALL o rule) (Lib.zip beta conjs)) 
       val fn1 = #Bvar(dest_exists (concl ethsp)) 
       and fsel = mk_select(dest_exists(concl ethsp)) 
   in
   EXISTS(mk_exists{Bvar=fn1, Body=subst[fsel |-> fn1] (concl th)},fsel) th
   end handle (e as HOL_ERR{origin_structure = "Prim_rec",
                            origin_function = "instantiate_existence_thm",...})
               => raise e
        | _ => raise PRIM_REC_ERR{function = "instantiate_existence_thm",
                                  message = ""};


(* prove_rec_fn_exists th tm                               *)
(*                                                         *)
(* Given 1) th, a recursion theorem (type axiom)           *)
(*       2) tm, the specification of a recursive function  *)
(*                                                         *)
(* proves that such a function exists.                     *)

(* Quantify the equations of the function spec.            *)

fun closeup tm = 
   let fun lvars t = 
          set_diff (free_varsl(snd(strip_comb(lhs(snd (strip_forall t))))))
                   (fst(strip_forall t)) 
   in list_mk_conj(map (fn tm => list_mk_forall(lvars tm,tm)) (strip_conj tm))
   end;


(* MJCG 17/1/89: added test for attempted redefinition of a constant and *)
(* code to propagate failure message					 *)

fun prove_rec_fn_exists th tm : thm = 
   let val eth = derive_existence_thm th tm 
       val ith = instantiate_existence_thm eth tm 
       fun get_avars tm  = 
	  if (is_var (rand tm)) 
          then get_avars (rator tm)
          else (Lib.snd(strip_comb (rator tm)),rand tm)
       val cl = Lib.snd(strip_forall(hd(strip_conj tm))) 
       val fn1 = Lib.fst(strip_comb(lhs cl)) 
       and (av,tv) = ((map (genvar o type_of)) ## (genvar o type_of))
	             (get_avars (lhs cl)) 
   in
   if (is_const fn1)
   then raise PRIM_REC_ERR{function = "prove_rec_fn_exists",
                       message = (#Name(dest_const fn1)^" previously defined")}
   else let val goal = ([],mk_exists{Bvar = fn1, Body = closeup tm})
            fun etac th = 
               let val efn = fst(strip_comb(lhs(snd(strip_forall(concl th))))) 
               in EXISTS_TAC (list_mk_abs(av@[tv],list_mk_comb(efn,tv::av)))
               end  
            fun fn_beta th (A,gl) = 
 	       let val efn = Lib.fst(strip_comb(lhs(Lib.snd(strip_forall(concl th)))))
                   val eabs = (list_mk_abs(av@[tv],list_mk_comb(efn,tv :: av)))
	           val epat = list_mk_comb(eabs, map (genvar o type_of)
                                                     (av @ [tv]))
	           val tms = find_terms(fn tm => Lib.can(Match.match_term epat) tm)
                                       gl
               in PURE_ONCE_REWRITE_TAC (map LIST_BETA_CONV tms) (A,gl) 
               end
        in
        GEN_ALL(TAC_PROOF(goal,
                STRIP_ASSUME_TAC ith THEN 
                FIRST_ASSUM etac THEN
                REPEAT STRIP_TAC THEN 
                FIRST_ASSUM fn_beta THEN
                FIRST_ASSUM MATCH_ACCEPT_TAC))
       end
   end
   handle (e as HOL_ERR{origin_structure = "Prim_rec",
                        origin_function = "prove_rec_fn_exists",...}) 
           => raise e
        | _ => raise PRIM_REC_ERR{function = "prove_rec_fn_exists",
                                  message = "Can't solve recursion equation"};

(* Make a new recursive function definition.				*)
fun new_recursive_definition {name,fixity,rec_axiom,def} = 
 let val thm = prove_rec_fn_exists rec_axiom def
 in
 new_specification
    {name = name, sat_thm = thm,
     consts =  [{fixity = fixity, 
                 const_name = #Name(dest_var(#Bvar(dest_exists(concl thm))))}]}
 end;

end; (* Prim_rec *)
