(* ===================================================================== *)
(* FILE          : tactical.sml                                          *)
(* DESCRIPTION   : Functions that glue tactics together. From LCF, and   *)
(*                 added to through the years. Translated from hol88.    *)
(*                                                                       *)
(* AUTHORS       : (c) University of Edinburgh and                       *)
(*                     University of Cambridge, for hol88                *)
(* TRANSLATOR    : Konrad Slind, University of Calgary                   *)
(* DATE          : September 11, 1991                                    *)
(* ===================================================================== *)


structure Tactical :Tactical_sig =
struct

open Base_logic;

structure Thm = Base_logic.Thm;

fun TACTICAL_ERR{function,message} = HOL_ERR{origin_structure = "Tactical",
					     origin_function = function,
					     message = message}


(* TAC_PROOF (g,tac) uses tac to prove the goal g *)
fun TAC_PROOF (g,(tac:tactic)) =
   case (tac g)
     of ([],p) => p []
      |     _  => raise TACTICAL_ERR{function = "TAC_PROOF",
				     message = "unsolved goals"};


fun prove(t,tac) = TAC_PROOF(([],t), tac);
fun store_thm (name, tm, tac) = Theory.save_thm (name, prove (tm, tac));
    
(* Provide a function (tactic) with the current assumption list
*)
fun ASSUM_LIST (aslfun: (Thm.thm list -> tactic)) ((asl,w):goal) =
    aslfun (map Thm.ASSUME asl) (asl,w);

(* Pop the first assumption and give it to a function (tactic) *)
fun POP_ASSUM (thfun: thm_tactic) (((assum::asl), w):goal) = 
               thfun (Thm.ASSUME assum) (asl,w);

(* Pop off the entire assumption list and give it to a function (tactic) *)
fun POP_ASSUM_LIST (asltac: Thm.thm list -> tactic) ((asl,w):goal) =  
                    asltac (map Thm.ASSUME asl) ([],w);

fun mapshape [] _ _ =  []
  | mapshape (n1::nums) (f1::funcs) args = 
       let val (f1_args,args') = split_after n1 args
       in 
       (f1 f1_args)::(mapshape nums funcs args')
       end;


infix THEN;
infix THENL;
infix ORELSE;

(*
 * fun (tac1:tactic) THEN (tac2:tactic) : tactic = fn g =>
 *    let val (gl,p) = tac1 g 
 *        val (gll,pl) = unzip(map tac2 gl) 
 *    in
 *    (flatten gll, (p o mapshape(map length gll)pl))
 *    end;
 *******)

(* fun (tac1:tactic) THEN (tac2:tactic) :tactic = fn g =>
 *    let val (gl,vf) = tac1 g
 *        val (G,V,lengths) = 
 *           itlist (fn goal => fn (G,V,lengths) =>
 *                     case (tac2 goal) 
 *                       of ([],vfun) => let val th = vfun []
 *                                       in
 *                                       (G, (fn [] => th)::V, 0::lengths)
 *                                       end
 *                        | (goals,vfun) => (goals@G, vfun::V, 
 *                                           (length goals)::lengths))
 *                  gl ([],[],[])
 *    in
 *    case G
 *      of [] => ([], let val th = vf (map (fn f => f[]) V)
 *                    in
 *                    fn [] => th
 *                    end)
 *       | _ => (G, (vf o mapshape lengths V))
 *    end;
 ************)

fun (tac1:tactic) THEN (tac2:tactic) :tactic = fn g =>
   let val (gl,vf) = tac1 g
   in case (itlist (fn goal => fn (G,V,lengths) =>
                    case (tac2 goal) 
                      of ([],vfun) => let val th = vfun []
                                      in
                                      (G, (fn [] => th)::V, 0::lengths)
                                      end
                       | (goals,vfun) => (goals@G, vfun::V, 
                                          (length goals)::lengths))
                 gl ([],[],[]))
        of ([],V,_) => ([], let val th = vf (map (fn f => f[]) V)
                            in fn [] => th
                            end)
         | (G,V,lengths) => (G, (vf o mapshape lengths V))
   end
   handle HOL_ERR{origin_structure,origin_function,message}
   => raise TACTICAL_ERR{function = "THEN",
                message = (origin_structure^"."^origin_function^": "^message)};


(*
 * fun (tac1:tactic) THENL (tac2l : tactic list) : tactic = fn g =>
 *    let val (gl,p) = tac1 g  
 *        val tac2gl = zip tac2l gl 
 *        val (gll,pl) = unzip (map (fn (tac2,g) => tac2 g) tac2gl)
 *    in
 *    (flatten gll, p o mapshape(map length gll) pl)
 *    end
 *    handle HOL_ERR{origin_structure,origin_function,message} =>
 *        raise TACTICAL_ERR{function = "THENL",
 * 			  message = (origin_structure^"."^origin_function^": "
 * 				     ^message)};
 *******)
fun (tac1:tactic) THENL (tacl:tactic list) :tactic = fn g =>
   let val (gl,vf) = tac1 g
       val (G,V,lengths) = 
          itlist2 (fn goal => fn tac => fn (G,V,lengths) =>
                    case (tac goal) 
                      of ([],vfun) => let val th = vfun []
                                      in
                                      (G, (fn [] => th)::V, 0::lengths)
                                      end
                       | (goals,vfun) => (goals@G, vfun::V, 
                                          (length goals)::lengths))
                 gl tacl ([],[],[])
   in
   case G
     of [] => ([], let val th = vf (map (fn f => f[]) V)
                   in
                   fn [] => th
                   end)
      | _ => (G, (vf o mapshape lengths V))
   end
   handle HOL_ERR{origin_structure,origin_function,message}
   => raise TACTICAL_ERR{function = "THENL",
                         message = (origin_structure^"."^origin_function^": "
                                   ^message)};

fun (tac1:tactic) ORELSE (tac2:tactic) :tactic = 
   fn g => (tac1 g) handle _ => tac2 g ;

(* Fail with the given token.  Useful in tactic programs to check that a 
   tactic produces no subgoals.  Write

	TAC  THEN  FAIL_TAC "TAC did not solve the goal"
*)
fun FAIL_TAC tok (g:goal) = raise TACTICAL_ERR{function = "FAIL_TAC",
					       message = tok};

(* Tactic that succeeds on no goals;  identity for ORELSE *)
val NO_TAC = FAIL_TAC "NO_TAC";

(* Tactic that succeeds on all goals;  identity for THEN *)
val ALL_TAC:tactic = fn (g:goal) => ([g],hd);

fun TRY tac = tac ORELSE ALL_TAC;

(* The abstraction around g is essential to avoid looping, due to applicative
   order semantics
*)
fun REPEAT tac g = ((tac THEN REPEAT tac) ORELSE ALL_TAC) g ;

(* Check whether a theorem achieves a goal, using no extra assumptions *)
fun achieves th ((asl,w):goal) =
    (Term.aconv (Thm.concl th) w) andalso
    (all (fn h => (exists (Term.aconv h)) asl) (Thm.hyp th));


(* Check the goal list and proof returned by a tactic.
 *    At top-level, it is convenient to type "chktac it;"
 * 
 *    MJCG 17/1/89 for HOL88: mk_thm used instead of mk_fthm. This
 *    introduces slight insecurity into the system, but since chktak
 *    is assignable this insecurity can be removed by doing:
 * 
 *    chktak := fn (gl,prf) => raise TACTICAL_ERR{function = "chktac",
 *                                                message = ""};
 *********)

val chktac = ref 
   (fn (gl,(prf:Thm.thm list -> Thm.thm)) => prf(map Thm.mk_tac_thm gl));

(* Check whether a prospective (goal list, proof) pair is valid.
 *  MJCG 17/1/89 for HOL88: "falsity.asl" changed to "asl".
 *******)
fun check_valid ((asl,w):goal) (tac_res)  =
   achieves ((!chktac) tac_res) (asl, w);

(* Tactical to make any tactic valid.
 *    "VALID tac" is the same as "tac", except it will fail in the cases where
 *    "tac" returns an invalid proof. 
 * 
 *    VALID uses mk_thm; the proof could assign its arguments to 
 *    global theorem variables, making them accessible outside.
 * 
 *    This kind of insecurity is very unlikely to lead to accidental proof of 
 *    false theorems; see comment preceding check_valid for how to remove 
 *    insecurity.
 * 
 *    Previously mk_fthm was used by check_valid instead of mk_thm (see 
 *    hol-drule.ml), but this lead to problems with tactics (like resolution) 
 *    that checked for "F". A possible solution would be to use another 
 *    constant that was defined equal to F.
 ****************************)
fun VALID (tac:tactic) :tactic = fn (g:goal) =>
   let val tac_res = tac g 
   in if check_valid g tac_res
      then tac_res
      else raise TACTICAL_ERR{function = "VALID",message = "Invalid tactic"}
   end;

(* Tactical quantifiers -- Apply a list of tactics in succession. *)


(* Uses every tactic.
 *    EVERY [TAC1;...;TACn] =  TAC1  THEN  ...  THEN  TACn
 ********)
fun EVERY tacl = itlist (curry (op THEN)) tacl ALL_TAC;


(* Uses first tactic that succeeds.
 *    FIRST [TAC1;...;TACn] =  TAC1  ORELSE  ...  ORELSE  TACn
 ***********)
local
exception NO_ANSWER
fun first_answer f [] = raise NO_ANSWER
  | first_answer f (a::rst) = (f a) 
                              handle _ => first_answer f rst;
in
fun FIRST (tacl: tactic list): tactic = 
   fn g => first_answer (fn tac => tac g) tacl
           handle _ => NO_TAC g
end;

fun MAP_EVERY tacf lst  =  EVERY (map tacf lst);

fun MAP_FIRST tacf lst =  FIRST (map tacf lst);


(*Call a thm-tactic for every assumption *)
val EVERY_ASSUM : thm_tactic -> tactic = ASSUM_LIST o MAP_EVERY;


(* Call a thm-tactic for the first assumption at which it succeeds. *)
fun FIRST_ASSUM (ttac:Thm.thm->tactic): tactic = fn (A,g)  =>
   let fun find ttac [] = raise TACTICAL_ERR{function = "FIRST_ASSUM",
					     message = ""}
         | find ttac (a::L) = ttac (Thm.ASSUME a) (A,g)
                              handle _ => find ttac L
   in
   find ttac A
   end;



(* Split off a new subgoal and provide it as a theorem to a tactic
 * 
 *     SUBGOAL_THEN wa (\tha. tac)
 * 
 * makes a subgoal of wa, and also assumes wa for proving the original goal.
 * Most convenient when the tactic solves the original goal, leaving only the
 * new subgoal wa.
 ***********)
fun SUBGOAL_THEN wa (ttac: thm_tactic) (asl,w) =
    let val (gl,p) = ttac (Thm.ASSUME wa) (asl,w) 
    in
    ((asl,wa)::gl,(fn (tha::thl) => Drule.PROVE_HYP tha (p thl)))
    end;

(* A tactical that makes a tactic fail if it has no effect *)
fun CHANGED_TAC (tac:tactic) g =
 let val (gl,p) = tac g
 in if (Lib.set_eq gl [g]) 
    then raise TACTICAL_ERR{function = "CHANGED_TAC", message = "no change"}
    else (gl,p)
 end;

end;  (* Tactical *)
