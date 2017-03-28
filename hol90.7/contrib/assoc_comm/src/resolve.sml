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

open Rsyntax;
fun RESOLVE_ERR{func,mesg} = 
        HOL_ERR{origin_structure = "Resolve",
                origin_function = func,
                mesg = mesg}

(* ---------------------------------------------------------------------*)
(* Resolve implicative assumptions with an antecedent			*)
(* ---------------------------------------------------------------------*)
fun ANTE_RES_THEN ttac ante : tactic =
   ASSUM_LIST (EVERY o (mapfilter (fn imp => ttac (AC_MATCH_MP imp ante))));

(* ---------------------------------------------------------------------*)
(* Definition of the primitive:						*)
(*									*)
(* IMP_RES_THEN: Resolve all assumptions against an implication.	*)
(*									*)
(* The definition uses an auxiliary (local) func, MATCH_MP, which is*)
(* just like the built-in version, but doesn't use GSPEC.		*)
(* 									*)
(* New implementation for version 1.12: fails if no MP-consequences can *)
(* be drawn, and does only one-step resolution.		[TFM 90.12.07]  *)
(* ---------------------------------------------------------------------*)

fun AC_MATCH_MP ac_eqns impth =
   let val sth = Drule.SPEC_ALL impth 
       val matchfn = Ac_tools.Acu.match_term (#ant(Dsyntax.dest_imp(Thm.concl sth))) 
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
                 handle _ => raise RESOLVE_ERR{func = "IMP_RES_THEN",
                                               mesg = "No implication"}
   in
   ASSUM_LIST 
     (fn asl => let val l = itlist(fn th => append(mapfilter(AC_MATCH_MP th) asl))
                                  ths [] 
                    val res = check (RESOLVE_ERR{func = "IMP_RES_THEN",
                                                 mesg = "No resolvents"}) l 
                    val tacs = check (RESOLVE_ERR{func = "IMP_RES_THEN",
						  mesg = "No tactics"})
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
        val imps = check (RESOLVE_ERR{func = "RES_THEN",
				      mesg = "No implication"}) ths 
        val l = itlist (fn th => append (mapfilter (AC_MATCH_MP th) aas))
                       imps [] 
        val res = check (RESOLVE_ERR{func = "RES_THEN",
				     mesg = "No resolvents"}) l 
        val tacs = check (RESOLVE_ERR{func = "RES_THEN",
				      mesg = "No tactics"})
                         (mapfilter ttac res) 
    in
    Tactical.EVERY tacs (asl,g)
    end;

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

end; (* Resolve *)
