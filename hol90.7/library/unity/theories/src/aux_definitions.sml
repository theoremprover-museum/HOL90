(* -*- Emacs Mode: sml -*- *)

(*----------------------------------------------------------------------*)
(* HOL88 system related functions					*)
(*----------------------------------------------------------------------*)
val delete_theory = fn name =>
    System.system("/bin/rm "^name^".thms "^name^".holsig")

val prove_thm = fn (name,tm,t) => save_thm(name, TAC_PROOF(([],tm),t))

(* Uniform error facility *)
fun UNITY_ERR{func,mesg} = 
      HOL_ERR{origin_structure = "Unity library",
              origin_function = func,
              message = mesg};

(*----------------------------------------------------------------------*)
(* Auxilliary definitions						*)
(*----------------------------------------------------------------------*)

val UNDISCH_ALL_TAC =
    let
	fun th_tac (th:thm) (tac:tactic) = (MP_TAC th) THEN tac
	fun u_asml (thml:thm list) = itlist  th_tac thml ALL_TAC
    in
	POP_ASSUM_LIST u_asml
    end

val UNDISCH_ONE_TAC =
    let
	fun th_tac (th:thm) (tac:tactic) = (UNDISCH_TAC (concl th)) THEN tac
	fun u_asm  (th:thm) = itlist  th_tac [th] ALL_TAC
    in
	FIRST_ASSUM u_asm
    end

val list_INDUCT = theorem "list" "list_INDUCT";

(* --------------------------------------------------------------------*)
(*   LIST_INDUCT: (thm # thm) -> thm			               *)
(*							               *)
(*     A1 |- t[[]]      A2 |- !tl. t[tl] ==> !h. t[CONS h t]           *)
(* ----------------------------------------------------------          *)
(*                   A1 u A2 |- !l. t[l]			       *)
(*							               *)
(* --------------------------------------------------------------------*)

fun LIST_INDUCT (base,step) =
   let val % = Parse.term_parser
       val alpha_ty = Parse.type_parser `:'a`
       val bool_ty = Parse.type_parser `:bool`
       val {Bvar,Body} = dest_forall(concl step)
       val {ant,conseq} = dest_imp Body
       val {Bvar=h,Body=con} = dest_forall conseq
       val P  = %`\^Bvar.^ant` 
       val b1 = genvar bool_ty
       val b2 = genvar bool_ty
       val base'  = EQ_MP (SYM(BETA_CONV (%`^P []`))) base 
       val step'  = DISCH ant (SPEC h (UNDISCH(SPEC Bvar step)))
       val hypth  = SYM(RIGHT_BETA(REFL (%`^P ^Bvar`)))
       val concth = SYM(RIGHT_BETA(REFL (%`^P(CONS ^h ^Bvar)`)))
       val IND    = SPEC P (INST_TYPE [alpha_ty |-> type_of h] list_INDUCT)
       val th1 = SUBST[{var=b1,thm=hypth},{var=b2,thm=concth}]
                      (%`^(concl step') = (^b1 ==> ^b2)`)
                      (REFL (concl step'))
       val th2 = GEN Bvar (DISCH (%`^P ^Bvar`)
                                 (GEN h(UNDISCH (EQ_MP th1 step'))))
       val th3 = SPEC Bvar (MP IND (CONJ base' th2))
   in
   GEN Bvar (EQ_MP (BETA_CONV(concl th3)) th3)
   end
   handle _ => raise UNITY_ERR{func = "LIST_INDUCT", mesg = ""};


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


(* Emacs editor information
|  Local variables:
|  mode:sml
|  sml-prog-name:"hol90"
|  End:
*)
