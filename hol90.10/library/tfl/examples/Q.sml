(*---------------------------------------------------------------------------
 * A bunch of functions that fold quotation parsing in, sometimes to good
 * effect.
 *---------------------------------------------------------------------------*)

structure Q :Qsig =
struct
open Rsyntax;

fun Q_ERR{func,mesg} = 
    HOL_ERR{origin_structure = "Q",
            origin_function = func, message = mesg};

val ptm = Parse.term_parser;
val pty = Parse.type_parser;

(* constrain parsed term to have a given type *)
fun ptm_with_ty qtm ty = 
   let fun trail s = [QUOTE (s^"):"), ANTIQUOTE(ty_antiq ty), QUOTE""]
   in
   ptm (case (Lib.front_last qtm)
          of ([],QUOTE s) => trail ("("^s)
           | (QUOTE s::rst, QUOTE s') => (QUOTE ("("^s)::rst) @ trail s'
           | _ => raise Q_ERR{func="ptm_with_ty",mesg="badly formed quote"})
   end;

(* coerce parsed term to be boolean *)
fun btm q = ptm_with_ty q bool;

val mk_term_rsubst = 
  map (fn {redex,residue} => 
          let val residue' = ptm residue
              val redex' = ptm_with_ty redex (type_of residue')
          in {redex = redex', residue = residue'}
          end);


val mk_type_rsubst = map (fn {redex,residue} => 
                              {redex = pty redex,
                               residue = pty residue});



fun W f x = f x x;
(* The jrh abomination *)
local val bool = Parse.type_parser`:bool`
fun bval w t = (type_of t = bool)
                andalso (can (find_term is_var) t) 
                 andalso (free_in t w)
in
val TAUT_CONV =
  C (curry prove)
    (REPEAT GEN_TAC THEN (REPEAT o CHANGED_TAC o W)
      (C (curry op THEN) (Rewrite.REWRITE_TAC[]) o BOOL_CASES_TAC o hd 
                    o sort free_in
                    o W(find_terms o bval) o snd))
  o btm
end;

fun store_thm(s,q,t) = Tactical.store_thm(s,btm q,t);
fun prove q t = Tactical.prove(btm q,t);
fun new_definition(s,q) = Const_def.new_definition(s,btm q);
fun new_infix_definition(s,q,f) = Const_def.new_infix_definition(s,btm q,f);

val ABS = Thm.ABS o ptm;
val BETA_CONV = Thm.BETA_CONV o ptm;
val REFL = Thm.REFL o ptm;

fun DISJ1 th = Drule.DISJ1 th o btm;
val DISJ2 = Drule.DISJ2 o btm;


(* val GEN = Drule.GEN o ptm; *)
fun GEN [QUOTE s] th =
     let val V = free_vars (concl th)
     in
     case (Lib.assoc2 s (Lib.zip V (map (#Name o dest_var) V)))
       of NONE => raise Q_ERR{func = "GEN", mesg = "variable not found"}
        | (SOME (v,_)) => Drule.GEN v th
     end
  | GEN _ _ = raise Q_ERR{func = "GEN", mesg = "unexpected quote format"}

fun SPEC q = 
    W(Drule.SPEC o ptm_with_ty q o (type_of o #Bvar o dest_forall o concl));

val SPECL = rev_itlist SPEC;
val ISPECL = Drule.ISPECL o map ptm;
val ID_SPEC = W(Drule.SPEC o (#Bvar o dest_forall o concl))


fun SPEC_TAC (q1,q2) = 
   let val tm1 = ptm q1
   in Tactic.SPEC_TAC(tm1, ptm_with_ty q2 (type_of tm1))
   end;

(* Generalizes first free variable with given name to itself. *)

fun ID_SPEC_TAC [QUOTE s] (g as (_,w)) =
     let val V = free_vars w
     in case (Lib.assoc2 s (Lib.zip V (map (#Name o dest_var) V)))
          of NONE => raise Q_ERR{func="ID_SPEC_TAC",mesg="variable not found"}
           | (SOME (v,_)) => Tactic.SPEC_TAC(v,v) g
     end
  | ID_SPEC_TAC _ _ = raise Q_ERR{func = "ID_SPEC_TAC", 
                                  mesg = "unexpected quote format"}
   
val EXISTS = Drule.EXISTS o (btm##btm);

val EXISTS_TAC = fn q => 
  W(Tactic.EXISTS_TAC o ptm_with_ty q o (type_of o #Bvar o dest_exists o snd));

fun ID_EX_TAC(g as (_,w)) = Tactic.EXISTS_TAC (#Bvar(Dsyntax.dest_exists w)) g;

val X_CHOOSE_THEN = fn q => fn ttac =>
      W(C X_CHOOSE_THEN ttac o ptm_with_ty q 
                             o (type_of o #Bvar o dest_exists o concl));
val X_CHOOSE_TAC = C X_CHOOSE_THEN Tactic.ASSUME_TAC;

val DISCH = Thm.DISCH o btm;
val PAT_UNDISCH_TAC = fn q => 
     W(Tactic.UNDISCH_TAC o first (can (match_term (ptm q))) o fst);
fun UNDISCH_THEN q ttac = PAT_UNDISCH_TAC q THEN DISCH_THEN ttac;
val UNDISCH_TAC = Tactic.UNDISCH_TAC o btm;
val num_CONV = Num_conv.num_CONV o ptm

val SUBGOAL_THEN = Tactical.SUBGOAL_THEN o btm
val ASSUME = ASSUME o btm
val X_GEN_TAC = fn q =>
  W(Tactic.X_GEN_TAC o ptm_with_ty q o (type_of o #Bvar o dest_forall o snd))

fun X_FUN_EQ_CONV q =
 W(Conv.X_FUN_EQ_CONV o ptm_with_ty q 
                      o (hd o #Args o dest_type o type_of o lhs));

infix 5 -->
fun (ty1 --> ty2) = mk_type{Tyop="fun",Args = [ty1,ty2]};
val list_mk_type = itlist (curry(op -->));

fun skolem_ty tm =
 let val (V,tm') = Dsyntax.strip_forall tm
 in if V<>[] then list_mk_type(map type_of V) (type_of(#Bvar(dest_exists tm')))
    else raise Q_ERR{func="XSKOLEM_CONV",mesg="no universal prefix"} 
  end;

fun X_SKOLEM_CONV q = W(Conv.X_SKOLEM_CONV o ptm_with_ty q o skolem_ty)

fun AP_TERM (q as [QUOTE s]) th = 
   let val {const,...} = Term.const_decl s
       val pat = hd(#Args(Type.dest_type(Term.type_of const)))
       val ty = Term.type_of (#lhs(Dsyntax.dest_eq (Thm.concl th)))
       val theta = Match.match_type pat ty
   in Drule.AP_TERM (Term.inst theta const) th
   end
   handle _ => Drule.AP_TERM(ptm q) th;


fun AP_THM th = 
   let val {lhs,rhs} = dest_eq(concl th)
       val {Tyop="fun", Args = [ty,_]} = dest_type(type_of lhs)
   in Drule.AP_THM th o (Lib.C ptm_with_ty ty)
   end;

val ASM_CASES_TAC = Tactic.ASM_CASES_TAC o btm
fun AC_CONV p = Conv.AC_CONV p o ptm;

(* Could be smarter *)
val INST = Drule.INST o mk_term_rsubst;
val INST_TYPE = Thm.INST_TYPE o mk_type_rsubst;


(*---------------------------------------------------------------------------
 * A couple from jrh.
 *---------------------------------------------------------------------------*)
fun ABBREV_TAC q =
  let val {lhs,rhs} = Rsyntax.dest_eq (ptm q)
  in CHOOSE_THEN (fn th => SUBST_ALL_TAC th THEN ASSUME_TAC th)
       (Drule.EXISTS (mk_exists{Bvar=lhs,Body=mk_eq{lhs=rhs,rhs=lhs}},rhs)
                     (Thm.REFL rhs))                                       end;

fun UNABBREV_TAC [QUOTE s] = FIRST_ASSUM(SUBST1_TAC o SYM o
  assert(curry op = s o #Name o dest_var o rhs o concl)) THEN BETA_TAC;

end; (* Q *)
