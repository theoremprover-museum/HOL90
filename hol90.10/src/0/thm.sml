(* ===================================================================== *)
(* FILE          : thm.sml                                               *)
(* DESCRIPTION   : The abstract data type of theorems. Mostly            *)
(*                 translated from the hol88 source.                     *)
(*                                                                       *)
(* AUTHORS       : (c) Mike Gordon, University of Cambridge              *)
(*                     Konrad Slind, University of Calgary               *)
(* DATE          : September 10, 1991                                    *)
(* ADDITIONS     : Proof recording                                       *)
(*                 Wai Wong, Hong Kong Baptist University                *)
(* ===================================================================== *)


functor THM (structure Dsyntax : Dsyntax_sig
             structure Hol_pp : Hol_pp_sig
             structure Term : Term_sig
             sharing
               Dsyntax.Term = Hol_pp.Term = Term) : Thm_sig =
struct
structure Term = Term;
open Lib;

fun THM_ERR{function,message} = 
  Exception.HOL_ERR{origin_structure = "Thm",
            origin_function = function,
            message = message}

val inc = Portable.Ref.inc;

datatype thm = THM of Term.term list * Term.term

(*---------------------------------------------------------------------------
 * Support for recording proofs.
 *---------------------------------------------------------------------------*)
datatype just_arg = JA_THM of thm
                  | JA_TERM of Term.term
                  | JA_TYPE of Term.Type.hol_type
                  | JA_STRING of string
                  | JA_INT of int
                  | JA_INTLIST of int list
		  | JA_PAIR of (just_arg * just_arg);

datatype step = STEP of { Name:string, Just: just_arg list, Thm: thm } ;

fun dummy_rec_step (STEP{Name, Just, Thm}) = Thm;

val record_step = ref dummy_rec_step;
val record_proof_flag = ref false;
val suspended = ref false;

fun record_proof b = (record_proof_flag := b; ());
fun is_recording_proof () = (!record_proof_flag);

fun suspend_recording () = 
  if !record_proof_flag then 
    (record_proof_flag := false; suspended := true; ())
  else ();
fun resume_recording () = 
  if (!suspended andalso not(!record_proof_flag)) then 
    (record_proof_flag := true; suspended := false; ())
  else ();

fun note (s,th) = if !record_proof_flag then !record_step s else th;

(*---------------------------------------------------------------------------
 * Support for monitoring how many theorems are proved in a session. 
 *---------------------------------------------------------------------------*)
val counting = ref false;

datatype counter = Assume | Refl | Beta | Subst | Abs
                 | Disch  | Mp   | Inst
                 | Drule  | Definition | Axiom
                 | Disk   | Validity   | Other;

val count = {ASSUME     = ref 0,
             REFL       = ref 0,
             BETA_CONV  = ref 0,
             SUBST      = ref 0,
             ABS        = ref 0,
             DISCH      = ref 0,
             MP         = ref 0,
             INST_TYPE  = ref 0,
             DRULE      = ref 0,
             DEFINITION = ref 0,
             AXIOM      = ref 0,
             FROM_DISK  = ref 0,
             VALID_TAC  = ref 0,
             OTHER      = ref 0};

fun make_thm C seq = 
  ( if !counting 
    then (case C of
            Assume     => inc (#ASSUME count)
          | Refl       => inc (#REFL count)
          | Beta       => inc (#BETA_CONV count)
          | Subst      => inc (#SUBST count)
          | Abs        => inc (#ABS count)
          | Disch      => inc (#DISCH count)
          | Mp         => inc (#MP count)
          | Inst       => inc (#INST_TYPE count)
          | Drule      => inc (#DRULE count)
          | Definition => inc (#DEFINITION count)
          | Axiom      => inc (#AXIOM count)
          | Disk       => inc (#FROM_DISK count)
          | Validity   => inc (#VALID_TAC count)
          | Other      => inc (#OTHER count))
    else ()
    ;
    THM seq);

local fun zero (r as ref _) = (r := 0)
in
fun reset_thm_count() = 
   (zero (#ASSUME count);
    zero (#REFL count);
    zero (#BETA_CONV count);
    zero (#SUBST count);
    zero (#ABS count);
    zero (#DISCH count);
    zero (#MP count);
    zero (#INST_TYPE count);
    zero (#DRULE count);
    zero (#DEFINITION count);
    zero (#AXIOM count);
    zero (#FROM_DISK count);
    zero (#VALID_TAC count);
    zero (#OTHER count))
end;

fun thm_count() = 
   {ASSUME     = !(#ASSUME count),
    REFL       = !(#REFL count),
    BETA_CONV  = !(#BETA_CONV count),
    SUBST      = !(#SUBST count),
    ABS        = !(#ABS count),
    DISCH      = !(#DISCH count),
    MP         = !(#MP count),
    INST_TYPE  = !(#INST_TYPE count),
    drule      = !(#DRULE count),
    definition = !(#DEFINITION count),
    axiom      = !(#AXIOM count),
    from_disk  = !(#FROM_DISK count),
    valid_tac  = !(#VALID_TAC count),
    other      = !(#OTHER count)};

fun counting_thms b = (counting := b);


(*---------------------------------------------------------------------------
 * Making various kinds of theorems.
 *---------------------------------------------------------------------------*)

val mk_drule_thm      = make_thm Drule;
val mk_axiom_thm      = make_thm Axiom;
val mk_definition_thm = make_thm Definition;
val mk_disk_thm       = make_thm Disk;
val mk_tac_thm        = make_thm Validity;
val mk_thm            = make_thm Other;

fun hyp (THM(asl,_)) = asl
and concl(THM(_,c))  = c
and dest_thm(THM s)  = s


fun thm_free_vars (THM(asl,c)) = Term.free_varsl (c::asl);
val term_union = op_union Term.aconv
val term_U = op_U Term.aconv
fun hyp_union thm_list = itlist (union o hyp) thm_list [];


(*---------------------------------------------------------------------------
 *                THE PRIMITIVE RULES OF INFERENCE
 *---------------------------------------------------------------------------*)

local val bool = Term.Type.Tyc "bool"
      val mk_thm = make_thm Assume
      fun step tm th = STEP{Name="ASSUME", Just=[JA_TERM tm], Thm=th}
in
fun ASSUME tm =
   if (Term.type_of tm = bool)
   then let val th = mk_thm([tm],tm) 
        in note (step tm th, th)  end
   else raise(THM_ERR{function="ASSUME", message="not a proposition"})
  end;

  
local val mk_thm = make_thm Refl
      fun step tm th = STEP{Name="REFL", Just=[JA_TERM tm], Thm=th}
in
fun REFL tm = 
  let val th = mk_thm([], Dsyntax.mk_eq{lhs=tm, rhs=tm})
  in note (step tm th, th)
  end
end;


local val mk_thm = make_thm Beta
      fun step tm th = STEP{Name="BETACONV", Just=[JA_TERM tm], Thm=th}
in
fun BETA_CONV tm = 
  let val th = mk_thm ([],Dsyntax.mk_eq{lhs = tm, rhs = Term.beta_conv tm})
  in note (step tm th, th)
  end
  handle _ => raise THM_ERR{function="BETA_CONV", message="not a beta-redex"}
end;


(*---------------------------------------------------------------------------
 * ltheta is the substitution mapping from the template to the concl of
 * the given theorem. It checks that the template is an OK abstraction of
 * the given theorem. rtheta maps the template to another theorem, in which
 * the lhs in the first theorem have been replaced by the rhs in the second
 * theorem. The replacements provide the lhs and rhs. 
 *---------------------------------------------------------------------------*)
local val mk_thm = make_thm Subst
      fun spread{thm,var} = JA_PAIR(JA_THM thm, JA_TERM var)
      fun step tmplate (th,th') repls =
         STEP{Name = "SUBST",   Thm=th',
              Just = [JA_TERM tmplate, JA_THM th] @ map spread repls}
in
fun SUBST replacements template (th as THM(asl,c)) = 
     let val (ltheta, rtheta, hyps) =
         itlist (fn {var as Term.Fv _,thm = THM(h,c)} => 
                 fn (ltheta,rtheta,hyps) =>
                      let val {lhs,rhs} = Dsyntax.dest_eq c
                      in ({redex = var, residue = lhs}::ltheta,
                          {redex = var, residue = rhs}::rtheta,
                          union h hyps)
                      end)
                replacements ([],[],asl)
         handle Match => raise THM_ERR{function = "SUBST",
                                       message = "badly formed replacements"}
     in
     if (Term.aconv (Term.subst ltheta template) c)
     then let val th' = mk_thm (hyps,Term.subst rtheta template)
          in note (step template (th,th') replacements, th')  end
     else th
     end
end;


local val mk_thm = make_thm Abs
    fun step (v,th') th = STEP{Name="ABS",Just=[JA_TERM v, JA_THM th'], Thm=th}
in
fun ABS (v as Term.Fv _) (th as THM(asl,c)) = 
     let val {lhs,rhs} = Dsyntax.dest_eq c
     in if (mem v (Term.free_varsl asl))
        then raise THM_ERR{function = "ABS",
                           message = "variable is free in assumptions"}
        else let val th' = 
               mk_thm(asl,Dsyntax.mk_eq{lhs=Term.mk_abs{Bvar=v, Body=lhs},
                                        rhs=Term.mk_abs{Bvar=v, Body=rhs}})
             in note (step (v,th) th', th')
             end
     end
  | ABS _ _ = raise THM_ERR{function = "ABS",
                            message  = "first argument must be a variable"}
end;


local val mk_thm = make_thm Inst
      val type_vars_in_term_list = rev_itlist (union o Term.type_vars_in_term)
      fun spread{redex,residue} = JA_PAIR(JA_TYPE redex,JA_TYPE residue)
      fun step th th' theta = 
            STEP{Name="INSTTYPE", Just=JA_THM th::map spread theta, Thm=th'}
in
fun INST_TYPE [] th = th
  | INST_TYPE theta (th as THM(asl,c)) = 
     let val problem_tyvars = 
           intersect (Term.type_vars_in_term c) (type_vars_in_term_list asl [])
     in if (null_intersection problem_tyvars (map #redex theta))
        then let val th' = mk_thm(asl, Term.inst theta c)
             in note (step th th' theta,  th')        end
        else raise THM_ERR{function = "INST_TYPE",
                           message = "type variable(s) in assumptions would\
                                      \ be instantiated in concl"}
     end
end;


local val mk_thm = make_thm Disch
      fun step (w,th) th' = 
            STEP{Name="DISCH", Just=[JA_TERM w, JA_THM th], Thm=th'}
in
fun DISCH w (th as THM(asl,c)) = 
  let val th' = mk_thm (gather (not o Term.aconv w) asl,
                        Dsyntax.mk_imp{ant=w, conseq=c})
  in note (step (w,th) th', th')
  end
end;


local val mk_thm = make_thm Mp
      fun step (th1,th2) th =
            STEP{Name="MP", Just=[JA_THM th1, JA_THM th2], Thm=th}
in
fun MP (th1 as THM(asl1,c1)) (th2 as THM(asl2,c2)) =
   let val {ant,conseq} = Dsyntax.dest_imp c1
   in if (Term.aconv ant c2)
      then let val th = mk_thm(union asl1 asl2, conseq)
           in note (step (th1,th2) th, th)          end
      else raise THM_ERR{function = "MP",
                message="antecedent of first thm not aconv to concl of second"}
   end
end;


(*---------------------------------------------------------------------------
 * Prettyprinting of theorems.
 *---------------------------------------------------------------------------*)
fun pp_thm ppstrm (THM(asl,c)) =
   let val {add_string,add_break,begin_block,end_block,...} = 
              PP.with_ppstream ppstrm
       val pp_term = Hol_pp.pp_term ppstrm 
       fun commafy [] = ()
         | commafy [tm] = pp_term tm
         | commafy (t1::rst) = ( pp_term t1; 
                                 add_string ",";
                                 add_break(1,0);
                                 commafy rst)
       fun dotify alist = itlist (fn _ => fn dots => ("."^dots)) alist ""
   in
     begin_block PP.CONSISTENT 0;
     if (!Globals.max_print_depth = 0)
     then add_string " ... "
     else (case asl
             of [] => ()
              | _ => ( if (!Globals.show_assums) 
                       then ( begin_block PP.INCONSISTENT 1;
                              add_string "["; 
                              commafy asl; 
                              add_string "]";
                              end_block() )
                       else add_string (dotify asl);
                       add_break (1,0)) ;
           add_string "|- ";
           pp_term c);
     end_block()
   end;


fun thm_to_string thm = PP.pp_to_string (!Globals.linewidth) pp_thm thm
fun print_thm thm = Portable.output(Portable.std_out, thm_to_string thm);

end; (* THM *)