(* ===================================================================== *)
(* FILE          : thm.sml                                               *)
(* DESCRIPTION   : The abstract data type of theorems. Mostly            *)
(*                 translated from the hol88 source.                     *)
(*                                                                       *)
(* AUTHORS       : (c) Mike Gordon, University of Cambridge              *)
(*                     Konrad Slind, University of Calgary               *)
(* DATE          : September 10, 1991                                    *)
(* ===================================================================== *)


functor THM (structure Dsyntax : Dsyntax_sig
             structure Hol_pp : Hol_pp_sig
             structure Globals : Globals_sig
             structure Term : Term_sig
             sharing
               Dsyntax.Term = Hol_pp.Term = Term) : Thm_sig =
struct
structure Term = Term;

fun THM_ERR{function,message} = 
    HOL_ERR{origin_structure = "Thm",
            origin_function = function,
            message = message}

datatype thm = THM of Term.term list * Term.term


(* For telling how many theorems are proved in a session. *)
val counting = ref false;

datatype counter = Assume | Refl | Beta | Subst | Abs
                 | Disch  | Mp   | Inst
                 | Drule  | Definition | Axiom
                 | Disk | Validity | Other;

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
  ( if not(!counting) 
    then ()
    else (case C of
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
    ;
    THM seq);

local
fun zero (r as ref _) = (r := 0)
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
   {ASSUME = !(#ASSUME count),
    REFL = !(#REFL count),
    BETA_CONV = !(#BETA_CONV count),
    SUBST = !(#SUBST count),
    ABS = !(#ABS count),
    DISCH = !(#DISCH count),
    MP = !(#MP count),
    INST_TYPE = !(#INST_TYPE count),
    drule = !(#DRULE count),
    definition = !(#DEFINITION count),
    axiom = !(#AXIOM count),
    from_disk = !(#FROM_DISK count),
    valid_tac = !(#VALID_TAC count),
    other = !(#OTHER count)};

fun counting_thms b = (counting := b);


(* Ought to check that all terms in A and c have type :bool *)
val mk_drule_thm = make_thm Drule;
val mk_axiom_thm = make_thm Axiom;
val mk_definition_thm = make_thm Definition;
val mk_disk_thm = make_thm Disk;
val mk_tac_thm = make_thm Validity;
val mk_thm = make_thm Other;

fun hyp (THM(asl,_)) = asl
and concl(THM(_,c)) = c
and dest_thm(THM s) = s


fun thm_free_vars (THM(asl,c)) = Term.free_varsl (c::asl);
val term_union = op_union Term.aconv
val term_U = op_U Term.aconv
fun hyp_union thm_list = itlist (union o hyp) thm_list [];


(* THE PRIMITIVE RULES OF INFERENCE *)

local
val bool = Term.Type.Tyc "bool"
in
fun ASSUME tm =
   if (Term.type_of tm = bool)
   then make_thm Assume ([tm],tm) 
   else raise(THM_ERR{function = "ASSUME", message = "not a proposition"})
end;
  
fun REFL tm = make_thm Refl ([], Dsyntax.mk_eq{lhs = tm, rhs = tm});


fun BETA_CONV tm = 
   make_thm Beta
    ([],Dsyntax.mk_eq{lhs = tm, rhs = Term.beta_conv tm})
                handle _ => raise THM_ERR{function = "BETA_CONV",
				          message = "not a beta-redex"};


(* ltheta is the substitution mapping from the template to the concl of
   the given theorem. It checks that the template is an OK abstraction of
   the given theorem. rtheta maps the template to another theorem, in which
   the lhs in the first theorem have been replaced by the rhs in the second
   theorem. The replacements provide the lhs and rhs. 
*)
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
     then make_thm Subst (hyps,Term.subst rtheta template)
     else th
     end;

fun ABS (v as Term.Fv _) (THM(asl,c)) = 
     let val {lhs,rhs} = Dsyntax.dest_eq c
     in if (mem v (Term.free_varsl asl))
        then raise THM_ERR{function = "ABS",
                           message = "variable is free in assumptions"}
        else make_thm Abs
                (asl,Dsyntax.mk_eq{lhs=Term.mk_abs{Bvar=v, Body=lhs},
                                   rhs=Term.mk_abs{Bvar=v, Body=rhs}})
     end
  | ABS _ _ = raise(THM_ERR{function = "ABS",
			    message = "first argument must be a variable"});


local
val type_vars_in_term_list = rev_itlist (union o Term.type_vars_in_term)
in
fun INST_TYPE [] th = th
  | INST_TYPE theta (THM(asl,c)) = 
       let val problem_tyvars = intersect (Term.type_vars_in_term c)
                                          (type_vars_in_term_list asl [])
       in if (null_intersection problem_tyvars (map #redex theta))
          then make_thm Inst (asl, Term.inst theta c)
          else raise THM_ERR{function = "INST_TYPE",
                             message = "type variable(s) in assumptions would\
                                       \ be instantiated in concl"}
       end
end;


fun DISCH w (THM(asl,c)) = 
   make_thm Disch (gather (not o Term.aconv w) asl,
                     Dsyntax.mk_imp{ant = w, conseq = c});

fun MP (THM(asl1,c1)) (THM(asl2,c2)) =
   let val {ant,conseq} = Dsyntax.dest_imp c1
   in if (Term.aconv ant c2)
      then make_thm Mp (union asl1 asl2, conseq)
      else raise THM_ERR{function = "MP",
                message="antecedent of first thm not aconv to concl of second"}
   end;

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
fun print_thm thm = output(std_out, thm_to_string thm);

end; (* THM *)
