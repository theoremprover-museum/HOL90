signature RW_sig = 
sig
 type term
 type thm
 type tactic
 type conv

  (* Simplification sets *)
  type simpls
  val empty_simpls : simpls
  val dest_simpls  : simpls -> {congs:thm list, rws:thm list}
  val mk_simpls    : (thm -> thm) -> thm -> thm list
  val MK_RULES     : thm -> thm list
  val add_rws      : simpls -> thm list -> simpls
  val add_congs    : simpls -> thm list -> simpls
  val join_simpls  : simpls -> simpls -> simpls
  val std_simpls   : simpls
  val pp_simpls    : PP.ppstream -> simpls -> unit
  val embedded_ref : (term -> term -> bool) ref

  (* The implicit simplification set *)
  structure Implicit :
  sig
    val add_congs  : thm list -> unit
    val add_rws    : thm list -> unit
    val add_simpls : simpls -> unit
    val implicit_simpls : unit -> simpls
    val set_simpls : simpls -> unit
  end

  (* Solvers and tracing *)
  val solver_err : unit -> 'a
  val tracing : bool ref
  val rw_solver : simpls -> thm list -> term -> thm
  val std_solver : 'a -> thm list -> term -> thm
  val always_fails : 'a -> 'b -> 'c -> 'd

  (* Tells whether to add context to the simpls as term is traversed *)
  datatype context_policy = ADD | DONT_ADD

  (* The atomic conditional term rewriter. *)
  val RW_STEP:{context:'a * context_policy, simpls:simpls,
               prover:simpls -> 'a -> term -> thm}
               -> term -> thm

  type strategy
  val DEPTH : strategy
  val REDEPTH : strategy
  val TOP_DEPTH : strategy
  val ONCE_DEPTH : strategy
  val RATOR : strategy
  val RAND  : strategy
  val ABST  : strategy

  datatype repetitions = Once | Fully | Special of strategy
  datatype rules   = Default of thm list 
                   | Pure of thm list 
                   | Simpls of simpls * thm list
  datatype context = Context of thm list * context_policy
  datatype congs   = Congs of thm list
  datatype solver  = Solver of simpls -> thm list -> term -> thm

  (* Parameterized rewriters for terms, theorems, and goals *)
  val Rewrite      :repetitions -> rules*context*congs*solver -> conv
  val REWRITE_RULE :repetitions -> rules*context*congs*solver -> thm -> thm
  val ASM_REWRITE_RULE:repetitions -> rules*context*congs*solver -> thm -> thm
  val REWRITE_TAC     :repetitions -> rules*context*congs*solver -> tactic
  val ASM_REWRITE_TAC :repetitions -> rules*context*congs*solver -> tactic


  (* Specialized rewriters for different types *)
  (* Terms *)
  val CRW_CONV          : thm list -> term -> thm
  val RW_CONV           : thm list -> term -> thm
  val PURE_RW_CONV      : thm list -> term -> thm
  val ONCE_RW_CONV      : thm list -> term -> thm
  val PURE_ONCE_RW_CONV : thm list -> term -> thm


  (* Theorems *)
  val CRW_RULE          : thm list -> thm -> thm
  val RW_RULE           : thm list -> thm -> thm
  val PURE_RW_RULE      : thm list -> thm -> thm
  val ONCE_RW_RULE      : thm list -> thm -> thm
  val PURE_ONCE_RW_RULE : thm list -> thm -> thm

  val ASM_CRW_RULE      : thm list -> thm -> thm
  val ASM_RW_RULE       : thm list -> thm -> thm
  val PURE_ASM_RW_RULE  : thm list -> thm -> thm
  val ONCE_ASM_RW_RULE  : thm list -> thm -> thm
  val PURE_ONCE_ASM_RW_RULE : thm list -> thm -> thm


  (* Goals *)
  val RW_TAC          : thm list -> tactic
  val CRW_TAC         : thm list -> tactic
  val PURE_RW_TAC     : thm list -> tactic
  val ONCE_RW_TAC     : thm list -> tactic
  val PURE_ONCE_RW_TAC: thm list -> tactic

  val ASM_RW_TAC      : thm list -> tactic
  val ASM_CRW_TAC     : thm list -> tactic
  val PURE_ASM_RW_TAC : thm list -> tactic
  val ONCE_ASM_RW_TAC : thm list -> tactic
  val PURE_ONCE_ASM_RW_TAC : thm list -> tactic
end;
