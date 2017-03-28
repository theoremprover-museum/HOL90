(* ===================================================================== *)
(* FILE          : term.sig                                              *)
(* DESCRIPTION   : Simply typed lambda terms.                            *)
(*                                                                       *)
(* AUTHOR        : (c) Konrad Slind, University of Calgary               *)
(* DATE          : August 26, 1991                                       *)
(* UPDATE        : October 94. Term signature implementation moved from  *)
(*                 symtab.sml, which is now gone.                        *)
(* ===================================================================== *)

signature Term_sig =
sig
  structure Type : Type_sig
  datatype fixity = Infix of int | Prefix | Binder
  datatype term = Fv of {Name : string, Ty : Type.hol_type}
                | Bv of int
                | Const of {Name : string, Ty : Type.hol_type}
                | Comb of {Rator : term, Rand : term}
                | Abs of {Bvar : term, Body : term}
                | ty_antiq of Type.hol_type
  
  datatype lambda = VAR of {Name : string, Ty : Type.hol_type}
                  | CONST of {Name : string, Ty : Type.hol_type}
                  | COMB of {Rator : term, Rand : term}
                  | LAMB of {Bvar : term, Body : term};

  type symtab
  val symtab_copy : unit -> symtab
  val replace_symtab : symtab -> unit
  exception TERM_SYMTAB_CLASH of {common_name:string, 
                                  theory1:string, theory2:string}

  val lookup_const: string -> term
  val const_decl : string -> {const : term, theory : string, place: fixity}
  datatype add_style = Defining | Loading;
  val add_term_const 
     : add_style -> {const :term, theory :string, place :fixity} -> unit

  val is_st_term_const : string -> bool
  val fixity_of_term : string -> fixity
  val prec_of_term : string -> int
  val is_binder : string -> bool
  val is_infix : string -> bool  
  val is_polymorphic : string -> bool

  val free_vars : term -> term list
  val free_in : term -> term -> bool
  val all_vars : term -> term list
  val free_varsl : term list -> term list
  val all_varsl : term list -> term list
  val term_lt :term -> term -> bool
  val genvar : Type.hol_type -> term
  val genvars : Type.hol_type -> int -> term list
  val variant : term list -> term -> term
  val type_of :term -> Type.hol_type
  val type_vars_in_term : term -> Type.hol_type list
  
  (* Constructors and destructors, except for mk_const *)
  val mk_var  :{Name : string, Ty : Type.hol_type} -> term
  val mk_primed_var  :{Name : string, Ty : Type.hol_type} -> term
  (* val prim_mk_const  :string -> term subst -> term *)
  val list_mk_comb: (term * term list) -> term
  val mk_comb :{Rator : term, Rand : term} -> term
  val mk_abs  :{Bvar : term, Body : term} -> term
  val dest_var  : term -> {Name : string, Ty : Type.hol_type}
  val dest_const: term -> {Name : string, Ty : Type.hol_type}
  val dest_comb : term -> {Rator : term, Rand : term}
  val dest_abs  : term -> {Bvar : term, Body : term}
  val is_var  : term -> bool
  val is_const: term -> bool
  val is_comb : term -> bool
  val is_abs  : term -> bool
  
  val dest_term : term -> lambda
  
  val rator : term -> term
  val rand  : term -> term
  val bvar  : term -> term
  val body  : term -> term
  val break_abs : term -> {Bvar : term, Body : term}
  val is_bvar : term -> bool
  
  (* Prelogic *)
  val aconv : term -> term -> bool
  val subst : term subst -> term -> term
  val inst : Type.hol_type subst -> term -> term
  val beta_conv : term -> term
end;


signature Public_term_sig =
sig
  structure Type : Public_type_sig
  datatype fixity = Infix of int | Prefix | Binder
  eqtype term 

  val const_decl : string -> {const : term, theory : string, place: fixity}
  val fixity_of_term : string -> fixity
  val prec_of_term : string -> int
  val is_binder : string -> bool
  val is_infix : string -> bool
  val is_polymorphic : string -> bool

  datatype lambda = VAR of {Name : string, Ty : Type.hol_type}
                  | CONST of {Name : string, Ty : Type.hol_type}
                  | COMB of {Rator : term, Rand : term}
                  | LAMB of {Bvar : term, Body : term};
  val ty_antiq : Type.hol_type -> term
  val free_vars : term -> term list
  val free_in : term -> term -> bool
  val all_vars : term -> term list
  val free_varsl : term list -> term list
  val all_varsl : term list -> term list
  val term_lt :term -> term -> bool
  val genvar : Type.hol_type -> term
  val genvars : Type.hol_type -> int -> term list
  val variant : term list -> term -> term
  val type_of :term -> Type.hol_type
  val type_vars_in_term : term -> Type.hol_type list
  
  (* Constructors and destructors, except for mk_const *)
  val mk_var  :{Name : string, Ty : Type.hol_type} -> term
  val mk_primed_var  :{Name : string, Ty : Type.hol_type} -> term
  val list_mk_comb: (term * term list) -> term
  val mk_comb :{Rator : term, Rand : term} -> term
  val mk_abs  :{Bvar : term, Body : term} -> term
  val dest_var  : term -> {Name : string, Ty : Type.hol_type}
  val dest_const: term -> {Name : string, Ty : Type.hol_type}
  val dest_comb : term -> {Rator : term, Rand : term}
  val dest_abs  : term -> {Bvar : term, Body : term}
  val is_var  : term -> bool
  val is_const: term -> bool
  val is_comb : term -> bool
  val is_abs  : term -> bool
  
  val dest_term : term -> lambda
  
  val rator : term -> term
  val rand  : term -> term
  val bvar  : term -> term
  val body  : term -> term
  
  (* Prelogic *)
  val aconv : term -> term -> bool
  val subst : term subst -> term -> term
  val inst : Type.hol_type subst -> term -> term
  val beta_conv : term -> term
end;
