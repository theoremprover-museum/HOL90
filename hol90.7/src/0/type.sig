
signature Type_sig =
sig
  datatype hol_type = Stv of int     (* System generated type variables *)
                    | Utv of string  (* User-given type variables *)
                    | Tyc of string  (* Type constants  *)
                    | Link of hol_type ref (* Modifiable pointers *)
                    | Tyapp of {Tyop : string, Args : hol_type list}

  datatype 'a delta = NO_CHANGE | CHANGED of 'a
  val new_type_var :unit -> hol_type
  val reset_type_num :unit -> unit
  val unify :hol_type -> hol_type -> unit
  val ty_eq :hol_type * hol_type -> bool
  val shrink_type :hol_type -> hol_type delta
  val rename_tv :hol_type -> hol_type delta
  val ty_sub : hol_type subst -> hol_type -> hol_type delta
  val type_subst : hol_type subst -> hol_type -> hol_type
  val type_vars : hol_type -> hol_type list
  val type_varsl : hol_type list -> hol_type list
  val mk_type : {Tyop: string, Args:hol_type list} -> hol_type
  val dest_type : hol_type -> {Tyop : string, Args : hol_type list}
  val mk_vartype : string -> hol_type
  val dest_vartype : hol_type -> string
  val is_vartype : hol_type -> bool
  val polymorphic : hol_type -> bool
  val type_lt :hol_type -> hol_type -> bool

   
  val lookup_type : string -> {tyc:hol_type, arity :int, theory:string}
  val type_decl : string -> {tyc:hol_type, arity :int, theory:string}
  val add_type_const : {tyc:hol_type, arity :int, theory:string} -> unit
  val add_entry : {tyc:hol_type, arity :int, theory:string} -> unit
  type symtab
  val symtab_copy : unit -> symtab
  val replace_symtab : symtab -> unit
  exception TYPE_SYMTAB_CLASH of {common_name:string, 
                                  theory1:string, theory2:string}
  val is_st_type_const : string -> bool
  val arity_of_type : string -> int
end;


signature Public_type_sig =
sig
  eqtype hol_type
  val new_type_var :unit -> hol_type
  val reset_type_num :unit -> unit
  val type_subst : hol_type subst -> hol_type -> hol_type
  val type_vars : hol_type -> hol_type list
  val type_varsl : hol_type list -> hol_type list
  val mk_type : {Tyop: string, Args:hol_type list} -> hol_type
  val dest_type : hol_type -> {Tyop : string, Args : hol_type list}
  val mk_vartype : string -> hol_type
  val dest_vartype : hol_type -> string
  val is_vartype : hol_type -> bool
  val type_lt :hol_type -> hol_type -> bool
  val type_decl : string -> {tyc:hol_type, arity :int, theory:string}
end;
