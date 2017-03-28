signature Parse_support_sig =
sig
type preterm_in_env
type binder_in_env

structure Preterm : Public_preterm_sig

datatype arg = Rec_occ 
             | Hty of Preterm.Term.Type.hol_type
datatype parse = 
   PTM of Preterm.preterm
 | TY of Preterm.Term.Type.hol_type
 | TY_SPEC of {ty_name: string,
               clauses: {constructor:string, 
                         args:arg list} list}
val make_preterm : preterm_in_env -> parse
val make_aq : Preterm.Term.term -> preterm_in_env
val make_binding_occ : string -> binder_in_env
val make_aq_binding_occ : Preterm.Term.term -> binder_in_env
val make_atom: string -> preterm_in_env
val make_string: string -> preterm_in_env
val list_make_comb : preterm_in_env list -> preterm_in_env
val make_constrained : preterm_in_env -> 
                       Preterm.Term.Type.hol_type -> preterm_in_env
val bind_term : string -> binder_in_env list -> preterm_in_env -> 
                preterm_in_env
val bind_restr_term : string -> binder_in_env list
                      -> preterm_in_env -> preterm_in_env
                      -> preterm_in_env
val make_vstruct : binder_in_env list -> binder_in_env
val make_constrained_vstruct : binder_in_env -> Preterm.Term.Type.hol_type -> 
                               binder_in_env
val make_let : (binder_in_env list * preterm_in_env) list -> preterm_in_env ->
               preterm_in_env
val make_list : preterm_in_env list -> preterm_in_env
val make_set : preterm_in_env list -> preterm_in_env
val make_set_abs : preterm_in_env * preterm_in_env -> preterm_in_env
val make_atomic_type : string -> Preterm.Term.Type.hol_type
val make_type_app : (string * (Preterm.Term.Type.hol_type list)) -> 
                    Preterm.Term.Type.hol_type
val make_type_clause: {constructor:string, 
                       args:Preterm.Term.Type.hol_type list} 
                      -> {constructor:string, args : arg list}
val rec_occ : Preterm.Term.Type.hol_type
val prec_parse : preterm_in_env list -> preterm_in_env

val is_binder : string -> bool
val extract_type_antiq : Preterm.Term.term -> Preterm.Term.Type.hol_type
end;
