(* File: more_list.sml *)

val _ = add_theory_to_sml "list"
val _ = add_theory_to_sml "more_list"

fun mk_list_ty ty = mk_type {Tyop = "list", Args = [ty]};
fun mk_nonemptylist_ty ty = mk_type {Tyop = "nonemptylist", Args = [ty]};
