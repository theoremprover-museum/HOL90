(* File: contrib/holML/theories/src/Modules/Common/mk_common_ModML.sml *)

local
    val path = (!HOLdir)^"contrib/holML/theories/"^
	       Globals.theory_file_type^"/"
in
    val _ = theory_path := path :: (!Globals.theory_path)
end;

val _ = new_theory "common_ModML";

fun local_use file =
    use ((!HOLdir)^"contrib/holML/theories/src/Modules/Common/"^file)

val _ = load_library_in_place (find_library "part_fun");
val _ = new_parent "holML_Plain_Core";
val _ = add_theory_to_sml "more_list";

val _ = load_library_in_place (find_library "ind_def");

open Inductive_def;

val _ = load_library_in_place (find_library "nested_rec");

val _ = local_use "grammar.sml";

val _ = local_use "eval.sml";

val _ = export_theory();
