(* File: contrib/holML/theories/src/Modules/HOFML/load.sml *)

local
    val path = (!HOLdir)^"contrib/holML/theories/"^
	       Globals.theory_file_type^"/"
in
    val _ = theory_path := path :: (!Globals.theory_path)
end;

val _ = new_theory "HOFML";

val _ = load_library_in_place (find_library "part_fun");
fun local_use file =
    use ((!HOLdir)^"contrib/holML/theories/src/Modules/HOFML/"^file)

val _ =  new_parent "common_ModML";

val _ = load_library_in_place (find_library "nested_rec")

val _ = load_library_in_place integer_lib

val _ = load_library_in_place (find_library "ind_def")

fun mk_set_ty ty = mk_type {Tyop = "set", Args = [ty]};

open Inductive_def;

open ExtraGeneralFunctions;

val _ = add_theory_to_sml "lift";
val _ = add_theory_to_sml "partial_functions";
val _ = local_use "../../more_list/more_list.sml";  
val _ = local_use "../../more_string/more_string.sml";
val _ = add_theory_to_sml "finmap"; 
val _ = local_use "../../Core/Common/common_holML_core_autoloads.sml";
val _ = add_theory_to_sml "common_holML_core";

val _ = local_use "../../Core/Plain_Core/holML_Plain_Core_autoloads.sml";
val _ = add_theory_to_sml "holML_Plain_Core";

val _ = add_theory_to_sml "common_ModML";

val _ = local_use "../../Core/Common/MLgramFtns.sml";
val _ = local_use "../../Core/Common/MLsvalFtns.sml";
val _ = local_use "../../Core/Common/MLexconenvFtns.sml";

val _ = local_use "../../Core/Plain_Core/MLenvFtns.sml";
val _ = local_use "../../Core/Plain_Core/MLvalFtns.sml";
val _ = local_use "../../Core/Plain_Core/MLpackFtns.sml";
val _ = local_use "../../Core/Plain_Core/MLstateFtns.sml";
val _ = local_use "../../Core/Plain_Core/MLinitialDynamicBasisFtns.sml";
val _ = local_use "../../Core/Plain_Core/MLinitial_bindings.sml";

val _ = local_use "../Common/grammarFtns.sml";

val _ = local_use "grammar.sml";

val _ = local_use "semantic_objects.sml";

val _ = local_use "semantic_object_functions.sml";

val _ = local_use "../../eval_rule_tac.sml";

val _ = local_use "eval.sml"; 

val _ = export_theory();

