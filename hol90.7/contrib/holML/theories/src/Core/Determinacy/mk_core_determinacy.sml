(* File: Core/Determinacy/mk_core_determinacy.sml *)

local
    val path = (!HOLdir)^"contrib/holML/theories/"^
	       Globals.theory_file_type^"/"
in
    val _ = theory_path := path :: (!Globals.theory_path)
end;

val _ = new_theory "core_determinacy";

fun local_use file =
    use ((!HOLdir)^"contrib/holML/theories/src/Core/Determinacy/"^file)

val _ = load_library_in_place utils_lib;
open ExtraGeneralFunctions;

val _ = load_library_in_place (find_library "part_fun");
val _ = add_theory_to_sml "lift";
val _ = add_theory_to_sml "partial_functions";

val _ = new_parent "holML_Plain_Core";

val _ = local_use "../../more_list/more_list.sml";
val _ = local_use "../../more_string/more_string.sml";
val _ = add_theory_to_sml "finmap";

val _ = local_use "../Common/common_holML_core_autoloads.sml"
val _ = add_theory_to_sml "common_holML_core";

val _ = local_use "../Plain_Core/holML_Plain_Core_autoloads.sml"
val _ = add_theory_to_sml "holML_Plain_Core";

val _ = local_use "match.sml";

val _ = local_use "exbind_det.sml";

val _ = local_use "pat_det.sml";

val _ = local_use "exp_det.sml";

val _ = export_theory();