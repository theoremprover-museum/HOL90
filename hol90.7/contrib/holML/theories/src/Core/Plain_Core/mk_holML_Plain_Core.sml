(* File: contrib/holML/theories/src/Core/Plain_Core/mk_holML_Plain_Core.sml *)

local
    val path = (!HOLdir)^"contrib/holML/theories/"^
	       Globals.theory_file_type^"/"
in
    val _ = theory_path := path :: (!Globals.theory_path)
end;

val _ = new_theory "holML_Plain_Core";

fun local_use file =
    use ((!HOLdir)^"contrib/holML/theories/src/Core/Plain_Core/"^file)

(* Get the information about mutual recursion *)
val _ = load_library_in_place (find_library "nested_rec");

val _ = local_use "../../define_mut_rewrite.sml";

open ExtraGeneralFunctions;

val _ = load_library_in_place (find_library "part_fun");
val _ = add_theory_to_sml "lift";
val _ = add_theory_to_sml "partial_functions";

(* Pick up where we left off *)

val _ = new_parent "common_holML_core";
val _ = local_use "../../more_string/more_string.sml";
val _ = local_use "../../more_list/more_list.sml";
val _ = add_theory_to_sml "finmap";
val _ = local_use "../Common/common_holML_core_autoloads.sml"
val _ = add_theory_to_sml "common_holML_core";

val _ = local_use "../Common/MLgramFtns.sml";
val _ = local_use "../Common/MLsvalFtns.sml";
val _ = local_use "../Common/MLexconenvFtns.sml";
fun mk_set_ty ty = mk_type {Tyop = "set", Args = [ty]};

(* Get environment info *)

val _ = Lib.say "\nDefining the type of environments.\n";
val _ = local_use "MLenvInput.sml";
val _ = Lib.say "\nFinished defining the type of environments.\n";


(* define derived syntax functions for MLenv *)
val _ = Lib.say "\nSyntax functions for the abstract syntax.\n";
val _ = local_use "MLenvFtns.sml";


val _ = Lib.say "\nDefining functions for testing cases and selecting \
         \arguments from values.\n";
val _ = local_use "MLval_args.sml";
val _ = local_use "MLvalFtns.sml";


val _ = Lib.say "Defining the types of packs, values or packs, env. \
	 \or packs, etc.\n";
val _ = local_use "MLpack.sml";
val _ = local_use "MLpackFtns.sml";

val _ = Lib.say "\nDefining the types of memory and state.\n";
val _ = local_use "MLstateDef.sml";
val _ = local_use "MLstateFtns.sml";

val _ = Lib.say "\nDefining the initial Dymanic Basis.\n";
val _ = local_use "MLinitialDynamicBasis.sml";
val _ = local_use "MLinitialDynamicBasisFtns.sml";

val _ = Lib.say "\nDefining the apply function.\n";
val _ = local_use "MLapply.sml";


(* read in evaluation stuff *)

val _ = local_use "../../eval_rule_tac.sml";

val _ = Lib.say "\nDefining the ML exbind evaluation relation.\n";
val _ = local_use "MLexbind_eval.sml";

val _ = Lib.say "\nDefining the ML pattern evaluation relations.\n";
val _ = local_use "MLpat_eval.sml";

val _ = Lib.say "\nDefining the ML evaluation relations.\n";
val _ = local_use "MLeval.sml";

val _ = export_theory ();


