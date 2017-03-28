(* File: contrib/holML/theories/src/Core/Common/mk_common_holML_core.sml *)

local
    val path = (!HOLdir)^"contrib/holML/theories/"^
	       Globals.theory_file_type^"/"
in
    val _ = theory_path := path :: (!Globals.theory_path)
end;

val _ = new_theory "common_holML_core";

val _ = new_parent "integer";

val _ = new_parent "more_string";

val _ = new_parent "more_list";
val _ = use ((!HOLdir)^"contrib/holML/theories/src/more_list/more_list.sml");

val _ = new_parent "set"
fun mk_set_ty ty = mk_type {Tyop = "set", Args = [ty]};

val _ = load_library_in_place (find_library "part_fun");
val _ = add_theory_to_sml "lift";
val _ = add_theory_to_sml "partial_functions";

val _ = new_parent "finmap";
val _ = add_theory_to_sml "finmap";

(* Get the information about mutual nested recursion *)
val _ = load_library_in_place (find_library "nested_rec");

open ExtraGeneralFunctions;

fun local_use file =
    use ((!HOLdir)^"contrib/holML/theories/src/Core/Common/"^file)

(* Get grammar info *)

val _ = local_use "MLgramInput.sml";

(* define syntax functions for MLgram *)
val _ = Lib.say "\nSyntax functions for the abstract syntax.\n";
val _ = local_use "MLgramFtns.sml";

(*
val _ = local_use "MLgramThms.sml";
*)

(* Get preliminary environment info *)

val _ = Lib.say "\nPrelinimaries for environments.\n";
val _ = local_use "MLsval.sml";

val _ = local_use "MLsvalFtns.sml";

val _ = local_use "MLexconenv.sml";

val _ = export_theory ();

