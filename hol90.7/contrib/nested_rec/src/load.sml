(*
val _ = use ((!Globals.HOLdir)^"contrib/desc/mk_mutrec_desc.sml");
*)

val _ = load_library_in_place (find_library "mutrec");

val _ = Lib.compile "gen_funs.sig";
val _ = Lib.compile "gen_funs.sml";
val _ = Lib.compile "exists_funs.sml";
val _ = Lib.compile "table.sig";
val _ = Lib.compile "table.sml";
val _ = Lib.compile "entries.sml";
val _ = Lib.compile "def_type.sig";
val _ = Lib.compile "make_type_op.sml";
val _ = Lib.compile "def_type.sml";
val _ = Lib.compile "nested_rec_def.sml";


