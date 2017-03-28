(* FILE		: mk_string_lib.sml					*)
(* DESCRIPTION  : load file for the string library.			*)
(*									*)
(* AUTHOR	: Elsa L. Gunter					*)
(* DATE		: 3 November 1992					*)
(*======================================================================*)

(* Copyright 1992 by AT&T Bell Laboratories *)

val _ = Lib.clean_directory ((!Globals.HOLdir)^"library/string/theories/"^
			     (Globals.theory_file_type))

(* Set the path to write the theory to. *)
local
    val path = (!HOLdir)^"library/string/theories/"^
	       Globals.theory_file_type^"/"
in
    val _ =  theory_path := path::(!theory_path)
end;

local
    val cur_dir = (!Globals.HOLdir)^"library/string/theories/src/"
in
    val _ = Lib.interpret (cur_dir ^ "mk_ascii.sml");
    val _ = Lib.interpret (cur_dir ^ "mk_string.sml");
end
