(* FILE		: mk_elt_gp.sml						*)
(* DESCRIPTION  : load file for the group library.			*)
(*									*)
(* AUTHOR	: Elsa L. Gunter					*)
(* DATE		: 29 October 1992					*)
(*									*)
(*======================================================================*)

(* Copyright 1992 by AT&T Bell Laboratories *)
(* Share and Enjoy *)

val _ = Lib.clean_directory ((!Globals.HOLdir)^"library/group/theories/"^
			     (Globals.theory_file_type))

val _ = Library.load_library{lib=Sys_lib.utils_lib, theory = "-"};

open ExtraGeneralFunctions;

local
    fun code file = (!HOLdir)^"library/group/src/"^file
in
    val _ = compile (code "group_fun.sig");
    val _ = compile (code "group_fun.sml");
end;

(* Set the path to write the theory to. *)
local
    val path = (!HOLdir)^"library/group/theories/"^Globals.theory_file_type^"/"
in
    val _ = theory_path := path :: (!theory_path)
end;

val _ = Lib.interpret "mk_elt_gp.sml";
