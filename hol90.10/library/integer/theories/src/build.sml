(* FILE		: mk_elt_gp.sml						*)
(* DESCRIPTION  : load file for the group library.			*)
(*									*)
(* AUTHOR	: Elsa L. Gunter					*)
(* DATE		: 29 October 1992					*)
(*									*)
(*======================================================================*)

(* Copyright 1992 by AT&T Bell Laboratories *)
(* Share and Enjoy *)

val _ = Lib.clean_directory ((!Globals.HOLdir)^"library/integer/theories/"^
			     (SysParams.theory_file_type))

val _ = Theory.loadLibThry"group" "elt_gp";

val _ = Library.load_library{lib=Sys_lib.group_lib, theory = "-"};

local
    fun code file = (!HOLdir)^"library/integer/src/"^file
in
    val _ = compile (code "integer_tac.sig");
    val _ = compile (code "integer_tac.sml");
end;


local
    fun code file = (!HOLdir)^"library/integer/theories/src/"^file
in
  val _ = Lib.interpret (code "mk_integer.sml");
end;

