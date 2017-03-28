(* FILE		: mk_lib.sml                                            *)
(* DESCRIPTION  : Build the theory used in the res_quan library.        *)
(*									*)
(* AUTHOR	: Elsa L. Gunter					*)
(* DATE		: 28 May 1993						*)
(* BASED ON FILE BY	: Elsa L. Gunter				*)
(*======================================================================*)

(* Copyright 1992 by AT&T Bell Laboratories *)

val _ = Lib.clean_directory ((!Globals.HOLdir)^"library/res_quan/theories/"^
			     SysParams.theory_file_type)

(* Set the path to write the theory to. *)
local
    val path = (!HOLdir)^"library/res_quan/theories/"^
	       SysParams.theory_file_type^"/"
in
    val _ =  theory_path := path::(!theory_path)
end;

local
    val cur_dir = (!Globals.HOLdir)^"library/res_quan/theories/src/"
in
    val _ = Lib.interpret (cur_dir ^ "mk_res_quan.sml");
end
