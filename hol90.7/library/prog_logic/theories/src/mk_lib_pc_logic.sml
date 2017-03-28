(* ==================================================================== *)
(* FILE		: mk_lib_pc_logic.sml					*)
(* DESCRIPTION  : load file for the program logics library.		*)
(*									*)
(* AUTHOR	: M. J. Morley 					        *)
(* DATE		: February 1993					        *)
(* ==================================================================== *)

val _ = Lib.clean_directory ((!Globals.HOLdir)^"library/prog_logic/theories/"^
			     (Globals.theory_file_type))

(* Set the path to write the theory to. *)

local
    val path = (!HOLdir)^"library/prog_logic/theories/"^
	       Globals.theory_file_type^"/"
in
    val _ =  theory_path := path::(!theory_path)
end

local
    val cur_dir = (!Globals.HOLdir)^"library/prog_logic/theories/src/"
in
    val _ = Lib.interpret (cur_dir ^ "mk_semantics.sml");
    val _ = Lib.interpret (cur_dir ^ "mk_hoare_thms.sml");
    val _ = Lib.interpret (cur_dir ^ "mk_hoare_logic_pc.sml");
end
