(* ==================================================================== *)
(* FILE		: mk_lib_tc_logic.sml					*)
(* DESCRIPTION  : load file for the program logics library.		*)
(*									*)
(* AUTHOR	: M. J. Morley 					        *)
(* DATE		: February 1993					        *)
(* ==================================================================== *)

(* Set the path to write the theory to. *)

local
    val path = (!HOLdir)^"library/prog_logic/theories/"^
	       Globals.theory_file_type^"/"
in
    val _ =  theory_path := path::(!theory_path)
    val _ =  load_theory "semantics"
end

local
    val cur_dir = (!Globals.HOLdir)^"library/prog_logic/theories/src/"
in
    val _ = Lib.interpret (cur_dir ^ "mk_halts.sml");
    val _ = Lib.interpret (cur_dir ^ "mk_halts_thms.sml");
    val _ = Lib.interpret (cur_dir ^ "mk_hoare_logic_tc.sml");
end
