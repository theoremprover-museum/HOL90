(* ===================================================================== *)
(* FILE          : install.sml                                           *)
(* DESCRIPTION   : Defines the function install_system_theory for use    *)
(*                 when rebuilding the system to either rebuild new      *)
(*                 theory files, or load existing as determined by       *)
(*                 SysParams.remake_theory_files.                        *)
(*                                                                       *)
(*                 Also defines "install", for updating system paths     *)
(*                 when the root directory of the hol90 sources is       *)
(*                 moved.                                                *)
(*                                                                       *)
(* AUTHOR        : Elsa L. Gunter, AT&T Bell Laboratories                *)
(* DATE          : 20 November, 1992                                     *)
(* AUGMENTED     : Jan28 1993, to have "install", which allows one to    *)
(*                 move the hol90 directory structure after it has been  *)
(*                 built. (Konrad Slind)                                 *)
(* ===================================================================== *)

(* Copyright 1992 by AT&T Bell Laboratories *)

structure Install : Install_sig =
struct

open CoreHol;

fun install_system_theory thy_name =
    if SysParams.remake_theory_files
    then Portable.use ((!Globals.HOLdir)^"theories/src/mk_"^thy_name^".sml")
    else (Theory.load_theory thy_name;
	  Add_to_sml.add_theory_to_sml thy_name)



(*---------------------------------------------------------------------------
 * Informs the system of its new location, if one moves the hol90 sources
 *   after the system has been built.
 *---------------------------------------------------------------------------*)
local
fun last_char str = Portable.String.substring(str, size str - 1, 1)
fun pathify str = if (last_char str = "/") then str else str^"/"
fun op_mem eq_func i =
   let val eqi = eq_func i
       fun mem [] = false
         | mem (a::b) = eqi a orelse mem b
   in mem
   end
fun op_set_diff eq_func a b = 
   let val mem = Lib.C (op_mem eq_func) b
   in Lib.gather (not o mem) a
   end
in
fun install base =
   let val base = pathify base
       val help_base = base^"help/"
       val lib_base = base^"library/"
       val contrib_base = base^"contrib/"
       val theory_suffix = "theories/"^SysParams.theory_file_type^"/"
       (* all known but unloaded libraries *)
       val unloaded_libs = op_set_diff Library.lib_eq 
                                       (Library.known_libraries())
                                       (Library.loaded_libraries())
       (* the unloaded libs that supply theories *)
       val theory_suppliers = 
	   Lib.itlist (fn lib => fn A => 
                       let val {name,theories,...} = Library.dest_library lib
                       in if (Portable.List.null theories)
                          then A
                          else name::A
                       end)
                    unloaded_libs []
   in
     Globals.HOLdir := base;
     Globals.help_path := ["", help_base^"90/", help_base^"88/ENTRIES/"];
     Globals.library_path := ["", lib_base^"desc/", contrib_base^"desc/"];
     (* move the system theories and also the theories of any unloaded but
        known libraries *)
     Globals.theory_path := (["", base^theory_suffix]@
                             (map (fn s => lib_base^s^"/"^theory_suffix)
                                  theory_suppliers));
     (* move the unloaded but known libraries *)
     map (fn lib => Library.move_library
                    (lib, lib_base^(#name(Library.dest_library lib))^"/"))
         unloaded_libs;
     Lib.say ("hol90 root directory now regarded as "^Lib.quote base^".\n")
   end
end;

end;  (* Install *)
