(*---------------------------------------------------------------------------
 * This structure contains facts that HOL needs to know about its environment.
 *---------------------------------------------------------------------------*)

structure SysParams =
struct

datatype MLversion = Ninety | NinetySeven;

(*---------------------------------------------------------------------------
 * HOL_base_directory is only used in the preliminary stages of building
 * the system. Use Globals.HOLdir for general use.
 *---------------------------------------------------------------------------*)
val HOL_base_directory  = "/Nfs/bescot/grp11/hol/hol90.10/";
val arch                = "x86-linux";
val MLdialect = NinetySeven;

datatype thy_opt = make_binary | make_new_ascii | use_old_ascii;

val theory_file_option  = make_new_ascii
val theory_file_type    = "ascii";
val remake_theory_files = true;
val version_number      = "10"

(*---------------------------------------------------------------------------

          Stuff that comes from outside (in 9.alpha)

  datatype thy_opt = make_binary
                 | make_new_ascii
                 | use_old_ascii;

val theory_file_option =
   case getEnv "THEORY_TYPE"
   of SOME s => s
    | NONE => raise Fail "HOL_DIR variable not bound"

val HOL_base_directory =
   case getEnv "HOL_DIR"
   of SOME s => ref s
    | NONE => raise Fail "HOL_DIR variable not bound"

val theory_file_type =
    (case (!theory_file_option)
       of make_binary => Portable.arch
	| _ => "ascii")


val remake_theory_files =
    (case (!theory_file_option)
       of use_old_ascii => false
	| _ => true)


val version_number =
   case (Portable.getEnv "HOL90_VERSION")
   of NONE => "?"
    | SOME s => s;

 *---------------------------------------------------------------------------*)

end;
