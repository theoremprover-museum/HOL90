(* ===================================================================== *)
(* FILE          : globals.sml                                           *)
(* DESCRIPTION   : Contains global flags for hol90.                      *)
(*                                                                       *)
(* AUTHOR        : (c) Konrad Slind, University of Calgary               *)
(* DATE          : August 26, 1991                                       *)
(* ===================================================================== *)


functor GLOBALS (structure Sys_params : Sys_params_sig) : Globals_sig =
struct

(* Version number for hol90 *)
val version_number = 7;

(* Bogus hack for defining negation. Hack is required because
   "~" is the only prefix; therefore, it is allowed to be a constant,
   but not allowed to be part of another constant. 
*)
local
val defined = ref false
in
fun neg_defined() = !defined
fun assert_neg_defined() = defined := true
end;

(* Bogus hack for defining numbers *)
local
val defined = ref false
in
fun nums_defined() = !defined
fun assert_nums_defined() = defined := true
end;

(* Bogus hack for defining strings *)
local
val defined = ref false
in
fun strings_defined() = !defined
fun assert_strings_defined() = defined := true
end;

(* Temporary hack *)
val in_type_spec = ref NONE:string option ref;

(* For controlling the display of exceptions *)
val print_exceptions = ref true;

(* For showing assumptions in theorems *)
val show_assums = ref false

(* Tells whether or not to bother finding and using a hol-init.sml file *)
val use_init_file = ref false;

(* sml/nj 0.93 val linewidth = System.Print.linewidth *)
(* sml/nj 1.02 val linewidth = Compiler.Control.Print.linewidth *)
val linewidth = System.Print.linewidth;

(* Whether the host compiler is running in interpreted mode, e.g., not 
 * optimizing the code *)
(* sml/nj 93 val interp = System.Control.interp; *)
(* sml/nj 102 val interp = Compiler.Control.interp; *)
val interp = System.Control.interp;

(* suffix to distinguish hol90s for different architectures. 
 *   Implode.tl.explode used to get rid of leading "."
 ***)
(* sml/nj 93 val arch = implode (tl (explode (!System.architecture))) *)
(* sml/nj 102 val arch = implode (tl (explode Compiler.architecture)); *)
val arch = implode (tl (explode (!System.architecture)));

val theory_file_type = 
    (case Sys_params.theory_file_option
       of Sys_params.make_binary => arch
	| _ => "ascii")

val remake_theory_files =
    (case Sys_params.theory_file_option
       of Sys_params.use_old_ascii => false
	| _ => true)

(* For pathnames to theories and libraries and help directories. *)
local val base = Sys_params.HOL_base_directory
in
val paths = { HOLdir = ref base,
              theory_path = ref [base^"theories/"^theory_file_type^"/"],
              library_path = ref [base^"library/desc/", base^"contrib/desc/"],
              help_path = ref [base^"help/90/", base^"help/88/ENTRIES/"]}
end;

val HOLdir = #HOLdir paths
and theory_path = #theory_path paths
and library_path = #library_path paths
and help_path = #help_path paths

(* Allow theorems with assumptions to be saved in a theory *)
val allow_theorems_with_assumptions = ref true;

(* controls depth of printing for terms. Since the pp recursively decrements 
   this value when traversing a term, and since printing stops when the
   value is 0, the negative value means "print everything". Warning: this
   will work to negmaxint, but no guarantees after that. But that's a pretty
   big term.
*)
val max_print_depth = ref ~1;

(* Assignable function for printing errors *)
val output_HOL_ERR = 
   ref (fn {message,origin_function,origin_structure} =>
         ( output(std_out, ("\nException raised at "^origin_structure^"."^
			    origin_function^":\n"^message^"\n"));
	  flush_out std_out));

(* Controls how online help is printed. *)
val output_help = ref "/bin/cat";

(* Gives some ability to tweak the lexis. It is initially being used 
   to make "~" more widely accessible in symbolic identifiers.
*)
val tilde_symbols = ref []:string list ref;

(* For prettyprinting *)
val type_pp_prefix = ref "(=="  and  type_pp_suffix = ref "==)"

val term_pp_prefix = ref "(--"  and  term_pp_suffix = ref "--)"

val pp_flags = {infix_at_front = ref false,
                show_dB = ref false,
                show_restrict = ref true, 
                show_types = ref false,
                stack_infixes = ref true};

(* For showing the deBruijn structure of a term *)
val show_dB = #show_dB pp_flags;

(* For showing the representation of a term having restricted quantifiers *)
val show_restrict = #show_restrict pp_flags;

(* For prettyprinting type information in a term.  *)
val show_types = #show_types pp_flags;

(* This is for documentation purposes *)
val reserved_identifiers = {symbolic = ["\\", ";", "=>", "|", ":" ],
                            alphanumeric = ["let", "in", "and", "of"]}

val goal_line = ref "____________________________";

end; (* Globals *)
