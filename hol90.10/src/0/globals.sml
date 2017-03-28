(* ===================================================================== *)
(* FILE          : globals.sml                                           *)
(* DESCRIPTION   : Contains global flags for hol90.                      *)
(*                                                                       *)
(* AUTHOR        : (c) Konrad Slind, University of Calgary               *)
(* DATE          : August 26, 1991                                       *)
(* ===================================================================== *)


structure Globals : Globals_sig =
struct

open Portable;


(*------------------------------------------------------------------
 * Version number for hol90
 *----------------------------------------------------------------*)

val version_number = SysParams.version_number

(*---------------------------------------------------------------------------
 * Bogus hack for defining negation. Hack is required because "~" is the only
 * prefix; therefore, it is allowed to be a constant, but not allowed to be 
 * part of another constant. 
 *---------------------------------------------------------------------------*)

val neg_defined_ref = ref false
fun neg_defined() = !neg_defined_ref
fun assert_neg_defined() = neg_defined_ref := true

(*------------------------------------------------------------------
 * Bogus hack for defining numbers.
 *----------------------------------------------------------------*)

local val defined = ref false
in
fun nums_defined() = !defined
fun assert_nums_defined() = defined := true
end;

(*------------------------------------------------------------------
 * Bogus hack for defining strings
 *----------------------------------------------------------------*)

local
val defined = ref false
in
fun strings_defined() = !defined
fun assert_strings_defined() = defined := true
end;

(*------------------------------------------------------------------
 * "Temporary" hack.
 *----------------------------------------------------------------*)

val in_type_spec = ref NONE:string option ref;

(*------------------------------------------------------------------
 * For controlling the display of exceptions
 *----------------------------------------------------------------*)

val print_exceptions = ref true;

(*------------------------------------------------------------------
 * For showing assumptions in theorems
 *----------------------------------------------------------------*)

val show_assums = ref false

(*------------------------------------------------------------------
 * Tells whether or not to bother finding and using a hol-init.sml file
 *----------------------------------------------------------------*)

val use_init_file = ref false;

val linewidth = Portable.linewidth;

(*------------------------------------------------------------------
 * Whether the host compiler is running in interpreted mode, e.g., not 
 * optimizing the code 
 *----------------------------------------------------------------*)

val interp = Portable.interp;


(*------------------------------------------------------------------
 * For pathnames to theories and libraries and help directories.
 *----------------------------------------------------------------*)

local val base = ref SysParams.HOL_base_directory
in
val paths = { HOLdir = base,
            theory_path=ref [!base^"theories/"^SysParams.theory_file_type^"/"],
             library_path=ref [!base^"library/desc/", !base^"contrib/desc/"],
                help_path=ref [!base^"help/90/", !base^"help/88/ENTRIES/"]}
end

val HOLdir = #HOLdir paths
and theory_path = #theory_path paths
and library_path = #library_path paths
and help_path = #help_path paths

(*------------------------------------------------------------------
 * Allow theorems with assumptions to be saved in a theory 
 *----------------------------------------------------------------*)

val allow_theorems_with_assumptions = ref true;

(*---------------------------------------------------------------------------
 * Controls depth of printing for terms. Since the pp recursively decrements 
 * this value when traversing a term, and since printing stops when the
 * value is 0, the negative value means "print everything". Warning: 
 * this will work to negmaxint, but no guarantees after that. But that's 
 * a pretty big term.
 *----------------------------------------------------------------*)

val max_print_depth = ref ~1;

(*------------------------------------------------------------------
 * Assignable function for printing errors 
 *----------------------------------------------------------------*)

val output_HOL_ERR = 
   ref (fn {message,origin_function,origin_structure} =>
         ( output(std_out, ("\nException raised at "^origin_structure^"."^
			    origin_function^":\n"^message^"\n"));
	  Portable.flush_out std_out));

(*------------------------------------------------------------------
 * Controls how online help is printed. 
 *----------------------------------------------------------------*)

val output_help = ref "/bin/cat";

(*------------------------------------------------------------------
 * Gives some ability to tweak the lexis. It is initially being used 
 * to make "~" more widely accessible in symbolic identifiers.
 *----------------------------------------------------------------*)

val tilde_symbols = ref []:string list ref;

(*------------------------------------------------------------------
 * For prettyprinting 
 *----------------------------------------------------------------*)

(* Old values:
val type_pp_prefix = ref "(=="  and type_pp_suffix = ref "==)"
val term_pp_prefix = ref "(--"  and term_pp_suffix = ref "--)"
*)

val type_pp_prefix = ref "`"  and type_pp_suffix = ref "`"

val term_pp_prefix = ref "`"  and term_pp_suffix = ref "`"

val pp_flags = {show_dB        = ref false,
                show_restrict  = ref true, 
                show_types     = ref false,
                infix_at_front = ref false,
                stack_infixes  = ref true,
                in_at_end      = ref false};

(*------------------------------------------------------------------
 * For showing the deBruijn structure of a term 
 *----------------------------------------------------------------*)

val show_dB = #show_dB pp_flags;

(*------------------------------------------------------------------
 * For showing the representation of a term having restricted quantifiers
 *----------------------------------------------------------------*)

val show_restrict = #show_restrict pp_flags;

(*------------------------------------------------------------------
 * For prettyprinting type information in a term. 
 *----------------------------------------------------------------*)

val show_types = #show_types pp_flags;

(*------------------------------------------------------------------
 * For printing HOL infixes at beginning or end of lines.
 *----------------------------------------------------------------*)

val infix_at_front = #infix_at_front pp_flags;

(*------------------------------------------------------------------
 * Controls whether each argument of an infix goes on a new line.
 *----------------------------------------------------------------*)

val stack_infixes = #stack_infixes pp_flags;

(*------------------------------------------------------------------
 * Controls whether the "in" of a let expression is printed at the
 * end of the line.
 *----------------------------------------------------------------*)

val in_at_end = #in_at_end pp_flags;

(*------------------------------------------------------------------
 * This is mainly for documentation purposes
 *----------------------------------------------------------------*)

val reserved_identifiers = {symbolic = ["\\", ";", "=>", "|", ":" ],
                            alphanumeric = ["let", "in", "and", "of"]}


val goal_line = ref "____________________________";


(*------------------------------------------------------------------
 * At the end of type inference, HOL now guesses names for 
 * unconstrained type variables. If this flag is set, then the system
 * will print a message when such guesses are made.
 *----------------------------------------------------------------*)
val notify_on_tyvar_guess = ref true;

end; (* Globals *)

