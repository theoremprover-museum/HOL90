(* ===================================================================== *)
(* FILE          : globals.sig                                           *)
(* DESCRIPTION   : Signature for global flags of hol90.                  *)
(*                                                                       *)
(* AUTHOR        : (c) Konrad Slind, University of Calgary               *)
(* DATE          : August 26, 1991                                       *)
(* ===================================================================== *)


signature Globals_sig =
sig

  val version_number : int

  val neg_defined : unit -> bool
  val nums_defined :  unit -> bool
  val strings_defined :  unit -> bool
  val assert_neg_defined : unit -> unit
  val assert_nums_defined : unit -> unit
  val assert_strings_defined : unit -> unit

  val in_type_spec: string option ref

  val print_exceptions : bool ref
  val show_assums : bool ref
  val allow_theorems_with_assumptions : bool ref
  val use_init_file : bool ref
  val max_print_depth : int ref

  val type_pp_prefix : string ref
  val type_pp_suffix : string ref
  val term_pp_prefix : string ref
  val term_pp_suffix : string ref
  val linewidth : int ref
  val interp : bool ref
  val arch : string
  val theory_file_type : string
  val remake_theory_files : bool

  val paths : {HOLdir : string ref,
               theory_path : string list ref,
               library_path : string list ref,
               help_path : string list ref}

  val HOLdir : string ref
  val theory_path : string list ref
  val library_path : string list ref
  val help_path : string list ref

  val output_HOL_ERR : ({origin_structure : string,
                         origin_function : string,
  		         message : string} -> unit) ref
  val output_help : string ref
  val tilde_symbols : string list ref
  val pp_flags : {infix_at_front:bool ref,
                  show_dB: bool ref,
                  show_restrict:bool ref,
                  show_types: bool ref,
                  stack_infixes :bool ref}
  val show_restrict : bool ref
  val show_types : bool ref
  val show_dB : bool ref
  val reserved_identifiers : {symbolic : string list, 
                              alphanumeric : string list}
  val goal_line : string ref
end
