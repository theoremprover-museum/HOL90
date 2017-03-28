(* ===================================================================== *)
(* FILE          : add_to_sml.sig                                        *)
(* DESCRIPTION   : Signature for routines that allow theory-level        *)
(*                 bindings to become SML bindings. Intended to serve    *)
(*                 as a replacement for auto-loading.                    *)
(*                                                                       *)
(* AUTHOR        : Konrad Slind, University of Calgary                   *)
(* DATE          : September 15, 1991                                    *)
(* ===================================================================== *)


signature Add_to_sml_sig =
sig
type thm
val L : (string * thm) list ref;
val parser : thm frag list -> thm
val add_to_sml : (string*thm) list -> unit
val add_axioms_to_sml : string -> unit
val add_definitions_to_sml : string -> unit
val add_theorems_to_sml : string -> unit
val add_theory_to_sml : string -> unit
val add_theory_structure_to_sml : {structure_name:string,
				   theory_name:string} -> unit
type autoload_info
val set_autoloads : autoload_info -> unit
end;
