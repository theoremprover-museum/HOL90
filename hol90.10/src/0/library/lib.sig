(* ===================================================================== *)
(* FILE          : lib.sig                                               *)
(* DESCRIPTION   : Provides functionality for HOL libraries.             *)
(*                                                                       *)
(* AUTHOR        : Konrad Slind, University of Calgary                   *)
(* DATE          : December 9, 1991                                      *)
(*                                                                       *)
(* Modified      : December 25, 1992  (kls)                              *)
(*                 Changed to have a library be represented by a data    *)
(*                 structure in memory rather than as a file on disk.    *)
(* ===================================================================== *)


signature Library_sig = 
sig
 type lib
 val loaded_cell : (unit -> unit) ref
 val lib_eq : lib -> lib -> bool
 val new_library : {name : string,
                    doc : string,
                    path : string,
                    parents : lib list,
                    theories : string list,
                    code : string list,
                    help : string list,
                    loaded : string} -> lib
 val dest_library : lib -> {name : string,
                            doc : string,
                            path : string,
                            parents : lib list,
                            theories : string list,
                            code : string list,
                            help : string list}
 val prim_load_library' : (string list -> unit) -> {lib:lib, theory:string} -> unit
 val prim_load_library : (string -> unit) -> {lib:lib, theory:string} -> unit
 val load_library : {lib:lib, theory:string} -> unit
 val load_library_in_place :lib -> unit
 val find_library : string -> lib
 val get_library_from_disk : string -> lib
 val move_library : lib * string  -> unit
 val delete_library : lib -> unit

 val known_libraries : unit -> lib list
 val loaded_libraries : unit -> lib list
 val pp_library : PP.ppstream -> lib -> unit
 val lib_help : {lib:lib,topic:string} -> unit
end;
