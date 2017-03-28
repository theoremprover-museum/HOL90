(* ===================================================================== *)
(* FILE          : install.sml                                           *)
(* DESCRIPTION   : signature for some system installation functions      *)
(*                                                                       *)
(* AUTHOR        : Elsa L. Gunter, AT&T Bell Laboratories                *)
(* DATE          : 20 November, 1992                                     *)
(* MODIFIED      : Jan 28, 1993, Konrad Slind                            *)
(*                 to add "install", which allows source directory to be *)
(*                 moved after building system.                          *)
(* ===================================================================== *)

(* Copyright 1992 by AT&T Bell Laboratories *)

signature Install_sig =
sig
  val install_system_theory : string -> unit
  val install : string -> unit
end
