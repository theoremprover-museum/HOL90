(* ===================================================================== *)
(* FILE          : mk_holML_lib.sml                                      *)
(* DESCRIPTION   : Library entry for the theories defining the dynamic   *)
(*                 semantics of Standard ML.                             *)
(*                                                                       *)
(* AUTHOR        : Elsa L. Gunter, AT&T Bell Laboratories                *)
(* DATE          : 94.11.3                                               *)
(*                                                                       *)
(* ===================================================================== *)

(* Copyright 1994 by AT&T Bell Laboratories *)

val holML_lib =
    new_library{name = "holML",
		doc = "Dynamic semantics of Standard ML, \n"^
		      "  by Myra VanInwegen, Savitri Maharaj, and E. Gunter",
		path = (!Globals.HOLdir)^"contrib/holML/",
		parents = [find_library "part_fun"],
		theories = ["common_holML_core","holML_Plain_Core",
			    "core_determinacy","common_ModML",
			    "ModML","HOFML"],
		code = ["common_holML_core_autoloads.sml",
			"holML_Plain_Core_autoloads.sml",
			"MLgramFtns.sml",
			"MLsvalFtns.sml",
			"MLexconenvFtns.sml",
			"MLenvFtns.sml",
			"MLvalFtns.sml",
			"MLpackFtns.sml",
			"MLstateFtns.sml",
			"MLinitialDynamicBasisFtns.sml",
			"grammarFtns.sml"],
		help = [],
		loaded = "fn () => ()"};
