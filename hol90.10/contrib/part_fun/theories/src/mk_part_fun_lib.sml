(* ===================================================================== *)
(* FILE          : mk_part_fun_lib.sml                                   *)
(* DESCRIPTION   : Library entry for the theory of lifts and             *)
(*                 partial functions.                                    *)
(*                                                                       *)
(* AUTHOR        : Elsa L. Gunter, AT&T Bell Laboratories                *)
(* DATE          : 93.09.21                                              *)
(*                                                                       *)
(* ===================================================================== *)

(* Copyright 1993 by AT&T Bell Laboratories *)


val part_fun_lib = 
    new_library{name = "part_fun",
		doc = "Partial functions, ala lift, by E. Gunter",
		path = (!Globals.HOLdir)^"contrib/part_fun/",
		parents = [],
		theories = ["lift","partial_functions","finite_functions"],
		code = [],
		help = [],
		loaded = "fn () => ()"};