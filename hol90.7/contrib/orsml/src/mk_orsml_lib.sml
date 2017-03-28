(* ===================================================================== *)
(* FILE          : mk_part_fun_lib.sml                                   *)
(* DESCRIPTION   : Library entry for the functional database query       *)
(*                 language, ORSML, and its interface to HOL90.          *)
(*                                                                       *)
(* AUTHOR        : Elsa L. Gunter, AT&T Bell Laboratories                *)
(* DATE          : 94.09.21                                              *)
(*                                                                       *)
(* ===================================================================== *)

(* Copyright 1994 by AT&T Bell Laboratories *)
(* Share and Enjoy *)

val _ = Lib.cd (!HOLdir^"contrib/desc");

val orsml_lib =
    new_library {name = "orsml",
		 doc = ("ORSML - a database query language for theories,\n"^
			"          by Leonid Libkin and E. Gunter"),
		 path = (!HOLdir)^"contrib/orsml/",
		 parents = [hol_lib],
		 theories = [],
		 code = ["hol_db_datatype.sml","common","type","dupelim",
			 "sr","dest","print","make","algebra","parser",
			 "build_orsml.sml", "set.lib","hol_queries.sml"],
		 help = [],
		 loaded = "fn () => ()"}; 

