(* ===================================================================== *)
(* FILE		: mk_word.ml						 *)
(* DESCRIPTION   : Create the theory word as the descendent theory of	 *)
(*   	    	  all the word_xxx theories.				 *)
(* WRITES FILE   : word.th  	    					 *)
(*									 *)
(* AUTHOR	: (c) Wai Wong						 *)
(* DATE		: 24 September 1992					 *)
(* TRANSLATOR: Paul Curzon  3 June 1993, September 1994			 *)
(* ===================================================================== *)

val path = 
   "../"^SysParams.theory_file_type^"/"

val _ = theory_path := path::(!theory_path);


local
fun delete_theory name = 
    Portable.system("/bin/rm -f "^name^".thms "^name^".holsig")
in
  val _ = delete_theory (path^"word")
end;

load_theory "bword_arith";

new_theory"word";

new_parent "bword_bitop";

export_theory();
