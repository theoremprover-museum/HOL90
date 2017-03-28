(*===========================================================================*)
(*                                                                           *)
(*   FILE:         mk_more_arithmetic.sml                                    *)
(*   EDITOR:       Paul Curzon                                               *)
(*   DATE:         April 1993                                                *)
(*   DESCRIPTION:  more_arithmetic top_level theory                          *)
(*                                                                           *)
(*===========================================================================*)

(*
val path = 
   (!Globals.HOLdir)^"library/more_arithmetic/theories/"^Globals.theory_file_type^"/"
*)

val path = 
   "../"^Globals.theory_file_type^"/"

val _ = theory_path := path::(!theory_path);


local
fun delete_theory name = 
    System.system("/bin/rm -f "^name^".thms "^name^".holsig")
in
  val _ = delete_theory (path^"more_arithmetic")
end;


new_theory "more_arithmetic";

new_parent"ineq";
new_parent"pre";
new_parent"sub";
new_parent"mult";
new_parent"min_max";
new_parent"odd_even";
new_parent"div_mod";

local
fun use_lib_code s =
(*   let val p = (!Globals.HOLdir)^"library/more_arithmetic/src/" *)
   let val p = "../../src/" 
   in  compile (p^s^".sig"); 
       compile (p^s^".sml")
   end;
in
  val _ =  use_lib_code "gen_ind"
end;



export_theory();



