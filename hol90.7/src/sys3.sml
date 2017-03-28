use "3/sys_lib.sig";
use "3/sys_lib.sml";


if Globals.remake_theory_files 
then ( load_theory "rec_type";
       Theory.new_theory "HOL";
       map Theory.new_parent ["one", "sum", "restr_binder"];
      ())
else Theory.load_theory "HOL";

(* Need "" at head of theory_path in order for absolute paths used in 
   library theories to make sense. Don't have to take it off again, unlike
   in sys2.sml.
*)
val _ = (Lib.cons_path "" Globals.theory_path;
         Library.load_library{lib = Sys_lib.hol_lib, theory = "-"});
