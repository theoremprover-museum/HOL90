val basic_hol_lib =
   if Globals.remake_theory_files
   then Library.new_library
        {name = "BASIC_HOL",
         doc = "Supplies numbers and pairs. Preloaded.",
         path = !Globals.HOLdir,
         parents = [prim_hol_lib],
         theories = ["BASIC_HOL"],
         code = ["2/num_conv.sig","2/num_conv.sml",
                 "2/let_conv.sig","2/let_conv.sml",
                 "2/num_induct.sig","2/num_induct.sml",
                 "2/rec_type_support.sig","2/rec_type_support.sml"],
         help = [],
         loaded = "fn() => \
           \ let val pair_rewrites = map (theorem \"pair\") \
           \                             [\"PAIR\",\"FST\",\"SND\"] \
           \ in \
           \    Globals.theory_path := tl (!Globals.theory_path); \
           \    if Globals.remake_theory_files \
           \    then (close_theory(); export_theory()) \
           \    else (); \
           \    Globals.assert_nums_defined(); \
           \    Rewrite.add_base_rewrites pair_rewrites;\
           \    Lib.use_string\"open Num_conv Let_conv\"; \
           \    Lib.use_string\"open Num_induct Rec_type_support\"; \
           \    System.Control.interp := true; \
           \    Save_hol.save_hol\"hol90.2\" \
           \ end"}
   else let val bh_lib = Library.find_library "BASIC_HOL";
        in Library.move_library(bh_lib, !Globals.HOLdir);
           bh_lib
        end;

if Globals.remake_theory_files 
then ( load_theory "pair";
       Theory.new_theory "BASIC_HOL";
       Theory.new_parent "num";
      ())
else Theory.load_theory "BASIC_HOL";


(* Need "" at head of theory_path in order for absolute paths used in 
   library theories to make sense when loading theory files.
   Complicated: see interaction with "loaded" definition above.
*)
val _ = (Lib.cons_path "" Globals.theory_path;
         Library.load_library_in_place basic_hol_lib);
