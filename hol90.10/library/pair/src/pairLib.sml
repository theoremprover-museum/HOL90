structure pairLib : pairLib_sig =
struct

  open pairTheoryLoaded;
  open Pair_basic;
  open Pair_both1;
  open Pair_forall;
  open Pair_exists;
  open Pair_both2;
  open Pair_conv;

    
    val _ = Lib.cons_path (!Globals.HOLdir^"library/pair/help/defs/") 
                           Globals.help_path;
    val _ = Lib.cons_path (!Globals.HOLdir^"library/pair/help/entries/") 
                          Globals.help_path;
    val _ = Lib.cons_path (!Globals.HOLdir^"library/pair/help/thms/") 
                          Globals.help_path;
    val _ = Lib.say "Pair library - Copyright (c) Jim Grundy 1992\n";

end;
