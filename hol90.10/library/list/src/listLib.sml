structure listLib : List_conv_sig =
struct

  open ListTheoryLoaded;
  open List_conv1
  open List_conv2

    val _ = Lib.cons_path (!Globals.HOLdir^"library/list/help/defs/") 
                           Globals.help_path;
    val _ = Lib.cons_path (!Globals.HOLdir^"library/list/help/entries/") 
                          Globals.help_path;
    val _ = Lib.cons_path (!Globals.HOLdir^"library/list/help/thms/") 
                          Globals.help_path;
end;
