structure wordLib : Word_convs_sig =
struct
 
  open Word_convs;
  open wordTheoryLoaded 

  val _ = Lib.cons_path (!Globals.HOLdir^"library/word/help/entries/") 
                        Globals.help_path;

end;
