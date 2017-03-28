structure hol88Lib : Compat_sig =
struct
  open Compat

  val _ = Lib.cons_path (!Globals.HOLdir^"library/hol88/help/entries/") 
                        Globals.help_path;
end;
