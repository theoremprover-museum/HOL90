structure res_quanLib : res_quanLib_sig =
struct

  open res_quanTheoryLoaded;
  open Res_quan;
  open Cond_rewrite;

  val _ = Lib.cons_path (!Globals.HOLdir^"library/res_quan/help/entries/") 
                        Globals.help_path;

end;
