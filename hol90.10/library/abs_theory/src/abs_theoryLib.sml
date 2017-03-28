structure abs_theoryLib 
         : sig structure Imp_rewrite : Imp_rewrite_sig
               include Abs_theory_sig 
           end =
struct
  structure Imp_rewrite = Imp_rewrite;
  open Abs_theory;

  val _ = Lib.cons_path (!Globals.HOLdir^"library/abs_theory/help/entries/") 
                        Globals.help_path;

end;
