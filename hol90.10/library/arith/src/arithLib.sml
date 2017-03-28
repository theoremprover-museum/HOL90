structure arithLib 
         : sig   structure Arith : Arith_sig
                 structure Arith_cons : Arith_cons_sig
           end =
struct
  structure Arith = Arith
  structure Arith_cons = Arith_cons

  val _ = Lib.cons_path (!Globals.HOLdir^"library/arith/help/entries/") 
                        Globals.help_path;

end;
