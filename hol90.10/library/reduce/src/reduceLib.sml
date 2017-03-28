signature reduceLib_sig =
sig
  structure Dest      : Dest_sig
  structure Boolconv  : Boolconv_sig
  structure Arithconv : Arithconv_sig
  structure Redconv   : Redconv_sig
end;

structure reduceLib :reduceLib_sig =
struct
  structure Dest      = Dest
  structure Boolconv  = Boolconv_funct (structure Dest = Dest);

  structure Arithconv = Arithconv_funct (structure Dest = Dest);

  structure Redconv   = Redconv_funct(structure Boolconv  = Boolconv
	                              structure Arithconv = Arithconv);

  val _ = Lib.cons_path (!Globals.HOLdir^"library/reduce/help/entries/") 
                        Globals.help_path;

end;
