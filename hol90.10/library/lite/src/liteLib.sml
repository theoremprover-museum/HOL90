signature liteLib_sig = 
sig
  structure LiteLib : LiteLib_sig
  structure Trace : Trace_sig
  structure Equal : Equal_sig
end;

structure liteLib : liteLib_sig =
struct

  structure LiteLib = LiteLib
  structure Trace = Trace
  structure Equal = Equal;


(*---------------------------------------------------------------------------
 * Help files not yet available.
 *---------------------------------------------------------------------------*)
(*  val _ = Lib.cons_path (!Globals.HOLdir^"library/lite/help/entries/") 
                        Globals.help_path;
*)
end;
