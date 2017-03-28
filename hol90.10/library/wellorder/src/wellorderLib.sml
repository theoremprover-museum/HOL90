(*---------------------------------------------------------------------------
 * This ensures that the "wellorder" theory is loaded.
 *---------------------------------------------------------------------------*)
structure wellorderLib : sig end =
struct

  val _ = Lib.try (CoreHol.Theory.loadLibThry "wellorder") "WELLORDER"

(* Currently useless because no docs!

 val _ = Lib.cons_path (!Globals.HOLdir^"library/wellorder/help/entries/") 
                        Globals.help_path;
*)

end;
