(*---------------------------------------------------------------------------
 * This ensures that the "real" theory "TRANSC" is loaded. TRANSC has 
 * all the other theories of the "real" library in its ancestry.
 *---------------------------------------------------------------------------*)
structure realLib : sig end =
struct

  val _ = Lib.try (CoreHol.Theory.loadLibThry "real") "TRANSC"

end;
