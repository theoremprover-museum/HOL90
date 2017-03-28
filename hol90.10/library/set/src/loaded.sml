(*---------------------------------------------------------------------------
 * This ensures that the "set" theory is present before the other 
 * structures in this library are evaluated.
 *---------------------------------------------------------------------------*)
structure setTheoryLoaded =
struct

  val _ = Lib.try (CoreHol.Theory.loadLibThry "set") "set"

end;
