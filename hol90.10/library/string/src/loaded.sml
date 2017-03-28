(*---------------------------------------------------------------------------
 * This ensures that the "string" theory is present before the other 
 * structures in this library are evaluated.
 *---------------------------------------------------------------------------*)
structure stringTheoryLoaded =
struct

  val _ = Lib.try (CoreHol.Theory.loadLibThry "string") "ascii"
  val _ = Lib.try (CoreHol.Theory.loadLibThry "string") "string"

end;
