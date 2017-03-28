(*---------------------------------------------------------------------------
 * This ensures that the "List" theory is loaded before the other structures
 * in this library are evaluated.
 *---------------------------------------------------------------------------*)
structure ListTheoryLoaded =
struct

  val _ = Lib.try (CoreHol.Theory.loadLibThry "list") "List"

end;
