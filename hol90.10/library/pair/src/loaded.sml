(*---------------------------------------------------------------------------
 * This ensures that the "" theory is loaded before the other structures
 * in this library are evaluated.
 *---------------------------------------------------------------------------*)
structure pairTheoryLoaded =
struct

  val _ = Lib.try (CoreHol.Theory.loadLibThry "pair") "pair_thms"

end;
