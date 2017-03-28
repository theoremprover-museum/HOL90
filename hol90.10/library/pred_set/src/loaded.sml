(*---------------------------------------------------------------------------
 * This ensures that the "pred_set" theory is present before the other 
 * structures in this library are evaluated.
 *---------------------------------------------------------------------------*)
structure pred_setTheoryLoaded =
struct

  val _ = Lib.try (CoreHol.Theory.loadLibThry "pred_set") "pred_set"

end;
