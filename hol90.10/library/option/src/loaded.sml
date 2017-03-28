(*---------------------------------------------------------------------------
 * This ensures that the "option" theory is loaded before the other structures
 * in this library are evaluated.
 *---------------------------------------------------------------------------*)
structure optionTheoryLoaded =
struct

  val _ = Lib.try (CoreHol.Theory.loadLibThry "option") "option"

end;
