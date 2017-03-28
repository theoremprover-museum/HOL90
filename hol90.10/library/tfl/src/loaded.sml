(*---------------------------------------------------------------------------
 * This ensures that the "WF" theory is loaded.
 *---------------------------------------------------------------------------*)
structure WFTheoryLoaded : sig end =
struct

  val _ = Lib.try (CoreHol.Theory.loadLibThry "tfl") "WF"

end;
