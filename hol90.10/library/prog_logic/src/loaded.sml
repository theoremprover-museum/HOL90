(*---------------------------------------------------------------------------
 * This ensures that the "prog_logic" theory is present before the other 
 * structures in this library are evaluated.
 *---------------------------------------------------------------------------*)
structure prog_logicTheoryLoaded =
struct

  val _ = Lib.try (CoreHol.Theory.loadLibThry "prog_logic") "prog_logic"

end;
