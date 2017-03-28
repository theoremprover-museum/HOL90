(*---------------------------------------------------------------------------
 * This ensures that the "res_quan" theory is loaded before the other 
 * structures in this library are evaluated.
 *---------------------------------------------------------------------------*)
structure res_quanTheoryLoaded =
struct

  val _ = Lib.try (CoreHol.Theory.loadLibThry "res_quan") "res_quan"

end;
