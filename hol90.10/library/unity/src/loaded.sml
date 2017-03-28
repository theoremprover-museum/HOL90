(*---------------------------------------------------------------------------
 * This ensures that the "unity" theory "comp_unity" is loaded. comp_unity 
 * has all the other theories of the "unity" library in its ancestry.
 *---------------------------------------------------------------------------*)
structure unityTheoryLoaded : sig end =
struct

  val _ = Lib.try (CoreHol.Theory.loadLibThry "unity") "comp_unity"

end;
