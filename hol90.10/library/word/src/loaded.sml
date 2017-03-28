(*---------------------------------------------------------------------------
 * This ensures that the "word" theory is loaded before the other 
 * structures in this library are evaluated.
 *---------------------------------------------------------------------------*)
structure wordTheoryLoaded =
struct

  (*--------------------------------------------------------------------------
   * We need to manipulate the library theory path as well, so that
   * "res_quan" and "List" theories are found by load_theory.
   *-------------------------------------------------------------------------*)
  
  val _ = Lib.cons_path (!Globals.HOLdir^"library/res_quan/theories/"
                                        ^SysParams.theory_file_type^"/")
                        Globals.theory_path;



  val _ = Lib.cons_path (!Globals.HOLdir^"library/list/theories/"
                                        ^SysParams.theory_file_type^"/")
                        Globals.theory_path;



  val _ = Lib.try (CoreHol.Theory.loadLibThry "word") "word"

end;
