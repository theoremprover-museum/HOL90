structure IntegerTheoryLoaded : sig end = 
struct

  val group_path = (!Globals.HOLdir)^"library/group/theories/"
                        ^SysParams.theory_file_type^"/";


  val _ = Lib.cons_path group_path Globals.theory_path;
  val _ = CoreHol.Theory.loadLibThry"integer" "integer"
end;
