structure GroupTheoryLoaded : sig end = 
struct
  val _ = CoreHol.Theory.loadLibThry"group" "elt_gp"
end;
