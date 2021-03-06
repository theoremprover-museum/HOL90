signature setLib_sig =
sig
 type tactic
 type conv

  val SET_SPEC_CONV : conv
  val SET_INDUCT_TAC : tactic
  val FINITE_CONV : conv
  val IN_CONV :conv -> conv
  val DELETE_CONV :conv -> conv
  val UNION_CONV :conv -> conv
  val INSERT_CONV :conv -> conv
  val IMAGE_CONV :conv -> conv ->conv

end;

structure setLib : setLib_sig =
struct

 type tactic = Abbrev.tactic
 type conv = Abbrev.conv

  open setTheoryLoaded;
  open Gspec
  open Set_ind
  open Fset_conv
    
  val _ = Lib.cons_path (!Globals.HOLdir^"library/set/help/entries/") 
                         Globals.help_path;
end;
