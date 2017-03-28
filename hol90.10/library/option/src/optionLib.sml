signature optionLib_sig = 
sig
  type simpset
 	val OPTION_ss : simpset
	val option_ss : simpset
end;


structure optionLib : optionLib_sig = 
struct

type simpset = simpLib.Simplifier.simpset;

local open optionTheoryLoaded;
      open simpLib;
      open CoreHol.Dsyntax CoreHol.Thm CoreHol.Theory Drule ;
      open Simplifier arith_ss;
      infix ++

val OPTION_data = rewrites
  (map ((fn th => if (is_neg (concl th)) then EQF_INTRO th else th) o SPEC_ALL)
       (CONJUNCTS (theorem "option" "option_CLAUSES")));

in

  val OPTION_ss = mk_simpset [OPTION_data];
  val option_ss = hol_ss ++ OPTION_data;

end;

end;
