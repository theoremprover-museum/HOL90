signature prog_logicLib_sig = 
sig
  structure PC : HOARE_LOGIC
  structure TC : HALTS_LOGIC
end;

structure prog_logicLib : prog_logicLib_sig =
struct
  open prog_logicTheoryLoaded;

  structure Syntax = Syntax();
  structure Trans = Translation();
  structure HolMatch = Hol_Match();
  structure Bnd = Bnd_Conv(Syntax);

  structure PC = Hoare_Logic(structure Syntax = Syntax 
                             structure Trans = Trans 
                             structure Holm = HolMatch
                             structure Bnd = Bnd);

  structure TC = Halts_Logic(structure Syntax = Syntax 
                             structure Trans = Trans 
                             structure Holm = HolMatch
                             structure Bnd = Bnd);


 val _ = Lib.say ("\n" ^
    ">> Open structure prog_logicLib.PC for rules & tactics for \
             \partial correctness \n" ^ 
    ">> Open structure prog_logicLib.TC for rules & tactics for \
             \total correctness\n\n");

end;


