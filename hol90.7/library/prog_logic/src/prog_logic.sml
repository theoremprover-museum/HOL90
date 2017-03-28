
structure Syntax = Syntax();
    
structure Trans = Translation();
    
structure HolMatch = Hol_Match();

structure Bnd = Bnd_Conv(Syntax);

structure PC = Hoare_Logic(structure Syntax = Syntax 
                           structure Trans = Trans 
                           structure Holm= HolMatch
                           structure Bnd = Bnd);

structure TC = Halts_Logic(structure Syntax = Syntax 
                           structure Trans = Trans 
                           structure Holm= HolMatch
                           structure Bnd = Bnd);


say ("\n" ^
     ">> Open structure PC for rules & tactics for partial correctness \
\specifications\n" ^ 
     ">> Open structure TC for rules & tactics for total correctness \
\specifications\n\n");


