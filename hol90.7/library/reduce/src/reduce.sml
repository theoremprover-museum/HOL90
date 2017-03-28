(*===========================================================================
== LIBRARY:     reduce (part IV)                                           ==
==                                                                         ==
== DESCRIPTION: Reduction tools using all the conversions in the library   ==
==                                                                         ==
== AUTHOR:      John Harrison                                              ==
==              University of Cambridge Computer Laboratory                ==
==              New Museums Site                                           ==
==              Pembroke Street                                            ==
==              Cambridge CB2 3QG                                          ==
==              England.                                                   ==
==                                                                         ==
==              jrh@cl.cam.ac.uk                                           ==
==                                                                         ==
== DATE:        18th May 1991                                              ==
== REVISED:      8th July 1991                                             ==
==                                                                         ==
== TRANSLATOR:  Kim Dam Petersen (kimdam@tfl.dk)                           ==
============================================================================*)

structure Boolconv =
    Boolconv_funct (structure Dest = Dest);
open Boolconv;

structure Arithconv =
    Arithconv_funct (structure Dest = Dest);
open Arithconv;

structure Redconv =
    Redconv_funct(structure Boolconv  = Boolconv
	          structure Arithconv = Arithconv);
open Redconv;
