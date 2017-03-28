(*===========================================================================
== LIBRARY:     reduce (Part I)                                            ==
==                                                                         ==
== DESCRIPTION: Conversions for reducing boolean expressions.              ==
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
==                                                                         ==
== TRANSLATOR:  Kim Dam Petersen (kimdam@tfl.dk)                           ==
============================================================================*)

structure Dest : Dest_sig =
struct

fun failwith function = raise HOL_ERR{origin_structure = "Dest",
                                      origin_function = function,
                                      message = ""};

val num_ty   = Type.mk_type{Tyop= "num", Args= []};

(*-----------------------------------------------------------------------*)
(* dest_op - Split application down spine, checking head operator        *)
(*-----------------------------------------------------------------------*)

fun dest_op opr tm =
    let val (opr',arg) = Dsyntax.strip_comb tm
    in
	if (opr=opr')
        then arg
        else failwith "dest_op"
    end;

(*-----------------------------------------------------------------------*)
(* term_of_int - Convert ML integer to object level numeric constant     *)
(*-----------------------------------------------------------------------*)

val term_of_int =
  fn n => Dsyntax.mk_const{Name= int_to_string n, Ty= num_ty};

(*-----------------------------------------------------------------------*)
(* int_of_term - Convert object level numeric constant to ML integer     *)
(*-----------------------------------------------------------------------*)

val int_of_term =
  string_to_int o (#Name) o Term.dest_const;

end
