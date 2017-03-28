(* This file makes the base theory on top of which we are going to build a
 * number of theories related to CSP.
 **************************************************************************)

(* Get some theories that we need *)
map add_theory_to_sml ["list","arithmetic","prim_rec","num","pair","combin"];

(* Go to set theory so as to make it one of the parents of CSP_base *)
load_theory "set"; new_theory "CSP_base";

(* Get some libraries *)
map load_library_in_place[taut_lib, set_lib, string_lib];
map add_theory_to_sml [ "string", "set"];

use "rules_and_tacs.sml";

close_theory(); export_theory();

save_hol "./CSP_hol";

