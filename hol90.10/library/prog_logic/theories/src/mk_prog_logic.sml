(*---------------------------------------------------------------------------
 * Gathers everything together as children of one theory.
 *---------------------------------------------------------------------------*)
new_theory "prog_logic";

new_parent "hoare_logic_tc";
new_parent "hoare_logic_pc";
new_parent "dijkstra";

(* new_parent "dynamic_logic" -- Omitted in hol90 version, sorry! *)

close_theory();

export_theory();
