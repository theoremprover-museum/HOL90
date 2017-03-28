(* Load the library *)

load_library{lib = find_library "pev_rewrite", theory = "-"};


local val ADD = definition "arithmetic" "ADD"
in
 val ADD1 = CONJUNCT1 ADD
 val ADD2 = CONJUNCT2 ADD
end;

local
  fun mk_add x y = list_mk_comb(--`$+`--, [x,y])
in
  fun fib 0 = --`SUC 0`--
    | fib 1 = --`SUC 0`--
    | fib n = mk_add (fib (n-2)) (fib (n-1));
end;

(* Generate the file "temp.sml" containing the optimized rewriter. *)
convgen [(ADD1,"ADD1"),(ADD2,"ADD2")];

use "temp.sml";

(* Now use the fast rewriter! *)
REDEPTH_CONV conv (fib 5);

