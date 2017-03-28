(************************ example.sml ***********************************)
(*                                                                      *)
(* Author: Ralf Reetz                                                   *)
(* Date:   5.10.1994                                                    *)
(*                                                                      *)
(* Description:                                                         *)
(*                                                                      *)
(*  example for benchmark, as described in                              *)
(*  benchmark/help/entries/output_benchmark.doc                         *)
(*                                                                      *)
(* Used files:                                                          *)
(* Used modules:                                                        *)
(* Used theories:                                                       *)
(* Used libraries: taut                                                 *)
(*                                                                      *)
(************************************************************************)

val _ = load_library{lib=find_library "more_utils", theory="-"};
val _ = load_library{lib=find_library "taut",     theory="-"};

fun mk_rand n =
 if n<=1 then
  (--`T\/F`--)
 else
  let
   val t = mk_rand (n-1)
  in
   (--`T\/F /\ ^t`--)
  end;

fun number_of_literals n =
 2 * ( n + 1 );

val _ =
 benchmark.output_benchmark
 {filename_summary  = "rewrite_summary.txt",
  filename_details  = "rewrite_details.txt",
  rator             = (REWRITE_CONV []),
  mk_rand           = mk_rand,
  mk_index          = number_of_literals,
  max_count         = 20,
  mk_step           = (fn n => n+10)};

val _ = 
 benchmark.output_benchmark
 {filename_summary  = "taut_summary.txt",
  filename_details  = "taut_details.txt",
  rator             = Taut.TAUT_CONV,
  mk_rand           = mk_rand,
  mk_index          = number_of_literals,
  max_count         = 20,
  mk_step           = (fn n => n+10)};

