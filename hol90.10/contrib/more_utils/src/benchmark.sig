(************************ benchmark.sig *********************************)
(*                                                                      *)
(* Author: Ralf Reetz                                                   *)
(* Date:   5.10.1994                                                    *)
(*                                                                      *)
(* Description:                                                         *)
(*                                                                      *)
(*  See output_benchmark.doc in benchmark/help/entries                  *)
(*                                                                      *)
(* Used files:                                                          *)
(* Used modules:                                                        *)
(* Used theories:                                                       *)
(* Used libraries:                                                      *)
(*                                                                      *)
(************************************************************************)

signature BENCHMARK =
sig

val output_benchmark : {filename_summary  : string,
                        filename_details  : string,
                        rator             : ('a -> 'b),
                        mk_rand           : int -> 'a,
                        mk_step           : int -> int,
                        mk_index          : int -> int,
                        max_count         : int} -> unit; 

end;

