(************************ benchmark.sml *********************************)
(*                                                                      *)
(* Author: Ralf Reetz                                                   *)
(* Date:   5.10.1994                                                    *)
(*                                                                      *)
(* Description:                                                         *)
(*                                                                      *)
(*  see benchmark.sig                                                   *)
(*                                                                      *)
(* Used files:     benchmark.sig                                        *)
(* Used modules:   System.Timer, IO, Integer, Real                      *)
(* Used theories:                                                       *)
(* Used libraries:                                                      *)
(*                                                                      *)
(************************************************************************)

structure benchmark : BENCHMARK =
struct

open System.Timer;
open IO;

fun output_benchmark {filename_summary  : string,
                      filename_details  : string,
                      rator             : ('a -> 'b),
                      mk_rand           : int -> 'a,
                      mk_step           : int -> int,
                      mk_index          : int -> int,
                      max_count         : int} =
 let
  fun nchar c n =
   if n<=0 then
    []
   else
    c::(nchar c (n-1))
  fun divide_point [] =
   ([],[])
  | divide_point (h::t) =
   if h="." then
    ([],t)
   else
    let
     val (l1,l2) = (divide_point t)
    in
     (h::l1,l2)
    end
  (*
    Input:
     a value of time
    Output:
     string of length 8 with 3 digits after the period
  *)
  fun time_2_string t =
   let
    val (s1,s2) = divide_point(explode(System.Timer.makestring t))
    val s2' = if length s2<3 then
               append s2 (nchar "0" (3-(length s2)))
              else
               (hd s2)::((hd(tl s2))::[hd(tl(tl s2))])
    val s1' = if length s1<4 then
               append (nchar " " (4-(length s1))) s1
              else
               s1
   in
    implode(append s1' ("."::s2'))
   end
  fun time_2_real t =
   let
    fun poweroften n = 
     if n<=0 then
      1
     else
      10*(poweroften (n-1))
    fun stringl_2_int l =
     let
      fun do_it [] base =
       0
      | do_it (h::t) base =
       (((ord h)-48)*base) + (do_it t (base div 10))
     in
      do_it l (poweroften((length l)-1))
     end
    val (s1,s2) = divide_point(explode(System.Timer.makestring t))
    val r1      = real(stringl_2_int s1)
    val r2      = real(stringl_2_int s2)/(real(poweroften((length s2))))
   in
    r1+r2
   end
  (*
    Input:
     string, n
    Output:
     adjust string to the right for length n
  *)
  fun adjust s n =
   (implode(nchar " " (n-(size s))))^s
  (*
    Input:
     count
    Output:
     needed time paired with needed thm_count and the complete sum of 
     thm_count for one run
  *)
  fun measure step =
   let
    val rand        = mk_rand step
    val _ = reset_thm_count();
    val _ = counting_thms true;
    val tim       = start_timer()
    val t0        = check_timer(tim)
    val fx        = rator rand
    val t1        = check_timer(tim) 
    val {ABS        = result1 ,
         ASSUME     = result2 ,
         BETA_CONV  = result3 ,
         DISCH      = result4 ,
         INST_TYPE  = result5 ,
         MP         = result6 ,
         REFL       = result7 ,
         SUBST      = result8 ,
         axiom      = result9 ,
         definition = result10 ,
         drule      = result11 ,
         from_disk  = result12 ,
         other      = result13 ,
         valid_tac  = result14} = thm_count()
    val result   = result1 + result2 + result3 + result4 + result5 +
                   result6 + result7 + result8 + result9 + result10 +
                   result11 + result12 + result13 + result14
   in
    (t1,result1,result2,result3,result4,result5,result6,result7,result8,
    result9,result10,result11,result12,result13,result14,result)
   end
  (* initialization *)
  val file_summary  = open_out filename_summary
  val file_details  = open_out filename_details
  val count = ref 0
  val step  = ref (mk_step 0)
 in
  (* header output for summary *)
  output(file_summary,"Index      Time       Rules      Rules/Time\n\n");
  (* header output for details *)
  output(file_details,"Index     ABS  ASSUME    BETA   DISCH    INST "^
                            "     MP    REFL   SUBST   axiom  defini "^
                            "  drule    from  others   valid\n");
  output(file_details,"                        _CONV            TYPE "^
                            "                                   tion "^
                            "           disk            _tac\n\n");
  while ((!count) <= max_count) do
  (
   (* computing benchmark for one run *)
   let
    val (t,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r) = measure (!step)
   in
    (* one run output for summary *)
    output(file_summary,adjust (Integer.makestring(mk_index (!step))) 5);
    output(file_summary,"   ");
    output(file_summary,time_2_string t);
    output(file_summary,"   ");
    output(file_summary,adjust (Integer.makestring r) 8);
    output(file_summary,"   ");
    output(file_summary,
    (if (time_2_real t) = 0.0 then
     "       0.0"
    else
     adjust 
     (Real.makestring
     ((real(Real.ceiling(((real(r))/(time_2_real t))*1000.0)))/1000.0))
     10));
    output(file_summary,"\n");
    (* one run output for details *)
    output(file_details,adjust (Integer.makestring(mk_index (!step))) 5);
    output(file_details," ");
    output(file_details,adjust (Integer.makestring r1) 7);
    output(file_details," ");
    output(file_details,adjust (Integer.makestring r2) 7);
    output(file_details," ");
    output(file_details,adjust (Integer.makestring r3) 7);
    output(file_details," ");
    output(file_details,adjust (Integer.makestring r4) 7);
    output(file_details," ");
    output(file_details,adjust (Integer.makestring r5) 7);
    output(file_details," ");
    output(file_details,adjust (Integer.makestring r6) 7);
    output(file_details," ");
    output(file_details,adjust (Integer.makestring r7) 7);
    output(file_details," ");
    output(file_details,adjust (Integer.makestring r8) 7);
    output(file_details," ");
    output(file_details,adjust (Integer.makestring r9) 7);
    output(file_details," ");
    output(file_details,adjust (Integer.makestring r10) 7);
    output(file_details," ");
    output(file_details,adjust (Integer.makestring r11) 7);
    output(file_details," ");
    output(file_details,adjust (Integer.makestring r12) 7);
    output(file_details," ");
    output(file_details,adjust (Integer.makestring r13) 7);
    output(file_details," ");
    output(file_details,adjust (Integer.makestring r14) 7);
    output(file_details,"\n")
   end;
   (* preparing next run *)
   count := (!count) + 1;
   step  := mk_step (!step)
  );
  (* that's it *)
  close_out file_summary;
  close_out file_details
 end;

end;
