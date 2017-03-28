structure Trace : Trace_sig =
struct

 type term = CoreHol.Term.term
 type thm = CoreHol.Thm.thm

local open Exception;
      val print_term = CoreHol.Hol_pp.print_term;
      val print_thm = CoreHol.Thm.print_thm;
      val concl = CoreHol.Thm.concl;
      val rhs = CoreHol.Dsyntax.rhs;
      val say = Lib.say;

in
   (* ---------------------------------------------------------------------
    * Tracing utilities
    * ---------------------------------------------------------------------*)

    datatype action = TEXT of string 
      | REDUCE of (string * CoreHol.Term.term)
      | REWRITING of (CoreHol.Term.term * CoreHol.Thm.thm)
      | SIDECOND_ATTEMPT of CoreHol.Term.term
      | SIDECOND_SOLVED of CoreHol.Thm.thm
      | SIDECOND_NOT_SOLVED of CoreHol.Term.term
      | OPENING of (CoreHol.Term.term * CoreHol.Thm.thm)
      | PRODUCE of (CoreHol.Term.term * string * CoreHol.Thm.thm)
      | IGNORE of (string * CoreHol.Thm.thm)
      | MORE_CONTEXT of CoreHol.Thm.thm;

   val trace_hook : ((int * action) -> unit) ref = ref (fn (n,s) => ());
   fun trace x = (!trace_hook) x

val trace_level = ref 0;
fun tty_trace (TEXT s) = (say "  "; say s; say "\n")
  | tty_trace (REDUCE (s,tm)) = (say "  "; say s; say " "; print_term tm; say "\n")
  | tty_trace (REWRITING (tm,thm)) = 
    (say "  rewriting "; print_term tm; say " with "; print_thm thm; say "\n")
  | tty_trace (SIDECOND_ATTEMPT tm) =
    (say "  trying to solve: "; print_term tm; say "\n")
  | tty_trace (SIDECOND_SOLVED thm) =
    (say "  solved! "; print_thm thm; say "\n")
  | tty_trace (SIDECOND_NOT_SOLVED tm) =
    (say "  couldn't solve: "; print_term tm; say "\n")
  | tty_trace (OPENING (tm,thm)) = 
    (say "  "; print_term tm; say " matches congruence rule "; print_thm thm; say "\n")
  | tty_trace (PRODUCE (tm,s,thm)) =
    (say "  "; print_term tm; say " via "; say s; say " simplifies to: "; 
     print_term (rhs (concl thm)) handle HOL_ERR _ => print_thm thm; say "\n")
  | tty_trace (IGNORE (s,thm)) =
    (say "  ignoring "; say s; say " rewrite "; print_thm thm; say "\n")
  | tty_trace (MORE_CONTEXT thm) =
    (say "  more context: "; print_thm thm; say "\n");

val _ = trace_hook := (fn (n,a) => if (n <= !trace_level) then tty_trace a else ());

end (*local*)
end (* struct *)
