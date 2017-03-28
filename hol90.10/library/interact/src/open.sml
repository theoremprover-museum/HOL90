val _ = Compiler.Control.quotation := true;
val _ = CM.make' "/usr/groups/hol/kxs/hol97/library/interact/sources.cm";
val _ = Hol90.pp_on();

val _ = Portable.say"\nOpening the Hol90 structure.\n";
val _ = Portable.flush_out Portable.std_out;
val DevNull = Portable.open_out"/dev/null"; (* Tisk tisk, never closed! *)

(*---------------------------------------------------------------------------
 * When the Hol90 structure gets opened, thousands of value bindings get 
 * printed to the screen, so I just turn printing off while that is happening.
 *---------------------------------------------------------------------------*)
val _ = Compiler.Control.Print.out :=
         {flush = fn() => (),
          say = fn s => Portable.output(DevNull,s)}

open Hol90;
infix THEN_TCL ORELSE_TCL THEN THENL ORELSE THENC ORELSEC ## |->;

val _ = Compiler.Control.Print.out :=
         {flush = fn() => Portable.flush_out Portable.std_out,
          say = fn s => Portable.output(Portable.std_out,s)}

(* Load hol-init bindings *)
local val init_fname = "/hol-init.sml"
      val local_init_fname = "."^init_fname
in
val _ = if (Lib.file_exists_for_reading local_init_fname)
          then Portable.use local_init_fname
           else (case Portable.getEnv "HOME"
                 of NONE => ()
                | SOME home_init =>
                   let val home_init_fname = home_init ^init_fname
                   in if (Lib.file_exists_for_reading home_init_fname)
                       then Portable.use home_init_fname
                        else ()
                   end)
end;
