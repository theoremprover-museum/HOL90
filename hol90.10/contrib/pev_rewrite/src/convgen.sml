(* ----------------------------------------------------------------------- *)
(* MW Conversion Generator -- an automatic tool for producing conversions. *)
(*                                                                         *)
(* Copyright (C) 1993, 1994 by Morten Welinder                             *)
(*                                                                         *)
(* Author: Morten Welinder (terra@diku.dk)                                 *)
(*                                                                         *)
(* This file is not part of GNU Emacs.                                     *)
(* This file is distributed under the same terms as GNU Emacs.             *)
(*                                                                         *)
(* GNU Emacs is free software; you can redistribute it and/or modify       *)
(* it under the terms of the GNU General Public License as published by    *)
(* the Free Software Foundation; either version 2, or (at your option)     *)
(* any later version.                                                      *)
(*                                                                         *)
(* GNU Emacs is distributed in the hope that it will be useful,            *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of          *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the           *)
(* GNU General Public License for more details.                            *)
(*                                                                         *)
(* You should have received a copy of the GNU General Public License       *)
(* along with GNU Emacs; see the file COPYING.  If not, write to           *)
(* the Free Software Foundation, 675 Mass Ave, Cambridge, MA 02139, USA.   *)
(* ----------------------------------------------------------------------- *)
(* This program is a general tool for turning a list of theorems into a    *)
(* conversion that does rewriting with respect to the theorems which are   *)
(* supposed to be equality-stating theorems.                               *)
(*                                                                         *)
(* This is more or less what GEN_REWRITE_CONV does so why bother?  Well,   *)
(* this tool does not really generate a conversion, but _source code_ for  *)
(* a conversion.  This means that the compiler will get a chance to look   *)
(* at the code again, and as a result the conversion is much faster.       *)
(*                                                                         *)
(* As this code inspects the syntax of the theorems only once (as opposed  *)
(* to once for each term that the conversion is used on), and as it        *)
(* produces very little garbage on its way there are more reasons why it   *)
(* is more efficient than GEN_REWRITE_CONV.                                *)
(*                                                                         *)
(* This tool is constructed as a `generating extension' of a rewriter.     *)
(* Producing `generating extensions' is a technique closely related to     *)
(* partial evaluation which happens to be my field.  In fact, my master's  *)
(* thesis was about the automatic production of generating extension of    *)
(* Standard ML programs.                                                   *)
(*                                                                         *)
(* The size of the produced conversion is linear with respect to the size  *)
(* of the input theorems.  The running time for the conversion generator   *)
(* is insignificant.                                                       *)
(*                                                                         *)
(* The conversions produced (on which I have no copyright claim) are       *)
(* dependent on the theorems used to construct them.  This is for proof-   *)
(* security reasons.  The dependency is checked.                           *)
(*                                                                         *)
(* The program prints usage instructions when compiled.  Note that all     *)
(* theorems must be given both as a theorem and as a SML-expression (text) *)
(* that will evaluate to the theorem.                                      *)
(*                                                                         *)
(*                        What a day for a daydream                        *)
(*                        What a day for a daydreaming boy                 *)
(*                        And I'm lost in a daydream                       *)
(*                        Dreaming 'bout my bundle of joy                  *)
(*                        And even if time ain't really on my side         *)
(*                        It's one of those days for taking a walk outside *)
(*                        I'm blowing the day to take a walk in the sun    *)
(*                        And fall on my face on somebody's new-mown lawn  *)
(*                                                                         *)
(*                               -- John Sebastian                         *)
(* ----------------------------------------------------------------------- *)
local
  open Rsyntax   (* use record syntax *)
  val program_name = "MW Conversion Generator";
  val program_version = "0,10";
  (* -------------------------------------------------------------- *)
  (* Debugging stuff.  *)
  exception Crash;
  val agressive_comb = true;

  fun fishy txt =
    output (std_out, "There is something fishy here:\n  "^
            txt^"\n"^
            "Please report this to Morten Welinder (terra@diku.dk)\n");
  (* -------------------------------------------------------------- *)
  (* Pretty-printing stuff. *)
  val outfile = ref std_out; (* Changed below. *)
  val null_device = ref std_out; (* Changed below. *)
  val indent = ref 0;

  fun out s =
    let
      fun spaces 0 = ()
        | spaces 1 = output (!outfile, " ")
        | spaces 2 = output (!outfile, "  ")
        | spaces 3 = output (!outfile, "   ")
        | spaces 4 = output (!outfile, "    ")
        | spaces 5 = output (!outfile, "     ")
        | spaces n = (output (!outfile, "      "); spaces (n-6))
    in
      if s<>"" then
        (spaces (!indent); output (!outfile, s))
      else
        ();
      output (!outfile, "\n")
    end

  fun movein () = indent := !indent + 2;
  fun moveout () = indent := !indent - 2;

  (* For the benefit of better language: *)
  fun pluralis (sing,plu,n) = if n = 1 orelse n = ~1 then sing else plu;
  fun pluraliss n = pluralis ("","s",n);

  (* Convert an integer to its string representation.  `makestring' is
     not Standard ML, but I'm lazy. *)
  fun int2str (i:int) = makestring i;

  (* Convert a term to its string representation adding types only
     if we have to.  The assignment to System.Print.out kills the
     type error message from the parser.  This is a dirty way, but
     it seems to be the only way.  *)
  fun term2str tm =
    let
      val save_Globals_show_types = !Globals.show_types;
      val save_System_Print_out = !System.Print.out;
      fun cleanup () =
        (Globals.show_types := save_Globals_show_types;
         System.Print.out := save_System_Print_out);
      exception Hamlet;
    in
      Globals.show_types := false;
      System.Print.out := !null_device;
      let
        val result =
          let
            val txt = term_to_string tm;
          in
            if tm=string_to_term txt then txt else raise Hamlet
          end handle _ =>
            (Globals.show_types := true;
             term_to_string tm)
      in
        cleanup ();
        "--`"^result^"`--"
      end handle x => (cleanup (); raise x) (* Just in case... *)
    end

  (* Convert a string into its SML-representation. *)
  fun quote s =
    let
      (* \034 is a double quote that doesn't confuse my Emacs. *)
      fun quote1 [] = ["\034"]
        | quote1 ("\034"::xs) = ("\\"::"\034"::quote1 xs)
        | quote1 ("\\"::xs) = ("\\"::"\\"::quote1 xs)
        | quote1 (x::xs) = x::quote1 xs;
    in
      implode ("\034"::quote1 (explode s))
    end
  (* -------------------------------------------------------------- *)
  (* Split a list into those that satisfy a predicate and those that don't. *)
  fun split _ [] = ([],[])
    | split p (x::xs) =
      let
        val (g,b) = split p xs
      in
        if p x then (x::g,b) else (g,x::b)
      end

  (* Concatenate the elements of a list of lists.  Simple, but slow. *)
  fun concat [] = []
    | concat (x::xs) = x @ (concat xs);

  fun polymorphic ty = type_vars ty <> nil;
  (* -------------------------------------------------------------- *)
  (* Object oriented programming in Standard ML!  The parameter is  *)
  (* only present to beat the type system.                          *)
  fun database (element : ''_a) =
    let
      exception NotFound
      val count = ref 0;
      val base = ref (nil : (''_a * int) list);
      fun find key =
        let
          fun search [] = raise NotFound
            | search ((key',data)::rest) = 
              if key=key' then data else search rest
        in
          search (!base)
        end

      and add key =
        (find key; ())
        handle NotFound =>
          (count := !count + 1;
           base := (key,!count) :: (!base))

      and map' f = (map f (rev (!base)); ())

      and get_count () = !count
    in
      {find      = find,
       add       = add,
       get_count = get_count,
       map       = map'}
    end;

  (* A database for monomorphic constants.  *)
  val const_base = database (--`T`--);
  fun const_name tm = "cst"^int2str (#find const_base tm);

  (* A database for polymorphic types.  *)
  val type_base = database (==`:bool`--);
  fun type_name ty = "type"^int2str (#find type_base ty);

  fun walk_term tm =
    if is_comb tm then
      (walk_term (rator tm); walk_term (rand tm))
    else if is_abs tm then
      walk_term (body tm)
    else if is_var tm then
      let
        val ty = type_of tm
      in
        if polymorphic ty then
          #add type_base ty
        else
          ()
      end
    else (* const *)
      if polymorphic (type_of tm) then
        ()
      else
        #add const_base tm;

  fun output_constants () =
    let
      val count = #get_count const_base ()
      fun print1 (tm,n) =
        out ("val cst"^int2str n^" = "^term2str tm^";");
    in
      if count = 0 then
        ()
      else
        (out ("");
         out ("(* The monomorphic constant"^pluraliss count^
              " used on any left-hand side: *)");
         #map const_base print1)
    end;

  fun output_types () =
    let
      val count = #get_count type_base ()
      fun print1 (ty,n) =
        out ("val type"^int2str n^" = ==`:"^type_to_string ty^"`==;");
    in
      if count = 0 then
        ()
      else
        (out ("");
         out ("(* The polymorphic type"^pluraliss count^
              " used on any left-hand side for any variable: *)");
         #map type_base print1)
    end;
  (* -------------------------------------------------------------- *)
  fun output_check_thms thms =
    let
      val thm_count = ref 0;
      fun make_eq thm =
        let
          fun cook thm =
            let
              val thm = SPEC_ALL thm
              val t = concl thm
            in
              if is_eq t then
                [thm]
              else if is_conj t then
                (op @ o (cook##cook) o CONJ_PAIR) thm
              else if is_neg t then [EQF_INTRO thm] else [EQT_INTRO thm]
            end
        in
          map (fn thm=>GENL (free_vars (concl thm)) thm) (cook thm)
        end;

      val thms' = map (fn (thm,txt) => (thm,txt,make_eq thm)) thms;

      fun check_eq1 (thm,_,thms) = [thm] = thms;

      fun check1 (x as (thm,txt,thms)) =
        let
          val _ = thm_count := !thm_count + 1;
          val name = "thm_" ^ int2str (!thm_count);
          fun name1 n = name^"_"^int2str n;
          fun namelist [] n = raise Crash
            | namelist [_] n = name1 n
            | namelist (x::x'::xs) n = name1 n ^ "," ^ namelist (x'::xs) (n+1)
          fun results [] n = []
            | results (x::xs) n = (x,name1 n)::(results xs (n+1));
        in
          out ("val "^name^" = check ("^txt^") ("^term2str (concl thm)^")");
          if check_eq1 x then
            [(thm,name)]
          else
            (out ("val ["^namelist thms 1^"] = make_eq "^name^";");
             results thms 1)
        end;
    in
      out ("");
      out (pluralis ("(* We check that the theorem is the right one: *)",
                     "(* We check that the theorems are the right ones: *)",
                     length thms));
      out ("fun check thm tm =");
      out ("  if concl thm=tm then");
      out ("    thm");
      out ("  else");
      out ("    raise HOL_ERR {message = \"Environment changed\",");
      out ("                   origin_function = \"\",");
      out ("                   origin_structure = \"top level\"};");
      if all check_eq1 thms' then
        ()
      else
        (out ("");
         out ("(* Handle conjuncts and other such stuff: *)");
         out ("fun make_eq thm =");
         out ("  let");
         out ("    fun cook thm =");
         out ("      let");
         out ("        val thm = SPEC_ALL thm");
         out ("        val t = concl thm");
         out ("      in");
         out ("        if is_eq t then");
         out ("          [thm]");
         out ("        else if is_conj t then");
         out ("          (op @ o (cook##cook) o CONJ_PAIR) thm");
         out ("        else if is_neg t then [EQF_INTRO thm] else [EQT_INTRO thm]");
         out ("      end");
         out ("  in");
         out ("    map (fn thm=>GENL (free_vars (concl thm)) thm) (cook thm)");
         out ("  end;");
         out ("");
         out ("(* It is OK for the `val [...] = ...' bindings below not to be exhaustive. *)"));
      concat (map check1 thms')
    end;

  (* Datatype to monitor the progress of mathcing of universially bound vars *)
  datatype Progress =
    Unmatched of term        (* Unmatched until now. *)
  | Matched of string*term;  (* Matched against variable named STRING.  *)

  fun initstate (thm,txt) =
    let
      val (vars,main) = strip_forall (concl thm)
    in
      ([("tm",lhs main)],(map Unmatched vars,txt))
    end;

  val Cname = #Name o dest_const;

  fun go [] = out ("raise bad")
    | go [([],(vars,thmtxt))] =
      let
        fun spectext [] txt = txt
          | spectext (Matched (name,tm)::rest) txt =
            let
              val ty = type_of tm
              val inner =
                if rest=nil then
                  txt
                else
                  "("^spectext rest txt^")";
            in
              if polymorphic ty then
                "SPECT "^name^" "^inner^" "^type_name ty
              else
                "SPEC "^name^" "^inner
            end
          | spectext (Unmatched tm::rest) txt =
            (fishy ("In theorem "^txt^
                    " the variable "^term2str tm^" was not matched");
             raise Crash);
      in
        out (spectext (rev vars) thmtxt)
      end
    | go ((x as ([],(vars,thmtxt)))::_) =
      (fishy "Two (or more) theorems matched at once -- duplication?";
       go [x])
    | go (xs as ((name,tm)::_,_)::_) =
      let
        fun const_case xs =
          let
            fun fix (list,goo) = (tl list,goo);
            val (good,bad)=split
              (fn x=>
               let val tm'=snd (hd (fst x)) in
                 is_const tm' andalso Cname tm=Cname tm' end) xs;
            val ty = type_of tm;
          in
            (* We cannot match using "=" when different (or polymorphic) *)
            (* types are around.  In such cases, we match on the name.   *)
            if (polymorphic ty orelse
                not (all (fn xs=>type_of (snd (hd (fst xs)))=ty) xs)) then
              out ("if match_const "^name^" "^quote (Cname tm)^" then")
            else
              out ("if "^name^"="^const_name tm^" then");
            movein ();
            go (map fix good);
            moveout ();
            out ("else");
            movein ();
            go bad;
            moveout ()
          end;

        fun comb_case xs =
          let
            fun fix ((name,tm)::rest,goo) =
              let
                val {Rator,Rand} = dest_comb tm
              in
                ((name^"1",Rator)::(name^"2",Rand)::rest,goo)
              end
              | fix _ = (fishy "Strange value in comb_case.fix";
                         raise Crash);

            val (good,bad) = split (is_comb o snd o hd o fst) xs;
            val letbind = "let val {Rator="^name^"1,Rand="^name^
              "2}=dest_comb "^name^" in";
          in
            if agressive_comb andalso bad=[] then
              (out letbind;
               movein ();
               go (map fix good);
               moveout ();
               out ("end"))
            else
              (out ("if is_comb "^name^" then");
               movein ();
               out letbind;
               movein ();
               go (map fix good);
               moveout ();
               out ("end");
               moveout ();
               out ("else");
               movein ();
               go bad;
               moveout ())
          end;

        fun var_case xs =
          let
            datatype linearity = LINEAR | NONLINEAR of string;

            fun linear ((name,tm)::rest,(vars,_)) =
              let
                fun check [] = LINEAR
                  | check (Unmatched tm'::rest) = check rest
                  | check (Matched (name,tm')::rest) =
                    if tm=tm' then NONLINEAR name else check rest
              in
                check vars
              end
              | linear _ = (fishy "Strange value in var_case.linear";
                            raise Crash);

            fun fix ((name,tm)::rest,(vars,thmtxt)) =
              let
                fun fix1 (x as (Unmatched tm')) =
                  if tm=tm' then
                    Matched (name,tm)
                  else
                    x
                  | fix1 x = x
              in
                (rest,(map fix1 vars,thmtxt))
              end
              | fix _ = (fishy "Strange value in var_case.fix";
                         raise Crash);

            val lin1 = linear (hd xs)
            val (good,bad) =
              split (fn x=>is_var (snd (hd (fst x))) andalso lin1=linear x) xs;
          in
            if bad<>[] then
              (out ("(");
               movein ())
            else
              ();
            case lin1 of
              LINEAR => go (map fix good)
            | NONLINEAR n => (out ("if "^n^"="^name^" then");
                              movein ();
                              go (map fix good);
                              moveout ();
                              out ("else");
                              movein ();
                              out ("raise bad");
                              moveout ());
            if bad<>[] then
              (moveout ();
               out (") handle HOL_ERR _ =>");
               movein ();
               go bad;
               moveout ())
            else
              ()
          end;

        fun abs_case xs =
          let
            fun fix ((name,tm)::rest,goo) = ((name^"1",body tm)::rest,goo)
              | fix _ = (fishy "Strange value in abs_case.fix";
                         raise Crash);

            val (good,bad) = split (is_abs o snd o hd o fst) xs;
            val letbind = "let val "^name^"1=body "^name^" in";
          in
            out ("if is_abs "^name^" then");
            movein ();
            out letbind;
            movein ();
            go (map fix good);
            moveout ();
            out ("end");
            moveout ();
            out ("else");
            movein ();
            go bad;
            moveout ()
          end;
      in
        if is_const tm then
          const_case xs
        else if is_comb tm then
          comb_case xs
        else if is_var tm then
          var_case xs
        else
          abs_case xs
      end

in
  fun conversion_generator file_name func_name thms =
    let
      val save_Global_linewidth = !Globals.linewidth;
      val save_Globals_max_print_depth = !Globals.max_print_depth;
      val _ = null_device := open_out "/dev/null";
      val _ = outfile := open_out file_name;

      fun cleanup () =
        (close_out (!outfile);
         close_out (!null_device);
         Globals.linewidth := save_Global_linewidth;
         Globals.max_print_depth := save_Globals_max_print_depth);
    in
      let
        (* Say hello to the user.  Making strings span more than one line
           tends to screw up the stupid Emacs sml-mode that I have.  *)
        fun welcome () =
          let
            val thmcount = length thms
          in
            output
            (std_out,
             "--------------------------------------------------------------"^
             "----------------\nHi, I'm the "^program_name^" version "^
             program_version^"!\n\n"^
             "I will now generate a file called \""^file_name^
             "\" containing the source code\n"^
             "for a rewriting conversion corresponding to the "^
             pluralis ("theorem",int2str thmcount^" theorems",thmcount)^
             " you gave me.\n"^
             "The name of the conversion will be \""^func_name^"\".\n\n"^
             "If you put conversions generated this way to any serious use, "^
             "you should\n"^
             "mail Morten Welinder (terra@diku.dk) and tell him; that might "^
             "cheer him up.\n"^
             "--------------------------------------------------------------"^
             "----------------\n")
          end;
      in
        welcome ();

        (* Set up pretty-printing. *)
        Globals.linewidth := 1000;
        Globals.max_print_depth := 1000000;
        indent := 0;

        out ("(* ------------------------------------------------------------------------ *)");
        out ("(* The following code is machine generated.  For this reason it is not wise *)");
        out ("(* to edit it by hand.  The main function is a conversion that rewrites     *)");
        out ("(* left-to-right with respect to one of the theorems below.                 *)");
        out ("(*                                                                          *)");
        out ("(* The code was generated by "^
             program_name^" version "^
             program_version^".          *)");
        out ("");
        out ("(* Make sure the conversion is compiled properly: *)");
        out ("val save_System_Control_interp = !System.Control.interp;");
        out ("val _ = System.Control.interp := false;");
        out ("");
        out ("local");
        movein ();
        if agressive_comb then
          out ("(* This or another HOL_ERR exception will be raised if no theorem matches: *)")
        else
          out ("(* This exception will be raised if no theorem matches: *)");
        out ("val bad = HOL_ERR {message = \"No matching theorem\",");
        out ("                   origin_function = \"" ^ func_name ^ "\",");
        out ("                   origin_structure = \"top level\"};");
        out ("");
        out ("(* Utility functions: *)");
        out ("fun match_const tm name = name = #Name (dest_const tm) handle _ => false;");
        out ("fun SPECT tm thm ty = SPEC tm (INST_TYPE (match_type ty (type_of tm)) thm);");
        let
          val thms = output_check_thms thms;
        in
          map walk_term (map (lhs o #2 o strip_forall o concl o #1) thms);
          output_constants ();
          output_types ();
          moveout ();
          out ("in");
          movein ();
          out ("val "^func_name^":conv = fn tm=>");
          movein ();
          go (map initstate thms);
          moveout ();
          moveout ();
          out ("end;");
          out ("val _ = System.Control.interp := save_System_Control_interp;")
        end;
        out ("");
        out ("(* Machine generated code ends here.                                        *)");
        out ("(* ------------------------------------------------------------------------ *)");
        cleanup ()
      end handle x=>
        (cleanup (); raise x)
    end;

  val convgen = conversion_generator "temp.sml" "conv";
end;

val _ = System.Print.say
  ("\nUsage: conversion_generator file_name func_name [(thm,\"thm\"),...]"^
   "\nor     convgen [(thm,\"thm\"),...]\n\n");
(* ----------------------------------------------------------------------- *)
(*
fun why f x = (f x; raise HOL_ERR {message = "No reason why.",
                                   origin_function = "why",
                                   origin_structure = ""})
  handle HOL_ERR x=>x;
*)
(* ----------------------------------------------------------------------- *)
(*
convgen [(REFL_CLAUSE,"REFL_CLAUSE"),
         (EQ_CLAUSES,"EQ_CLAUSES"),
         (NOT_CLAUSES,"NOT_CLAUSES"),
         (AND_CLAUSES,"AND_CLAUSES"),
         (OR_CLAUSES,"OR_CLAUSES"),
         (IMP_CLAUSES,"IMP_CLAUSES"),
         (COND_CLAUSES,"COND_CLAUSES"),
         (FORALL_SIMP,"FORALL_SIMP"),
         (EXISTS_SIMP,"EXISTS_SIMP"),
         (ABS_SIMP,"ABS_SIMP")];
*)
(* ----------------------------------------------------------------------- *)
