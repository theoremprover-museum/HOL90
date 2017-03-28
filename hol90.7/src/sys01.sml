(* infix 9 sub; *)
(* open Array; *)
val length = List.length;

(* sml/nj 93
 * System.Control.Print.printLength := 1000;
 * System.Control.Print.printDepth := 350;
 * System.Control.Print.stringDepth := 250;
 * System.Control.Print.pathnames := 2;
 * System.Control.quotation := true;
 *********************************************************)

(* sml/nj 102
 * Compiler.Control.Print.printLength := 1000;
 * Compiler.Control.Print.printDepth := 350;
 * Compiler.Control.Print.stringDepth := 250;
 * (* Compiler.Control.Print.pathnames := 2;*)
 * Compiler.Control.quotation := true;
 **********************************************************)

System.Control.Print.printLength := 1000;
System.Control.Print.printDepth := 350;
System.Control.Print.stringDepth := 250;
System.Control.Print.pathnames := 2;
System.Control.quotation := true;

use "0/sys_params.sig";
use "0/sys_params.sml";
structure Sys_params = SYS_PARAMS ();

use "0/globals.sig";
use "0/globals.sml";
structure Globals = GLOBALS(structure Sys_params = Sys_params);

use "0/exception.sig";
use "0/exception.sml";
structure Exception = EXCEPTION(structure Globals = Globals)
open Exception;

(* sml/nj 93 fun use file = System.Compile.use file handle e => Raise e; *)
(* sml/nj 102 fun use file = Compiler.Interact.use_file file 
 *                           handle e => Raise e; 
 ****************************************************************************)
fun use file = System.Compile.use file handle e => Raise e;

use "0/lib.sig";
use "0/lib.sml";
structure Lib = LIB(Exception)
open Lib;
infix 3 ##;
infix 5 |->;

use "0/uid.sig";
use "0/uid.sml";

use "0/file.sig";
use "0/file.sml";
structure File = FILE(Lib);

use "0/help.sig";
use "0/help.sml";
structure Help = HELP(structure Globals = Globals); 
open Help;

use "0/save_hol.sig";
use "0/save_hol.sml";

use "0/pp.sig";
use "0/pp.sml";

use "0/lexis.sig";
use "0/lexis.sml";

use "0/type.sig";
use "0/type.sml";

use "0/term.sig";
use "0/term.sml";

use "0/match.sig";
use "0/match.sml";

use "0/dsyntax.sig";
use "0/dsyntax.sml";

(* use "0/hol_pp.sig"; *)
(* use "0/hol_pp.sml"; *)

use "0/hol_pp.extensible.sig";
use "0/hol_pp.extensible.sml";

use "0/preterm.sig";
use "0/preterm.sml";

use "0/parse_support.sig";
use "0/parse_support.sml";

(****************************************************************
 * Make the standard HOL parse. Needs to call these shell scripts, due
 * to fact that ML-Yacc doesn't understand quote/antiquote. That also
 * explains why base.qaq.sml is a doctored version of base.sml in ML-Yacc.
 *
 * fun mk_hol_parser hol_root_dir lex_file yak_file =
 *    let val sig_sed = hol_root_dir^"tools/sig.sed"
 *        val sml_sed = hol_root_dir^"tools/sml.sed"
 *        val yak_sig = yak_file^".sig"
 *        val yak_sml = yak_file^".sml"
 *    in
 *      LexGen.lexGen lex_file; 
 *      ParseGen.parseGen yak_file;
 *      System.system ("sed -f "^sig_sed^" "^yak_sig^" > tmp1");
 *      System.system ("mv tmp1 "^yak_sig);
 *      System.system ("sed -f "^sml_sed^" "^yak_sml^" > tmp1");
 *      System.system ("mv tmp1 "^yak_sml)
 *    end;
 ****************************************************************)
use "0/base.qaq.sml";
use "0/hol_yak.sig";
use "0/hol_yak.sml";
use "0/hol_lex.sml";

(*************************************************************
  (LexGen.lexGen "thy_lex"; ParseGen.parseGen "thy_yak");
 *************************************************************)
use "0/thy_yak.sig";
use "0/thy_yak.sml";
use "0/thy_lex.sml";

use "0/parse.sig";
use "0/parse.sml";

use "0/thm.sig";
use "0/thm.sml";

use "0/net.sig";
use "0/net.sml";

use "0/theory/data.sig";
use "0/theory/data.sml";

use "0/theory/regime.sig";
use "0/theory/regime.sml";

use "0/theory/disk_io.sig";

(* Differs for different representations of theories. *)
(* begin ascii support *)
    use "0/thy_parse.sig";
    use "0/thy_parse.sml";

    use "0/thy_pp.sig";
    use "0/thy_pp.sml";

    use "0/theory/disk_io.ascii.sml";
    (* ************************************************************
      (LexGen.lexGen "thms.lex"; ParseGen.parseGen "thms.yak"; 
       LexGen.lexGen "holsig.lex"; ParseGen.parseGen "holsig.yak");
     * *************************************************************) 
    use "0/theory/thms.yak.sig";
    use "0/theory/thms.yak.sml";
    use "0/theory/thms.lex.sml";

    use "0/theory/holsig.yak.sig";
    use "0/theory/holsig.yak.sml";
    use "0/theory/holsig.lex.sml";

(* end ascii support *)

(* binary support :*)
(* use "0/theory/disk_io.binary.sml"; *)

use "0/theory/io.sig";
use "0/theory/io.sml";

use "0/cache.sml";
use "0/theory/cache.sig";

use "0/theory/graph.sig";
use "0/theory/graph.sml";

use "0/theory/ops.sig";
use "0/theory/ops.sml";

use "0/theory/theory.sig";
use "0/theory/theory.sml";

use "0/theory/add_to_sml.sig";
use "0/theory/add_to_sml.sml";

use "0/library/lib_data.sig";
use "0/library/lib_data.sml";

(*************************************************************
   (LexGen.lexGen "lib.lex"; ParseGen.parseGen "lib.yak");
 ***************************************************************) 
use "0/library/lib.yak.sig";
use "0/library/lib.yak.sml";
use "0/library/lib.lex.sml";

use "0/library/lib_io.sig";
use "0/library/lib_io.sml";

use "0/library/lib.sig"; 
use "0/library/lib.sml"; 

use "0/install.sig";
use "0/install.sml";

use "0/exists_def.sig";
use "0/exists_def.sml";

(* Begin POD *)

(* Constant specification *)
use "0/const_spec.sig";
use "0/const_spec.sml";

(* Type definition *)
use "0/type_def.sig";
use "0/type_def.sml";

(* Constant definition *)
use "0/const_def.sig";
use "0/const_def.sml";

(* End PoD *)


(* Make theories essential to the base logic *)
val _ = if Globals.remake_theory_files
        then Lib.clean_directory 
                ((!Globals.HOLdir)^"theories/"^Globals.theory_file_type)
	else ();

local fun theory file = (!Globals.HOLdir)^"theories/src/"^file
in
val _ = use (theory "mk_min.sig");
val _ = use (theory "mk_min.sml");

val _ = use (theory "mk_exists.sig");
val _ = use (theory "mk_exists.sml");

val _ = use (theory "mk_bool.sig");
end;


use "0/base_logic.sig";
use "0/term_io.sig";

local
structure Save_hol = SAVE_HOL(Globals)
structure Lexis = LEXIS(Globals)
structure Type = TYPE(Lexis)
structure Term = TERM(structure Type = Type
                      structure Lexis = Lexis)
structure Match = MATCH(Term)
structure Dsyntax = DSYNTAX(structure Match = Match
                            structure Term = Term
                            structure Lexis = Lexis)
structure Hol_pp = HOL_PP(structure Lexis = Lexis
                          structure Dsyntax = Dsyntax
                          structure Term = Term
                          structure Globals = Globals)
structure Preterm = PRETERM(structure Dsyntax = Dsyntax
                            structure Term = Term
                            structure Hol_pp = Hol_pp)
structure Parse_support = PARSE_SUPPORT(structure Lexis = Lexis
                                        structure Preterm = Preterm
                                        structure Dsyntax = Dsyntax)
structure Table = holLrValsFun(structure Token = LrParser.Token
                               structure Parse_support = Parse_support)
structure Lex = HOL_LEX(structure Tokens=Table.Tokens
                        structure Parse_support=Parse_support)
structure Parse = PARSE
               (structure Parse_support = Parse_support
                structure P=JoinWithArg(structure ParserData=Table.ParserData
                                        structure Lex=Lex
                                        structure LrParser = LrParser))
structure Thm = THM(structure Dsyntax = Dsyntax
                    structure Hol_pp = Hol_pp
                    structure Globals = Globals
                    structure Term = Term)

structure Theory_data = THEORY_DATA(structure Thm = Thm
                                    structure Hol_pp = Hol_pp
                                    structure Globals = Globals)
(* Binary theory representations: *)
(* structure Disk_io = DISK_IO_BINARY(REGIME(Theory_data)) *)

(* Ascii theory representations *)
local
structure Thy_pp = THY_PP(structure Term = Term
                          structure Hol_pp = Hol_pp)
structure Thy_table = thyLrValsFun(structure Token = LrParser.Token
                                   structure Term = Term)
structure Thy_parse = THY_PARSE(structure Term = Term
                                structure P = Join
                                 (structure ParserData = Thy_table.ParserData
                                  structure Lex = THY_LEX
                                        (structure Tokens = Thy_table.Tokens)
                                  structure LrParser = LrParser))
structure Table1 = thmsLrValsFun(structure Token = LrParser.Token
                                 structure Thm = Thm
                                 structure Thy_parse = Thy_parse
                                 structure Theory_data = Theory_data)

structure Table2 = holsigLrValsFun(structure Token = LrParser.Token
                                   structure Theory_data = Theory_data
                                   structure Term = Term)
in
structure Disk_io = 
          DISK_IO_ASCII(structure Regime = REGIME(Theory_data)
                        structure Thy_pp = Thy_pp
                        structure Thms_parse = 
                             Join(structure ParserData = Table1.ParserData
                                  structure Lex = 
                                      THMS_LEX(structure Tokens=Table1.Tokens)
                                  structure LrParser = LrParser)
                        structure Holsig_parse =
                             Join(structure ParserData = Table2.ParserData
                                  structure Lex = 
                                     HOLSIG_LEX(structure Tokens=Table2.Tokens)
                                  structure LrParser = LrParser))
end


structure Theory_cache : Theory_cache_sig = 
     CACHE(type object = Theory_data.theory
           type key = string
           val key_of = Theory_data.theory_id_name o Theory_data.theory_id)  
structure Theory_graph :Theory_graph_sig = 
          DAG(type node_id = Theory_data.theory_id
              val node_name = Theory_data.theory_id_name
              val node_eq = Lib.curry Theory_data.theory_id_eq)
structure Theory_io = THEORY_IO(structure Disk_io = Disk_io
                                structure File = File)
structure Theory_ops = THEORY_OPS(structure Globals = Globals
                                  structure Term = Term
                                  structure Theory_data = Theory_data
                                  structure Theory_io=Theory_io
                                  structure Theory_cache=Theory_cache
                                  structure Theory_graph=Theory_graph)
structure Theory = THEORY(structure Thm = Thm
                          structure Term = Term
                          structure Globals = Globals
                          structure Hol_pp = Hol_pp
                          structure Theory_ops = Theory_ops
                          structure Lexis = Lexis)

structure Add_to_sml = ADD_TO_SML (structure Theory = Theory
                                   structure Lexis  = Lexis)
structure Lib_table = libLrValsFun(structure Token = LrParser.Token
                                   structure Lib_data = Lib_data)

structure Lib_parse = 
              Join(structure ParserData = Lib_table.ParserData
                   structure Lex = LIB_LEX(structure Tokens = Lib_table.Tokens)
                   structure LrParser = LrParser)

structure Lib_io = LIB_IO(structure Lib_parse = Lib_parse
                          structure Lib_data = Lib_data)

structure Library = LIBRARY(structure Theory = Theory
                            structure Lib_io = Lib_io)
structure Install = INSTALL (structure Globals = Globals
		             structure Theory = Theory
		             structure Add_to_sml = Add_to_sml
                             structure Library = Library)

structure Exists_def = EXISTS_DEF(structure Theory = Theory
                                  structure Dsyntax = Dsyntax)

structure Net = NET(Term)

in
  structure Base_logic : Base_logic_sig =
  struct
     structure Save_hol = Save_hol
     structure Lexis = Lexis
     structure Type :Public_type_sig = Type
     structure Term :Public_term_sig = Term
     structure Preterm = Preterm
     structure Match = Match
     structure Dsyntax = Dsyntax
     structure Net = Net
     structure Thm = Thm
     structure Theory = Theory
     structure Add_to_sml = Add_to_sml
     structure Install = Install
     structure Library = Library
     structure Const_spec = CONST_SPEC(structure Theory = Theory
                                       structure Dsyntax = Dsyntax
                                       structure Lexis = Lexis)
     structure Type_def = TYPE_DEF(structure Theory = Theory
                                   structure Dsyntax = Dsyntax)
     structure Const_def = CONST_DEF(structure Theory = Theory
                                     structure Dsyntax = Dsyntax
                                     structure Lexis = Lexis
                                     structure Const_spec = Const_spec)
     structure Min = MK_MIN(structure Globals = Globals
                            structure Theory = Theory
                            structure Dsyntax = Dsyntax
                            structure Parse = Parse)
     structure Exists = MK_EXISTS(structure Globals = Globals
                                  structure Theory = Theory
                                  structure Exists_def = Exists_def
                                  structure Parse = Parse)
  end

  structure Term_io : Term_io_sig = 
  struct
     structure Parse = Parse
     structure Parse_support = Parse.Parse_support
     structure Hol_pp = Hol_pp
  end
end;

open Base_logic;

if Globals.remake_theory_files
then use ((!Globals.HOLdir)^"theories/src/mk_bool.sml")
else
  Base_logic.Add_to_sml.add_theory_structure_to_sml
     {structure_name = "Bool", theory_name = "bool"};


(*Argghh! T_DEF is stored in the theory as TRUTH *)
structure Bool:Mk_bool_sig =
    struct
	type thm = Base_logic.Thm.thm
	open Bool
	val T_DEF = Base_logic.Theory.definition "bool" "TRUTH"
    end;


(* Install prettyprinters for types, terms, and library descriptions. *)
local
fun top_pp_thm ppstrm th =  
   ( PP.begin_block ppstrm PP.CONSISTENT 0;
     Base_logic.Thm.pp_thm ppstrm th; 
     PP.end_block ppstrm)
in
val _ = PP.install_pp ["Base_logic","Thm","thm"] top_pp_thm
end;

val _ = PP.install_pp ["Base_logic","Type","hol_type"] 
                      Term_io.Hol_pp.pp_self_parsing_type;
val _ = PP.install_pp ["Base_logic","Term","term"] 
                      Term_io.Hol_pp.pp_self_parsing_term;
val _ = PP.install_pp ["Base_logic","Library","lib"] 
                      Base_logic.Library.pp_library;


local
open Thm
open Term
in
  type conv = term -> thm
  type goal = term list * term
  type validation = thm list -> thm
  type tactic = goal -> goal list * validation;
  type thm_tactic = thm -> tactic
  type thm_tactical = thm_tactic -> thm_tactic;
end;


(* This is for garbage collection and security *)

structure EMPTY = struct end;
functor GLOBALS() = EMPTY;
functor EXCEPTION() = EMPTY;
functor LIB() = EMPTY;
functor FILE() = EMPTY;
functor HELP() = EMPTY;
functor SAVE_HOL() = EMPTY;
functor LEXIS() = EMPTY;
functor TYPE() = EMPTY;
functor TERM() = EMPTY;
functor MATCH() = EMPTY;
functor SYMTAB() = EMPTY;
functor DSYNTAX() = EMPTY;
functor HOL_PP() = EMPTY;
functor PRETERM() = EMPTY;
functor PARSE_SUPPORT() = EMPTY;
functor HOL_LEX() = EMPTY;
functor THM() = EMPTY;
functor THEORY_DATA() = EMPTY;
functor THY_PP() = EMPTY;
functor THY_PARSE() = EMPTY;
functor DISK_IO_ASCII() = EMPTY;
functor CACHE() = EMPTY;
functor DAG() = EMPTY;
functor THEORY_IO() = EMPTY;
functor THEORY_OPS() = EMPTY;
functor THEORY() = EMPTY;
functor ADD_TO_SML() = EMPTY;
functor LIB_IO() = EMPTY;
functor LIBRARY() = EMPTY;
functor EXISTS_DEF() = EMPTY;


signature EMPTY = sig end
signature Type_sig = EMPTY
signature Term_sig = EMPTY
signature Symtab_sig = EMPTY
signature Dsyntax_sig = EMPTY;

val prim_hol_lib =
   if Globals.remake_theory_files
   then Library.new_library
         {name = "PRIM_HOL",
          doc = "Derived rules and such. Preloaded", 
          path = !Globals.HOLdir,
          parents = [],
          theories = [], (* ought to be "bool" in long run *)
          code = ["1/drule.sig", "1/drule.sml",
                  "1/conv.sig", "1/conv.sml",
                  "1/tactical.sig", "1/tactical.sml",
                  "1/rewrite.sig", "1/rewrite.sml",
                  "1/thm_cont.sig", "1/thm_cont.sml",
                  "1/tactic.sig", "1/tactic.sml",
                  "1/taut_thms.sig", "1/taut_thms.sml",
                  "1/resolve.sig", "1/resolve.sml",
                  "1/type_def_support.sig", "1/type_def_support.sml",
                  "1/induct_then.sig", "1/induct_then.sml",
                  "1/prim_rec.sig", "1/prim_rec.sml",
                  "1/hol1.sml"],
          help = [],
          loaded = "fn() => \
                   \  (Globals.interp := true;    \
                   \   PP.install_pp [\"Rewrite\",\"rewrites\"] \
                   \                 Rewrite.pp_rewrites; \
                   \   Save_hol.save_hol\"hol90.01\")"}
   else let val ph_lib = Library.find_library "PRIM_HOL"
        in Library.move_library(ph_lib, !Globals.HOLdir);
           ph_lib
        end;

Library.load_library_in_place prim_hol_lib;
