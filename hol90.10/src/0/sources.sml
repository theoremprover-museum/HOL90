use "SysParams.sml";
use "portableML/njsml.109.32.sml";
(* use "portableML/njsml.109.xx.sml"; *)
use "0/globals.sig";
use "0/globals.sml";
use "0/exception.sig";
use "0/exception.sml";
use "quote-filter/filter.sml";
use "0/lib.sig";
use "0/lib.sml";
open Lib;
use "0/file.sig";
use "0/file.sml";
use "0/help.sig";
use "0/help.sml";
use "0/save_hol.sig";
use "0/save_hol.sml";
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
use "0/pp.sig"; use "0/pp.sml";
use "0/hol_pp.extensible.sig";
use "0/hol_pp.extensible.sml";
use "0/thm.sig";
use "0/thm.sml";
use "0/preterm.sig";
use "0/preterm.sml";
(* Use underlying support for ML-Yacc parsers *)
use "Grammars/ParseBase/base.sig";
use "Grammars/ParseBase/join.sml";
use "Grammars/ParseBase/lrtable.sml";
use "Grammars/ParseBase/stream.sml";
use "Grammars/ParseBase/parser1.sml";
use "0/uid.sig";
use "0/uid.sml";
use "0/theory/data.sig";
use "0/theory/data.sml";
use "0/theory/thy_pp.sig";
use "0/theory/thy_pp.sml";
use "Grammars/thy.yak.sig";
use "Grammars/thy.yak.sml";
use "0/theory/thy_parse.sig";
use (case SysParams.MLdialect 
     of SysParams.NinetySeven => "0/theory/thy_parse.sml"
      | SysParams.Ninety      => "0/theory/thy_parse.90.sml");
use "Grammars/thy.lex.sml";
use "Grammars/thms.yak.sig";
use "Grammars/thms.yak.sml";
use "Grammars/holsig.yak.sig";
use "Grammars/holsig.yak.sml";
use "0/theory/regime.sig";
use "0/theory/disk_io.sig";
use (case SysParams.MLdialect 
     of SysParams.NinetySeven => "0/theory/disk_io.ascii.sml"
      | SysParams.Ninety      => "0/theory/disk_io.ascii.sml");
use "0/theory/regime.sml";
use "Grammars/thms.lex.sml";
use "Grammars/holsig.lex.sml";
use "0/cache.sml";
use "0/theory/cache.sig";
use "0/theory/graph.sml";
use "0/theory/graph.sig";
use "0/theory/io.sig";
use "0/theory/io.sml";
use "0/theory/ops.sig";
use (case SysParams.MLdialect 
     of SysParams.NinetySeven => "0/theory/ops.sml"
      | SysParams.Ninety      => "0/theory/ops.90.sml");
use "0/theory/theory.sig";
use (case SysParams.MLdialect 
     of SysParams.NinetySeven => "0/theory/theory.sml"
      | SysParams.Ninety      => "0/theory/theory.90.sml");
use "0/net.sig";
use "0/net.sml";
use "0/library/lib_data.sig";
use "0/library/lib_data.sml";
use "Grammars/lib.yak.sig";
use "Grammars/lib.yak.sml";
use "Grammars/lib.lex.sml";
use "0/library/lib_io.sig";
use (case SysParams.MLdialect 
     of SysParams.NinetySeven => "0/library/lib_io.sml"
      | SysParams.Ninety      => "0/library/lib_io.90.sml");
use "0/library/lib.sig";
use "0/library/lib.sml";

use "0/exists_def.sig";
use "0/exists_def.sml";
use "0/const_spec.sig";
use "0/const_spec.sml";
use "0/type_def.sig";
use "0/type_def.sml";
use "0/const_def.sig";
use "0/const_def.sml";
use"0/CoreHol.sig";
use"0/CoreHol.sml";


(* Once Term exists, we can build the parser; otherwise, functor madness! *)
use "0/parse_support.sig";
use "0/parse_support.sml";
use "Grammars/hol.yak.sig";
use "Grammars/hol.yak.sml";
use (case SysParams.MLdialect 
     of SysParams.NinetySeven => "Grammars/hol.lex.sml"
      | SysParams.Ninety      => "Grammars/hol.lex.90.sml");
use "0/parse.sig";
use "0/parse.sml";

local 
  structure Lib_table = libLrValsFun(structure Token = LrParser.Token
                                     structure Lib_data = Lib_data)
  structure Lib_parse = Join
       (structure ParserData = Lib_table.ParserData
        structure Lex = LIB_LEX(structure Tokens = Lib_table.Tokens)
        structure LrParser = LrParser)
  structure Lib_io = LIB_IO(structure File = File
                            structure Lib_parse = Lib_parse
                            structure Lib_data = Lib_data)
in
structure Library = LIBRARY(structure Help = Help
                            structure Theory = CoreHol.Theory
                            structure Lib_io = Lib_io)
end;

use "0/theory/add_to_sml.sig";
use "0/theory/add_to_sml.sml";
use "0/install.sig";
use "0/install.sml";

structure Abbrev =
struct
   local
      open CoreHol.Thm
      open CoreHol.Term
   in
      type conv = term -> thm
      type goal = (term list * term)
      type validation = thm list -> thm
      type tactic_result = goal list * validation;
      type tactic = goal -> tactic_result;
      type thm_tactic = thm -> tactic
      type thm_tactical = thm_tactic -> thm_tactic;
   end;
end;
