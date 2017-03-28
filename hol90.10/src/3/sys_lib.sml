structure Sys_lib :Sys_lib_sig =
struct

type lib = Library.lib;

open Library;

(*----------------------------------------------------------------------------
   Taken out by DRS for the time being, as these are being managed
   by CM.

val prim_hol_lib = prim_hol_lib
val basic_hol_lib = basic_hol_lib


val hol_lib =
   (* if Globals.remake_theory_files *)
   (* then *)Library.new_library
        {name = "HOL",
         doc ="Arithmetic, lists, trees, and recursive types. Preloaded.",
         path = !Globals.HOLdir,
         parents = [basic_hol_lib],
         theories = ["HOL"],
         code =  ["3/define_type.sig","3/define_type.sml",
                  "3/gstack.sig",     "3/gstack.sml",
                  "3/psyntax.sig",    "3/rsyntax.sig",
                  "3/psyntax.sml",    "3/rsyntax.sml"],
         help = [],
         loaded = "fn() => \
         \      ((* if Globals.remake_theory_files *) \
         \       then (Globals.theory_path := tl (!Globals.theory_path); \
         \             close_theory(); export_theory()) \
         \       else (); \
         \       Theory.delete_cache(); \
         \       Globals.use_init_file := true; \
         \ PP.install_pp[\"Goalstack\",\"goalstack\"] Goalstack.pp_goalstack; \
         \ PP.install_pp[\"Goalstack\",\"proofs\"] Goalstack.pp_proofs; \
         \       Lib.use_string \"open Goalstack; open Implicit\"; \
         \       Lib.use_string \"open Define_type Sys_lib Rsyntax\"; \
         \       Portable.interp := true; \
         \       Install.install (!Globals.HOLdir); \
         \       Save_hol.save_hol (\"hol90.\"^Portable.arch); \
         \       Portable.store_hol_in_HOLdir := false)"}
   (* else let val hlib = Library.find_library "HOL"
        in Library.move_library(hlib, !Globals.HOLdir);
           hlib
        end; *)
 *---------------------------------------------------------------------------*)
(* Dummy for contrib libraries *)
val hol_lib =
    Library.new_library
        {name = "HOL",
         doc ="Arithmetic, lists, trees, and recursive types. Preloaded.",
         path = !Globals.HOLdir,
         parents = [(* basic_hol_lib *)],
         theories = ["HOL"],
         code =  [],
         help = [],
         loaded = "fn() => ()"};


(* Make some system libraries known *)
fun sys_lib_path s = (!Globals.HOLdir)^"library/"^s^"/"

val lite_lib =
   (* if Globals.remake_theory_files *)
   (* then *)Library.new_library
        {name = "lite",
         doc = "The system library to allow HOL-Lite code to be used in hol90, by Donald Syme",
         path = sys_lib_path "lite",
         parents = [(* hol_lib *)],
         theories = [],
         code = ["Lib.sig","Lib.sml",
                 "Trace.sig", "Trace.sml",
                 "Equal.sig","Equal.sml",
                 "liteLib.sml"],
         help = [],
         loaded = "fn() => ()"}
   (* else Library.find_library "lite"; *)

val ho_match_lib =
   (* if Globals.remake_theory_files *)
   (* then *)Library.new_library
        {name = "ho_match",
         doc = "The system library for higher order matching and rewriting, by John Harrison",
         path = sys_lib_path "ho_match",
         parents = [lite_lib],
         theories = [],
         code = ["Ho_net.sig","Ho_net.sml",
                 "Ho_match.sig","Ho_match.sml",
                 "Rewrite.sig","Rewrite.sml",
                 "Resolve.sig","Resolve.sml",
                 "Theorems.sig","Theorems.sml",
                 "ho_matchLib.sml"],
         help = [],
         loaded = "fn () => ()"}
   (* else Library.find_library "ho_match"; *)

val refute_lib =
   (* if Globals.remake_theory_files *)
   (* then *)Library.new_library
        {name = "refute",
         doc = "The system library to support refutation procedures, by John Harrison",
         path = sys_lib_path "refute",
         parents = [lite_lib,ho_match_lib],
         theories = [],
         code = ["AC.sig","AC.sml", "Canon.sig","Canon.sml", "refuteLib.sml"],
         help = [],
         loaded = "fn() => ()"}
   (* else Library.find_library "refute"; *)

val fol_lib =
   (* if Globals.remake_theory_files *)
   (* then *)Library.new_library
        {name = "fol",
         doc = "The system library of shadow syntax for FOL terms in NNF, by John Harrison",
         path = sys_lib_path "fol",
         parents = [lite_lib],
         theories = [],
         code = ["FOL.sig","FOL.sml",
                 "FOL_HOL.sig","FOL_HOL.sml",
                 "folLib.sml"],
         help = [],
         loaded = "fn() => ()"}
   (* else Library.find_library "fol"; *)

val tab_lib =
   (* if Globals.remake_theory_files *)
   (* then *)Library.new_library
        {name = "tab",
         doc = "The system tableau-based first order theorem prover library, by John Harrison",
         path = sys_lib_path "tab",
         parents = [lite_lib,fol_lib,refute_lib],
         theories = [],
         code = ["tabLib.sig","tabLib.sml"],
         help = [],
         loaded = "fn() => ()"}
   (* else Library.find_library "tab"; *)


val decision_lib =
   (* if Globals.remake_theory_files *)
   (* then *)Library.new_library
        {name = "decision",
         doc = "The system decision procedure library, by Richard Boulton",
         path = sys_lib_path "decision",
         parents = [(* hol_lib *)],
         theories = [],
         code = ["lazy_thm.sig", "lazy_thm.sml",
                 "lazy_rules.sml",
                 "conv.sig", "qconv.sml",
                 "support.sml",
                 "norm_convs.sml",
                 "norm_bool.sml",
                 "decide.sml",
                 "type_info.sml",
                 "congruence.sml",
                 "cong_pairs.sml",
                 "cong_types.sml",
                 "arith/theorems.sig", "arith/theorems.sml",
                 "arith/thm_convs.sig", "arith/thm_convs.sml",
                 "arith/arith_cons.sig", "arith/arith_cons.sml",
                 "arith/ineq_coeffs.sig",
                 (case SysParams.MLdialect
                    of SysParams.NinetySeven => "arith/ineq_coeffs.sml"
                     | SysParams.Ninety      => "arith/ineq_coeffs.90.sml"),
                 "arith/arith.sig",
                 (case SysParams.MLdialect
                    of SysParams.NinetySeven => "arith/arith.sml"
                     | SysParams.Ninety      => "arith/arith.90.sml"),
                 "taut.sig", "taut.sml",
                 "num.sml",
                 "prop.sml",
                 "pair.sml",
                 "types.sml",
                 "uninterp.sml",
                 "user.sml",
                 "decisionLib.sml"],
         help = [],
         loaded = "fn () => ()"}
    (* else Library.find_library "decision"; *)

val reduce_lib =
   (* if Globals.remake_theory_files *)
   (* then *)Library.new_library
        {name = "reduce",
         doc = "The system library for normalizing {bool,num} terms, by John Harrison",
         path = sys_lib_path "reduce",
         parents = [(* hol_lib *)],
         theories = [],
         code = ["dest.sig","dest.sml",
                 "boolconv.sig","boolconv.sml",
                 "arithconv.sig","arithconv.sml",
                 "redconv.sig","redconv.sml",
                 "reduceLib.sml"],
         help = ["entries/"],
         loaded = "fn() => ()"}
   (* else Library.find_library "reduce"; *)

val arith_lib =
   (* if Globals.remake_theory_files *)
   (* then *)Library.new_library
        {name = "arith",
         doc = "The system linear arithmetic decision procedure library, by Richard Boulton",
         path = sys_lib_path "arith",
         parents = [reduce_lib],
         theories = [],
         code =["int_extra.sig", "int_extra.sml",
                "arith_cons.sig", "arith_cons.sml",
                "term_coeffs.sig", "term_coeffs.sml",
                "conv.sig", "qconv.sml",
                "theorems.sig", "theorems.sml",
                "thm_convs.sig", "thm_convs.sml",
                "norm_bool.sig", "norm_bool.sml",
                "norm_arith.sig", "norm_arith.sml",
                "norm_ineqs.sig", "norm_ineqs.sml",
                "solve_ineqs.sig", "solve_ineqs.sml",
                "solve.sig", "solve.sml",
                "rationals.sig", "rationals.sml",
                "sup-inf.sig", "sup-inf.sml",
                "streams.sig", "streams.sml",
                "sol_ranges.sig", "sol_ranges.sml",
                "exists_arith.sig", "exists_arith.sml",
                "sub_and_cond.sig", "sub_and_cond.sml",
                "prenex.sig", "prenex.sml",
                "instance.sig", "instance.sml",
                "gen_arith.sig", "gen_arith.sml",
                "arith.sig", "arith.sml",
                "arithLib.sml"],
         help = ["entries/"],
         loaded = "fn() => Lib.use_string \"open arithLib.Arith\""}
    (* else Library.find_library "arith"; *)

val simp_lib =
   (* if Globals.remake_theory_files *)
   (* then *)Library.new_library
        {name = "simp",
         doc = "The system conditional/contextual simplifier library, by Donald Syme",
         path = sys_lib_path "simp",
         parents = [ho_match_lib,refute_lib,arith_lib],
         theories = [],
         code = ["Opening.sig","Opening.sml",
                 "Travrules.sig","Travrules.sml",
                 "Cond_rewr.sig","Cond_rewr.sml",
                 "Traverse.sig","Traverse.sml",
                 "Simplifier.sig","Simplifier.sml",
                 "Unify.sig","Unify.sml",
                 "Sequence.sig","Sequence.sml",
                 "Satisfy.sig","Satisfy.sml",
                 "Unwind.sig","Unwind.sml",
                 "Simpsets.sig","Simpsets.sml",
                 "Termtable.sig","Termtable.sml",
                 "Cache.sig","Cache.sml",
                 "arith_ss.sig","arith_ss.sml",
                 "simpLib.sml"],
         help = [],
         loaded = "fn() => Lib.use_string \"open arith_ss\""}
   (* else Library.find_library "simp"; *)


val ind_def_new_lib =
   (* if Globals.remake_theory_files *)
   (* then *)Library.new_library
        {name = "ind_def_new",
         doc = "The new system inductive definition package, by John Harrison",
         path = sys_lib_path "ind_def_new",
         parents = [lite_lib,ho_match_lib,refute_lib],
         theories = [],
         code = ["IndDef.sig","IndDef.sml"],
         help = [],
         loaded = "fn() => ()"}
   (* else Library.find_library "ind_def_new"; *)

val tfl_lib =
   (* if Globals.remake_theory_files *)
   (* then *)Library.new_library
        {name = "tfl",
         doc = "The system well-founded recursive function definition library, by Konrad Slind",
         path = sys_lib_path "tfl",
         parents = [arith_lib],
         theories = ["WF"],
         code = ["mask.sig", "mask.sml",
                 "utils.sig", "utils.sml",
                 "usyntax.sig", "usyntax.sml",
                 "rw.sig", "rw.sml",
                 "loaded.sml",
                 "thms.sig", "thms.sml",
                 "rules.sig", "rules.sml",
                 "hol_datatype.sig", "hol_datatype.sml",
                 "thry.sig", "thry.sml",
                 "tfl.sig",
                 (case SysParams.MLdialect
                    of SysParams.NinetySeven => "tfl.sml"
                     | SysParams.Ninety      => "tfl.90.sml"),
                 "tflLib.sml"],
         help = [],
         loaded = "fn() => ()"}
    (* else Library.find_library "tfl"; *)

val string_lib =
   (* if Globals.remake_theory_files *)
   (* then *)Library.new_library
         {name = "string",
          doc = "The system string library, by Mike Gordon and Tom Melham",
          path = sys_lib_path "string",
          parents = [(* hol_lib *)],
          theories = ["string"],
          code = ["loaded.sml", "string_conv.sml","ascii_conv.sml",
                  "stringLib.sml"],
          help = [],
          loaded = "fn () => Globals.assert_strings_defined()"}
    (* else Library.find_library "string" *)

val option_lib =
   (* if Globals.remake_theory_files *)
   (* then *)Library.new_library
         {name = "option",
          doc = "The system library for an ML-like option type, by Donald Syme",
          path = sys_lib_path "option",
          parents = [simp_lib],
          theories = ["option"],
          code = ["loaded.sml","optionLib.sml"],
          help = [],
          loaded = "fn () => ()"}
    (* else Library.find_library "option" *)

val num_lib =
   (* if Globals.remake_theory_files *)
   (* then *)Library.new_library
        {name="num",
         doc = "The system library supporting proofs about numbers, due to John Harrison",
         path = sys_lib_path "num",
         parents = [(* hol_lib *)],
         theories = [],
         code = ["numLib.sig","numLib.sml"],
         help = [],
         loaded = "fn() => ()"}
   (* else Library.find_library "num"; *)

val set_lib =
   (* if Globals.remake_theory_files *)
   (* then *)Library.new_library
        {name="set",
         doc = "The system library of sets, due to Tom Melham and P. Leveilley",
         path=sys_lib_path "set",
         parents=[num_lib],
         theories=["set"],
         code=["loaded.sml",
               "gspec.sig","gspec.sml",
               "set_ind.sig","set_ind.sml",
               "fset_conv.sig","fset_conv.sml",
               "setLib.sml"],
         help=["entries/"],
         loaded = "fn() => ()"}
   (* else Library.find_library "set"; *)

val pred_set_lib =
   (* if Globals.remake_theory_files *)
   (* then *)Library.new_library
        {name="pred_set",
         doc = "The library of sets-as-predicates, due to Tom Melham and Ton Kalker",
         path=sys_lib_path "pred_set",
         parents=[num_lib],
         theories=["pred_set"],
         code=["loaded.sml",
               "gspec.sig","gspec.sml",
               "set_ind.sig","set_ind.sml",
               "fset_conv.sig","fset_conv.sml",
               "pred_setLib.sml"],
         help=["entries/"],
         loaded = "fn() => ()"}
   (* else Library.find_library "pred_set"; *)

val unwind_lib =
   (* if Globals.remake_theory_files *)
   (* then *)Library.new_library
        {name="unwind",
         doc = "The system library for unwinding hardware lines, by Richard Boulton",
         path=sys_lib_path "unwind",
         parents = [(* hol_lib *)],
         theories = [],
         code = ["unwindLib.sig","unwindLib.sml"],
         help = ["entries/"],
         loaded = "fn () => ()"}
   (* else Library.find_library"unwind"; *)

val hol88_lib =
   (* if Globals.remake_theory_files *)
   (* then *)Library.new_library
        {name="hol88",
         doc = "A library for compatibility with hol88, by Konrad Slind",
         path=sys_lib_path "hol88",
         parents = [(* hol_lib *)],
         theories = [],
         code = ["compat.sig", "compat.sml", "hol88Lib.sml"],
         help = [],
         loaded = "fn () => ()"}
   (* else Library.find_library "hol88"; *)

val ind_def_lib =
   (* if Globals.remake_theory_files *)
   (* then *)Library.new_library
        {name="ind_def",
         doc = "The system inductive definition package, by Tom Melham",
         path=sys_lib_path "ind_def",
         parents = [hol88_lib],
         theories = [],
         code = ["ind_defLib.sig", "ind_defLib.sml"],
         help = [],
         loaded = "fn () => ()"}
   (* else Library.find_library "ind_def"; *)

val taut_lib =
   (* if Globals.remake_theory_files *)
   (* then *)Library.new_library
        {name="taut",
         doc = "The system tautology checker library, by Richard Boulton",
         path=sys_lib_path "taut",
         parents = [(* hol_lib *)],
         theories = [],
         code = ["tautLib.sig","tautLib.sml"],
         help = ["entries/"],
         loaded = "fn () => ()"}
   (* else Library.find_library "taut"; *)


val meson_lib =
   (* if Globals.remake_theory_files *)
   (* then *)Library.new_library
        {name = "meson",
         doc = "The system MESON model elimination library, by John Harrison",
         path = sys_lib_path "meson",
         parents = [lite_lib, ho_match_lib, refute_lib, fol_lib, taut_lib],
         theories = [],
         code = ["jrhtactics.sml",
                 "canon_port.sig","canon_port.sml",
                  "mesonLib.sig","mesonLib.sml"],
         help = [],
         loaded = "fn() => ()"}
   (* else Library.find_library "meson"; *)

val automate_lib =
   (* if Globals.remake_theory_files *)
   (* then *)Library.new_library
        {name = "automate",
         doc = "The system library for proof automation, by Richard Boulton",
         path = sys_lib_path "automate",
         parents = [ho_match_lib,tab_lib,meson_lib,decision_lib,simp_lib],
         theories = [],
         code = [],
         help = [],
         loaded = "fn() => Lib.use_string \"open Simplifier Theorems " ^
                                            "open arith_ss " ^
(*                                            "open Arith " ^ *)
                                            "open Simpsets " ^
(*                                            "open Ho_rewrite " ^ *)
                                            "open Meson " ^
                                            "open Tab " ^
                                            "open DecisionUser " ^
(*                                            "open Resolve " ^ *)
(*                                            "open Trace " ^ *)
                                            "val arith_ss = hol_ss;\""}
   (* else Library.find_library "automate"; *)
val utils_lib =
   (* if Globals.remake_theory_files *)
   (* then *)Library.new_library
       {name="utils",
        doc = "A library of useful functions, by Elsa Gunter",
        path=sys_lib_path "utils",
        parents = [(* hol_lib *)],
        theories = [],
        code = ["utilsLib.sig","utilsLib.sml"],
        help = [],
        loaded = "fn () => ()"}
   (* else Library.find_library "utils"; *)

val retrieve_lib =
   (* if Globals.remake_theory_files *)
   (* then *)Library.new_library
       {name = "retrieve",
        doc = "Theorem Retrieval Library, by R.J.Boulton, ported by D.R.Syme",
        path = sys_lib_path "retrieve",
        parents = [(* hol_lib *)],
        theories = [],
        code = ["exceptions.sig","exceptions.sml",
                "sets.sig","sets.sml",
                "extract.sig","extract.sml",
                "struct.sig","struct.sml",
                "name.sig","name.sml",
                "matching.sig","matching.sml",
                "sidecond.sig","sidecond.sml",
                "search.sig","search.sml",
                "user.sig","user.sml",
                "retrieveLib.sml"],
        help = ["entries/"],
        loaded = "fn () => ()"}
   (* else Library.find_library "retrieve"; *)

val group_lib =
   (* if Globals.remake_theory_files *)
   (* then *)Library.new_library
       {name="group",
        doc = "The system library of groups, by Elsa Gunter",
        path=sys_lib_path "group",
        parents = [utils_lib],
        theories = ["elt_gp"],
        code = ["loaded.sml","group_fun.sig","group_fun.sml"],
        help = [],
        loaded = "fn () => ()"}
    (* else Library.find_library"group"; *)

val integer_lib =
   (* if Globals.remake_theory_files *)
   (* then *)Library.new_library
       {name="integer",
        doc = "The system library of integers, by Elsa Gunter",
        path = sys_lib_path "integer",
        parents = [group_lib],
        theories = ["integer"],
        code = ["loaded.sml",
                "integer_tac.sig","integer_tac.sml",
                "integerLib.sml"],
        help = [],
        loaded = "fn () => ()"}
   (* else Library.find_library "integer"; *)

val abs_theory_lib =
   (* if Globals.remake_theory_files *)
   (* then *)Library.new_library
       {name="abs_theory",
        doc = "A library for abstract theory operations, by Phil Windley and David Shepherd",
        path = sys_lib_path "abs_theory",
        parents = [(* hol_lib *)],
        theories = [],
        code = ["abs_theory.sml", "abs_theoryLib.sml"],
        help = [],
        loaded = "fn () => ()"}
   (* else Library.find_library "abs_theory"; *)

val unity_lib =
   (* if Globals.remake_theory_files *)
   (* then *)Library.new_library
       {name     = "unity",
        doc      = "A library defining Chandy and Misra's UNITY logic, due to Flemming Andersen",
        path     = sys_lib_path "unity",
        parents  = [(* hol_lib *)],
        theories = ["comp_unity"],
        code     = ["loaded.sml","leadsto_induct0.sml", "unityLib.sml"],
        help     = [],
        loaded   = "fn () => \
               \(Globals.tilde_symbols := (\"~*\" :: !Globals.tilde_symbols); \
               \ map add_definitions_to_sml \
               \     [\"state_logic\",\"unless\",\"ensures\",\"leadsto\"];())"}
   (* else Library.find_library "unity"; *)

val prog_logic_lib =
   (* if Globals.remake_theory_files *)
   (* then *)Library.new_library
        {name     = "prog_logic",
         doc      = "Various programming logics in HOL, by Mike Gordon, translator: Matthew Morley",
         path     = sys_lib_path "prog_logic",
         parents  = [string_lib],
         theories = ["prog_logic"],
         code     = ["loaded.sml",
                     "syntax_functions.sml","translation.sml","hol_match.sml",
                     "bnd_conv.sml","hoare_logic.sml","halts_logic.sml",
                     "prog_logicLib.sml"],
         help     = [],
         loaded   = "fn () => ()"}
   (* else Library.find_library "prog_logic"; *)

val pair_lib =
   (* if Globals.remake_theory_files *)
   (* then *)Library.new_library
       {name = "pair",
        doc = "A library for manipulating pairs, by J. Grundy, translated by D. Shepherd",
        path = sys_lib_path "pair",
        parents = [(* hol_lib *)],
        theories = ["pair_thms"],
        code = ["loaded.sml",
                "syn.sml","basic.sml","both1.sml","all.sml","exi.sml",
		"both2.sml","conv.sml","pairLib.sig", "pairLib.sml"],
        help = ["entries/"],
        loaded = "fn() => ()"}
    (* else Library.find_library "pair"; *)

val real_lib =
   (* if Globals.remake_theory_files *)
   (* then *)Library.new_library
       {name = "real",
        doc = "The system library for real numbers, by John Harrison",
        path = sys_lib_path "real",
        parents = [(* hol_lib *)],
        theories = ["TRANSC"],
        code = ["realLib.sml"],
        help = ["entries/"],
        loaded = "fn() => ()"}
    (* else Library.find_library "real"; *)

val wellorder_lib =
   (* if Globals.remake_theory_files *)
   (* then *)Library.new_library
       {name = "wellorder",
        doc = "Theorems about the Axiom of Choice and wellordered sets, by John Harrison",
        path = sys_lib_path "wellorder",
        parents = [(* hol_lib *)],
        theories = ["WELLORDER"],
        code = ["wellorderLib.sml"],
        help = ["entries/"],
        loaded = "fn () => ()"}
    (* else Library.find_library "wellorder"; *)

val window_lib =
   (* if Globals.remake_theory_files *)
   (* then *)new_library
        {name    = "window",
         doc     = "Support for transformational reasoning, by Jim Grundy",
         path    = sys_lib_path "window",
         parents = [(* hol_lib *)],
         theories= ["window"],
         code    = ["loaded.sig", "loaded.sml",
                    "ml_ext.sig", "ml_ext.sml", "hol_ext.sig", "hol_ext.sml",
                    "relations.sml", "rules.sml",
                    "basic_close.sml", "eq_close.sml", "imp_close.sml",
                    "win_core.sml", "win.sml", "history.sml", "signal.sml",
                    "defined.sml", "inter.sml", "tty.sml", "tactic.sml",
                    "windowLib.sig", "windowLib.sml"],
         help    = ["defs/","entries/","thms/"],
         loaded  = "fn () => ()"}
   (* else Library.find_library"window"; *)

val list_lib =
   (* if Globals.remake_theory_files *)
   (* then *)new_library
        {name    = "list",
         doc     = "Extended support for lists, by Paul Curzon and Wai Wong",
         path    = sys_lib_path "list",
         parents = [(* hol_lib *)],
         theories= ["List"],
         code    = ["loaded.sml",
                    "list_conv.sig", "list_conv1.sml", "list_conv2.sml",
                    "listLib.sml"],
         help    = ["defs/","entries/","thms/"],
         loaded  = "fn () => ()"}
   (* else Library.find_library"list"; *)

val res_quan_lib =
   (* if Globals.remake_theory_files *)
   (* then *)new_library
        {name    = "res_quan",
         doc     = "Support for restricted quantification, by Wai Wong",
         path    = sys_lib_path "res_quan",
         parents = [(* hol_lib *)],
         theories= ["res_quan"],
         code    = ["loaded.sml",
                    "cond_rewr.sig", "cond_rewr.sml",
                    "res_rules.sig", "res_rules.sml",
                    "res_quanLib.sig", "res_quanLib.sml"],
         help    = ["entries/", "thms/"],
         loaded  = "fn () => ()"}
   (* else Library.find_library"res_quan"; *)

val word_lib =
   (* if Globals.remake_theory_files *)
   (* then *)new_library
        {name    = "word",
         doc     = "Support for bit vectors, by Wai Wong",
         path    = sys_lib_path "word",
         parents = [num_lib, res_quan_lib, list_lib],
         theories= ["word"],
         code    = ["loaded.sml","word_convs.sig", "word_convs.sml",
                    "wordLib.sml"],
         help    = ["entries/", "defs/", "thms/"],
         loaded  = "fn () => ()"}
   (* else Library.find_library"word"; *)


val mutrec_lib = new_library
   {name = "mutrec",
    doc = "Mutually recursive type definition library, by E. Gunter",
    path = sys_lib_path "mutrec",
    parents = [utils_lib, num_lib],
    theories = [],
    code = ["mask.sml", "type_info.sml",
             "mut_rec_type_input.sig",
             "mut_rec_ty.sig", "mut_rec_ty.sml",
             "recftn.sml",
             "cons_thms.sig", "cons_thms.sml",
             "total_mut_rec_type_def.sml"],
     help = [],
     loaded = "fn () => ()"}


val nested_rec_lib = new_library
    {name = "nested_rec",
  doc = "Nested recursive type definition library, by H. Goguen and E. Gunter",
     path = sys_lib_path "nested_rec",
  parents = [mutrec_lib],
 theories = [],
     code = ["mask.sml", "gen_funs.sig","gen_funs.sml","exists_funs.sml",
             "table.sig","table.sml","entries.sml",
             "def_type.sig", "make_type_op.sml", "def_type.sml",
             "nested_rec_def.sml"],
     help = [],
   loaded = "fn () => ()"};

end;
