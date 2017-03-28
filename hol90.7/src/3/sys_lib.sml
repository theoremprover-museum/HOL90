structure Sys_lib :Sys_lib_sig = 
struct
val prim_hol_lib = prim_hol_lib
val basic_hol_lib = basic_hol_lib


val hol_lib = 
   if Globals.remake_theory_files
   then Library.new_library
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
         \      (if Globals.remake_theory_files \
         \       then (Globals.theory_path := tl (!Globals.theory_path); \
         \             close_theory(); export_theory()) \
         \       else (); \
         \       Theory.delete_cache(); \
         \       Globals.use_init_file := true; \
         \ PP.install_pp[\"Goalstack\",\"goalstack\"] Goalstack.pp_goalstack; \
         \ PP.install_pp[\"Goalstack\",\"proofs\"] Goalstack.pp_proofs; \
         \       use_string \"open Goalstack; open Implicit\"; \
         \       use_string \"open Define_type Sys_lib Rsyntax\"; \
         \       System.Control.interp := true; \
         \       Install.install (!Globals.HOLdir); \
         \       Save_hol.save_hol (\"hol90.\"^Globals.arch))"}
   else let val hlib = Library.find_library "HOL"
        in Library.move_library(hlib, !Globals.HOLdir);
           hlib
        end;



(* Make some system libraries known *)
fun sys_lib_path s = (!HOLdir)^"library/"^s^"/"

val string_lib = 
   if Globals.remake_theory_files
   then Library.new_library
         {name = "string",
          doc = "The system string library, by Mike Gordon and Tom Melham",
          path = sys_lib_path "string",
          parents = [hol_lib],
          theories = ["string"],
          code = ["string_conv.sml","ascii_conv.sml","string_rules.sml"],
          help = [],
          loaded = "fn () => Globals.assert_strings_defined()"}
    else Library.find_library "string"

val num_lib = 
   if Globals.remake_theory_files
   then Library.new_library
        {name="num",
         doc = "The system library supporting proofs about numbers, due to John Harrison",
         path = sys_lib_path "num",
         parents = [hol_lib],
         theories = [],
         code = ["num_lib.sig","num_lib.sml"],
         help = [],
         loaded = "fn() => ()"}
   else Library.find_library "num";

val reduce_lib = 
   if Globals.remake_theory_files
   then Library.new_library
        {name = "reduce",
         doc = "The system library for normalizing {bool,num} terms, by John Harrison",
         path = sys_lib_path "reduce",
         parents = [hol_lib],
         theories = [],
         code = ["dest.sig","dest.sml",
                 "boolconv.sig","boolconv.sml",
                 "arithconv.sig","arithconv.sml",
                 "redconv.sig","redconv.sml",
                 "reduce.sml"],
         help = ["entries/"],
         loaded = "fn() => ()"}
   else Library.find_library "reduce";

val arith_lib =
   if Globals.remake_theory_files
   then Library.new_library
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
                "arith.sig", "arith.sml"],
         help = ["entries/"],
         loaded = "fn() => Lib.eval_string \"open Arith\""}
    else Library.find_library "arith";

val set_lib = 
   if Globals.remake_theory_files
   then Library.new_library
        {name="set",
         doc = "The system library of sets, due to Tom Melham and P. Leveilley",
         path=sys_lib_path "set",
         parents=[num_lib],
         theories=["set"],
         code=["gspec.sig","gspec.sml",
               "set_ind.sig","set_ind.sml",
               "fset_conv.sig","fset_conv.sml"],
         help=["entries/"],
         loaded = "fn() => ()"}
   else Library.find_library "set";

val pred_set_lib = 
   if Globals.remake_theory_files
   then Library.new_library
        {name="pred_set",
         doc = "The library of sets-as-predicates, due to Tom Melham and Ton Kalker",
         path=sys_lib_path "pred_set",
         parents=[num_lib],
         theories=["pred_set"],
         code=["gspec.sig","gspec.sml",
               "set_ind.sig","set_ind.sml",
               "fset_conv.sig","fset_conv.sml"],
         help=["entries/"],
         loaded = "fn() => ()"}
   else Library.find_library "pred_set";

val unwind_lib = 
   if Globals.remake_theory_files
   then Library.new_library
        {name="unwind",
         doc = "The system library for unwinding hardware lines, by Richard Boulton",
         path=sys_lib_path "unwind",
         parents = [hol_lib],
         theories = [],
         code = ["unwinding.sig","unwinding.sml"],
         help = ["entries/"],
         loaded = "fn () => ()"}
   else Library.find_library"unwind";
         
val hol88_lib = 
   if Globals.remake_theory_files
   then Library.new_library
        {name="hol88",
         doc = "A library for compatibility with hol88, by Konrad Slind",
         path=sys_lib_path "hol88",
         parents = [hol_lib],
         theories = [],
         code = ["compat.sig", "compat.sml"],
         help = [],
         loaded = "fn () => ()"}
   else Library.find_library "hol88";

val ind_def_lib = 
   if Globals.remake_theory_files
   then Library.new_library
        {name="ind_def",
         doc = "The system inductive definition package, by Tom Melham",
         path=sys_lib_path "ind_def",
         parents = [hol88_lib],
         theories = [],
         code = ["inductive_def.sig","inductive_def.sml"],
         help = [],
         loaded = "fn () => ()"}
   else Library.find_library "ind_def";
         
val taut_lib = 
   if Globals.remake_theory_files
   then Library.new_library
        {name="taut",
         doc = "The system tautology checker library, by Richard Boulton",
         path=sys_lib_path "taut",
         parents = [hol_lib],
         theories = [],
         code = ["taut.sig","taut.sml"],
         help = ["entries/"],
         loaded = "fn () => ()"}
   else Library.find_library "taut";

val utils_lib = 
   if Globals.remake_theory_files
   then Library.new_library
       {name="utils",
        doc = "A library of useful functions, by Elsa Gunter",
        path=sys_lib_path "utils",
        parents = [hol_lib],
        theories = [],
        code = ["functions.sig","functions.sml"],
        help = [],
        loaded = "fn () => ()"}
   else Library.find_library "utils";

val group_lib = 
   if Globals.remake_theory_files
   then Library.new_library
       {name="group",
        doc = "The system library of groups, by Elsa Gunter",
        path=sys_lib_path "group",
        parents = [utils_lib],
        theories = ["elt_gp"],
        code = ["group_fun.sig","group_fun.sml"],
        help = [],
        loaded = "fn () => ()"}
    else Library.find_library"group";

val integer_lib = 
   if Globals.remake_theory_files
   then Library.new_library
       {name="integer",
        doc = "The system library of integers, by Elsa Gunter",
        path = sys_lib_path "integer",
        parents = [group_lib],
        theories = ["integer"],
        code = ["integer_tac.sig","integer_tac.sml"],
        help = [],
        loaded = "fn () => ()"}
   else Library.find_library "integer";

val abs_theory_lib = 
   if Globals.remake_theory_files
   then Library.new_library
       {name="abs_theory",
        doc = "A library for abstract theory operations, by Phil Windley and David Shepherd",
        path = sys_lib_path "abs_theory",
        parents = [hol_lib],
        theories = [],
        code = ["abs_theory.sml"],
        help = [],
        loaded = "fn () => ()"}
   else Library.find_library "abs_theory";

val unity_lib = 
   if Globals.remake_theory_files
   then Library.new_library
       {name     = "unity",
        doc      = "A library defining Chandy and Misra's UNITY logic, due to Flemming Andersen",
        path     = sys_lib_path "unity",
        parents  = [hol_lib],
        theories = ["comp_unity"],
        code     = ["leadsto_induct0.sml"],
        help     = [],
        loaded   = "fn () => \
               \(Globals.tilde_symbols := (\"~*\" :: !Globals.tilde_symbols); \
               \ map add_definitions_to_sml \
               \     [\"state_logic\",\"unless\",\"ensures\",\"leadsto\"];())"}
   else Library.find_library "unity";

val prog_logic_lib = 
   if Globals.remake_theory_files
   then Library.new_library
        {name     = "prog_logic",
         doc      = "Various programming logics in HOL, by Mike Gordon, translator: Matthew Morley",
         path     = sys_lib_path "prog_logic",
         parents  = [string_lib],
         theories = ["prog_logic"],
         code     = ["syntax_functions.sml","translation.sml","hol_match.sml",
                     "bnd_conv.sml","hoare_logic.sml","halts_logic.sml",
                     "prog_logic.sml"],
         help     = [],
         loaded   = "fn () => ()"}
   else Library.find_library "prog_logic";

val pair_lib = 
   if Globals.remake_theory_files
   then Library.new_library
       {name = "pair",
        doc = "A library for manipulating pairs, by J. Grundy, translated by D. Shepherd",
        path = sys_lib_path "pair",
        parents = [hol_lib],
        theories = ["pair_thms"],
        code = ["syn.sml","basic.sml","both1.sml","all.sml","exi.sml",
		"both2.sml","conv.sml","open_pair.sml"],
        help = ["entries/"],
        loaded = "fn() => ()"}
    else Library.find_library "pair";

val real_lib = 
   if Globals.remake_theory_files
   then Library.new_library
       {name = "real",
        doc = "The system library for real numbers, by John Harrison",
        path = sys_lib_path "real",
        parents = [hol_lib],
        theories = ["TRANSC"],
        code = [],
        help = ["entries/"],
        loaded = "fn() => ()"}
    else Library.find_library "real";

val wellorder_lib = 
   if Globals.remake_theory_files
   then Library.new_library
       {name = "wellorder",
        doc = "Theorems about the Axiom of Choice and wellordered sets, by John Harrison",
        path = sys_lib_path "wellorder",
        parents = [hol_lib],
        theories = ["WELLORDER"],
        code = [],
        help = ["entries/"],
        loaded = "fn() => ()"}
    else Library.find_library "wellorder";

val window_lib = 
   if Globals.remake_theory_files
   then new_library
        {name    = "window",
         doc     = "Support for transformational reasoning, by Jim Grundy",
         path    = sys_lib_path "window",
         parents = [hol_lib],
         theories= ["window"],
         code    = ["ml_ext.sml", "hol_ext.sml", "relations.sml", "rules.sml",
                    "basic_close.sml", "eq_close.sml", "imp_close.sml",
                    "win_core.sml", "win.sml", "history.sml", "signal.sml",
                    "defined.sml", "inter.sml", "tty.sml", "tactic.sml",
                    "window.sml"],
         help    = ["defs/","entries/","thms/"],
         loaded  = "fn () => ()"}
   else Library.find_library"window";

val list_lib = 
   if Globals.remake_theory_files
   then new_library
        {name    = "list",
         doc     = "Extended support for lists, by Paul Curzon and Wai Wong",
         path    = sys_lib_path "list",
         parents = [hol_lib],
         theories= ["List"],
         code    = ["list_conv.sig", "list_conv1.sml", "list_conv2.sml"],
         help    = ["defs/","entries/","thms/"],
         loaded  = "fn () => ()"}
   else Library.find_library"list";

val res_quan_lib = 
   if Globals.remake_theory_files
   then new_library
        {name    = "res_quan",
         doc     = "Support for restricted quantification, by Wai Wong",
         path    = sys_lib_path "res_quan",
         parents = [hol_lib],
         theories= ["res_quan"],
         code    = ["cond_rewr.sig", "cond_rewr.sml",
                    "res_rules.sig", "res_rules.sml"],
         help    = ["entries/", "thms/"],
         loaded  = "fn () => ()"}
   else Library.find_library"res_quan";

val word_lib = 
   if Globals.remake_theory_files
   then new_library
        {name    = "word",
         doc     = "Support for bit vectors, by Wai Wong",
         path    = sys_lib_path "word",
         parents = [num_lib, res_quan_lib, list_lib],
         theories= ["word"],
         code    = ["word_convs.sig", "word_convs.sml"],
         help    = ["entries/", "defs/", "thms/"],
         loaded  = "fn () => ()"}
   else Library.find_library"word";

end;
