(* ===================================================================== *)
(* FILE          : add_to_sml.sml                                        *)
(* DESCRIPTION   : Routines that allow theory-level bindings to become   *)
(*                 SML bindings. Intended to serve as a replacement for  *)
(*                 auto-loading.                                         *)
(*                                                                       *)
(* AUTHOR        : Konrad Slind, University of Calgary                   *)
(* DATE          : September 15, 1991                                    *)
(* ===================================================================== *)


functor ADD_TO_SML (structure Theory :Theory_sig
                    structure Lexis :Lexis_sig): Add_to_sml_sig =
struct
structure Lexis = Lexis;

open Theory
type thm = Theory.Thm.thm

fun ADD_TO_SML_ERR{function,message} = HOL_ERR{origin_structure = "Add_to_sml",
					       origin_function = function,
					       message = message}

val L = ref ([]:(string*thm) list);
fun parser [QUOTE "",ANTIQUOTE th, QUOTE ""] = th
  | parser _ = raise ADD_TO_SML_ERR{function = "parser",
				    message = "bad format"};


fun install() =
   if (null (!L))
   then ()
   else let val (n,_) = hd (!L)
        in 
          if (Lexis.ok_sml_identifier n)
           then ( Lib.eval_string
                  ("val "^n^" = Add_to_sml.parser`^(snd(hd(!Add_to_sml.L)))`");
                  ())
           else Lib.say ("\n"^Lib.quote n^" can not be a variable in SML, so\
                         \ skipping its binding.\n")
           ;
           L := tl (!L)
           ;
           install ()
        end;

fun add_to_sml alist = 
   ( L := alist;
     install()
   )
   handle _ => (L := [];
                raise ADD_TO_SML_ERR{function = "add_to_sml",message = ""});
  
val add_axioms_to_sml      = add_to_sml o axioms
and add_definitions_to_sml = add_to_sml o definitions
and add_theorems_to_sml    = add_to_sml o theorems;

fun add_theory str =
   ( add_axioms_to_sml str;
     add_definitions_to_sml str;
     add_theorems_to_sml str
   );


type autoload_info = {Theory : string,
                      Axioms : string list,
                      Definitions : string list,
                      Theorems : string list}

val autoloads = ref
([{Theory = "pair",
  Axioms = [],
  Definitions = ["UNCURRY_DEF", "CURRY_DEF"],
  Theorems = ["PAIR", "FST", "SND", "PAIR_EQ"]
},


{Theory = "one",
 Axioms = [],
 Definitions = [],
 Theorems = ["one_axiom", "one", "one_Axiom"]
},


{Theory = "combin",
 Axioms = [],
 Definitions = ["o_DEF", "K_DEF", "S_DEF", "I_DEF"],
 Theorems = ["o_THM", "o_ASSOC", "K_THM", "S_THM", "I_THM", "I_o_ID"]
},


{Theory = "sum",
 Axioms = [],
 Definitions = ["ISL", "ISR", "OUTL", "OUTR"],
 Theorems = ["sum_Axiom", "sum_axiom", "ISL_OR_ISR", "INL", "INR"]
},


{Theory = "num",
 Axioms = [],
 Definitions = [],
 Theorems = ["NOT_SUC", "INV_SUC", "INDUCTION"]
},


{Theory = "prim_rec",
 Axioms = [],
 Definitions = [],
 Theorems = ["INV_SUC_EQ", "LESS_REFL", "SUC_LESS",
             "NOT_LESS_0", "LESS_MONO", "LESS_SUC_REFL",
             "LESS_SUC",   "LESS_THM",  "LESS_SUC_IMP",
             "LESS_0",     "EQ_LESS",   "SUC_ID",
             "NOT_LESS_EQ","LESS_NOT_EQ","LESS_SUC_SUC",
             "PRE",        "num_Axiom"]
},


{Theory = "arithmetic",
 Axioms = [],
 Definitions = ["GREATER", "LESS_OR_EQ", "GREATER_OR_EQ", "DIVISION", 
                "ADD", "MULT", "SUB", "EXP", "FACT", "EVEN", "ODD"],
 Theorems = ["ADD_SUC", "ADD_CLAUSES", "ADD_SYM", 
             "num_CASES", "LESS_MONO_EQ", "SUC_SUB1", "PRE_SUB1",
             "LESS_ADD", "SUB_0", "LESS_TRANS", "ADD1", "ADD_0",
             "LESS_ANTISYM", "LESS_LESS_SUC", "FUN_EQ_LEMMA",
             "LESS_SUC_EQ_COR", "LESS_OR", "OR_LESS", "LESS_EQ",
             "LESS_NOT_SUC", "LESS_0_CASES",
             "LESS_CASES_IMP", "LESS_CASES", "ADD_INV_0", "LESS_EQ_ADD",
             "LESS_EQ_SUC_REFL", "LESS_ADD_NONZERO", "LESS_EQ_ANTISYM",
             "NOT_LESS", "SUB_EQ_0", "ADD_ASSOC", "MULT_0", "MULT_CLAUSES",
             "MULT_SYM", "RIGHT_ADD_DISTRIB", "LEFT_ADD_DISTRIB", "MULT_ASSOC",
             "SUB_ADD", "PRE_SUB", "ADD_EQ_0", "ADD_INV_0_EQ", "PRE_SUC_EQ",
             "INV_PRE_EQ", "LESS_SUC_NOT", "ADD_EQ_SUB", "LESS_MONO_ADD",
             "LESS_MONO_ADD_EQ", "EQ_MONO_ADD_EQ", "LESS_EQ_MONO_ADD_EQ",
             "LESS_EQ_TRANS", "LESS_EQ_LESS_EQ_MONO", "LESS_EQ_REFL",
             "LESS_IMP_LESS_OR_EQ", "LESS_MONO_MULT", "RIGHT_SUB_DISTRIB",
             "LESS_ADD_1", "ZERO_LESS_EQ", "LESS_EQ_MONO", "LESS_OR_EQ_ADD",
             "SUC_NOT", "EXP_ADD", "NOT_ODD_EQ_EVEN", "MULT_SUC_EQ",
             "MULT_EXP_MONO", "WOP", "DA", "MOD_ONE", "DIV_LESS_EQ",
             "DIV_UNIQUE", "MOD_UNIQUE","DIV_MULT", "LESS_MOD", "MOD_EQ_0",
             "ZERO_MOD", "MOD_MULT", "MOD_TIMES", "MOD_PLUS", "MOD_MOD",
             "SUB_MONO_EQ", "SUB_PLUS", "INV_PRE_LESS", "INV_PRE_LESS_EQ",
             "SUB_LESS_EQ", "LESS_EQUAL_ANTISYM", "SUB_EQ_EQ_0",
             "SUB_LESS_0", "SUB_LESS_OR", "LESS_ADD_SUC", "LESS_SUB_ADD_LESS",
             "TIMES2", "LESS_MULT_MONO", "MULT_MONO_EQ", "ADD_SUB",
             "LESS_EQ_ADD_SUB", "SUB_EQUAL_0", "LESS_EQ_SUB_LESS",
             "NOT_SUC_LESS_EQ", "SUB_SUB", "LESS_IMP_LESS_ADD",
             "LESS_EQ_IMP_LESS_SUC", "SUB_LESS_EQ_ADD", "SUB_CANCEL",
             "CANCEL_SUB", "NOT_EXP_0", "ZERO_LESS_EXP", "ODD_OR_EVEN",
             "LESS_EXP_SUC_MONO", "ADD_MONO_LESS_EQ","EQ_LESS_EQ","EVEN_ADD",
             "EVEN_AND_ODD","EVEN_DOUBLE", "EVEN_EXISTS","EVEN_MULT",
             "EVEN_ODD","EVEN_ODD_EXISTS","EVEN_OR_ODD",
             "FACT_LESS","GREATER_EQ","LEFT_SUB_DISTRIB","LESS_EQUAL_ADD",
             "LESS_EQ_0","LESS_EQ_CASES","LESS_EQ_EXISTS","LESS_EQ_LESS_TRANS",
             "LESS_LESS_CASES","LESS_LESS_EQ_TRANS","LESS_MONO_ADD_INV",
             "LESS_MONO_REV","LESS_MULT2","LESS_SUC_EQ","MULT_EQ_0",
             "MULT_LEFT_1","MULT_LESS_EQ_SUC","MULT_RIGHT_1","MULT_SUC",
             "NOT_GREATER","NOT_GREATER_EQ","NOT_LEQ","NOT_LESS_EQUAL",
             "NOT_NUM_EQ","NOT_SUC_ADD_LESS_EQ","NOT_SUC_LESS_EQ_0","ODD_ADD",
             "ODD_DOUBLE","ODD_EVEN","ODD_EXISTS","ODD_MULT","SUB_LEFT_ADD",
             "SUB_LEFT_EQ","SUB_LEFT_GREATER","SUB_LEFT_GREATER_EQ",
             "SUB_LEFT_LESS", "SUB_LEFT_LESS_EQ","SUB_LEFT_SUB","SUB_LEFT_SUC",
             "SUB_RIGHT_ADD","SUB_RIGHT_EQ","SUB_RIGHT_GREATER",
             "SUB_RIGHT_GREATER_EQ","SUB_RIGHT_LESS","SUB_RIGHT_LESS_EQ",
             "SUB_RIGHT_SUB","SUC_ADD_SYM","SUC_ONE_ADD","ZERO_DIV"]
},


{Theory = "list",
 Axioms = [],
 Definitions = ["NULL_DEF", "HD", "TL", "SUM", "APPEND",
                "FLAT", "LENGTH", "MAP", "MAP2", "EL", "EVERY_DEF"],
 Theorems = ["list_Axiom", "NULL", "list_INDUCT", "list_CASES",
             "CONS_11", "NOT_NIL_CONS", "NOT_CONS_NIL", "LIST_NOT_EQ",
             "NOT_EQ_LIST", "EQ_LIST", "CONS", "APPEND_ASSOC", 
             "LENGTH_APPEND", "MAP_APPEND", "LENGTH_MAP", "EVERY_EL",
             "EVERY_CONJ", "LENGTH_NIL", "LENGTH_CONS"]
},


{Theory = "rec_type",
 Axioms = [],
 Definitions = [],
 Theorems = ["TY_DEF_THM", "exists_TRP"]
}]:autoload_info list);


fun find_th s [] = NONE
  | find_th s ((ainfo as {Theory, ...}:autoload_info)::rst) = 
      if (s = Theory)
      then SOME ainfo
      else find_th s rst

fun set_autoloads r = autoloads := r::(!autoloads);

fun add_theory_to_sml str =
  case (find_th str (!autoloads))
    of NONE => add_theory str
     | (SOME {Axioms, Definitions, Theorems, ...}) =>
        ( add_to_sml((gather (fn (s,_) => mem s Axioms) (axioms str)) @
                     (gather (fn (s,_) => mem s Definitions)(definitions str))@
                     (gather (fn (s,_) => mem s Theorems) (theorems str)));
          Theory.delete_theory_from_cache str
        );


local
fun mk_entry thy kind name =
      implode ["val ",name," = Base_logic.Theory.",kind," \"",thy,
	       "\" \"",name,"\"\n"]

fun mk_axiom_entries thy name_list =
    implode (map (mk_entry thy "axiom") name_list)

fun mk_definition_entries thy name_list =
    implode (map (mk_entry thy "definition") name_list)

fun mk_theorem_entries thy name_list =
    implode (map (mk_entry thy "theorem") name_list)

fun mk_theory_structure thy str =
    let
	val (Axioms, Definitions, Theorems) = 
	    (case (find_th thy (!autoloads))
	       of NONE => (map fst (Theory.axioms thy),
			   map fst (Theory.definitions thy),
			   map fst (Theory.theorems thy))
		| SOME {Axioms, Definitions, Theorems, ...} =>
		 (Axioms, Definitions, Theorems))
    in
	implode ["structure ",str," =\nstruct\n",
		 (mk_axiom_entries thy Axioms),
		 (mk_definition_entries thy Definitions),
		 (mk_theorem_entries thy Theorems),"end\n"]
    end
in
fun add_theory_structure_to_sml {structure_name,theory_name} =
    let val command = mk_theory_structure theory_name structure_name
	(*val _ = print command*)
    in 
    Lib.eval_string command
    end
end

end; (* Add_to_sml *)
