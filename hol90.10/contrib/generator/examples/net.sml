(************************ net.sml ***************************************)
(*                                                                      *)
(* Author: Ralf Reetz                                                   *)
(* Date:   6.10.1994                                                    *)
(*                                                                      *)
(* Description:                                                         *)
(*                                                                      *)
(*   Example for the generator with the following grammar G=(V,T,P,S):  *)
(*                                                                      *)
(*   V = {statement_list, program}                                      *)
(*   T = {statement, end}                                               *)
(*   P = {p1 : program -> statement_list ,                              *)
(*        p2 : statement_list -> end ,                                  *)
(*        p3 : statement_list -> statement statement_list}              *)
(*   S = program                                                        *)
(*                                                                      *)
(* A toy example: the source language is a trivial process language,    *)
(* where a word of the source language is a list of statements. The     *)
(* target language is the graph of a petri net. The semantics is now as *)
(* follows: for every statement of the statement list, a transition is  *)
(* allocated. For every position of the program counter, a place is     *)
(* allocated. These places and transitions forms a circle, where the    *)
(* order in the graph is the same as in the statement list. The first   *)
(* position of the program counter is marked. So the semantics of a     *)
(* program is, that the statements will be executed on other the other  *)
(* in an infinite loop. This is behaviour is described by the marking   *)
(* of the petri net, whose representation is as follows:                *)
(*                                                                      *)
(* empty_net : net                                                      *)
(*  the empty petri net                                                 *)
(* new_pn : net -> net                                                  *)
(*  adds a new place to the supplied net                                *)
(* new_tn : net -> net                                                  *)
(*  adds a new transition to the supplied net                           *)
(* last_pn : net -> num                                                 *)
(*  returns the index of the last added new place                       *)
(* last_tn : net -> num                                                 *)
(*  returns the index of the last added new transition                  *)
(* new_tn_2_pn : net -> num -> num -> net                               *)
(*  adds an edge from the supplied transition to the supplied place     *)
(* new_pn_2_tn : net -> num -> num -> net                               *)
(*  adds an edge from the supplied place to the supplied transition     *)
(* mark_pn : net -> num -> net                                          *)
(*  puts a marker on the supplied place                                 *)
(*                                                                      *)
(* Used files:                                                          *)
(* Used modules:                                                        *)
(* Used theories:                                                       *)
(* Used libraries: generator, benchmark                                 *)
(*                                                                      *)
(************************************************************************)

new_theory "net";

val _ = load_library{lib=(find_library "generator"),theory="-"};

(*------------------definition of the petri net-------------------------*)

(*--- type definition ---*)

val net_thm = define_type
 {name      = "net",
  fixities  = [Prefix,Prefix,Prefix,Prefix],
  type_spec = `net = EMPTY |
                     PNNET of num =>            (* last allocated place     *)
                              (num list) |      (* marked places            *)
                     TNNET of num |             (* last allocated transition*)
                     NET of num =>              (* last allocated place     *)
                            num =>              (* last allocated transition*)
                            ((num#num) list) => (* edges from place to tr.  *)
                            ((num#num) list) => (* edges from tr. to place  *)
                            (num list)`};       (* marked places            *)

(*--- definitions ---*)

val empty_net = new_definition("empty_net",--`
 empty_net = EMPTY`--);

val new_pn = new_recursive_definition
 {name      = "new_pn",
  fixity    = Prefix,
  rec_axiom = net_thm,
  def       = (--`
 (new_pn EMPTY = PNNET 0 [])
 /\
 (new_pn (PNNET lpn ml) = PNNET (SUC lpn) ml)
 /\
 (new_pn (TNNET ltn) = NET 0 ltn [] [] [])
 /\
 (new_pn (NET lpn ltn pntnl tnpnl ml) = NET (SUC lpn) ltn pntnl tnpnl ml)
 `--)};

val new_tn = new_recursive_definition
 {name      = "new_tn",
  fixity    = Prefix,
  rec_axiom = net_thm,
  def       = (--`
 (new_tn EMPTY = TNNET 0)
 /\
 (new_tn (PNNET lpn ml) = NET lpn 0 [] [] ml)
 /\
 (new_tn (TNNET ltn) = TNNET (SUC ltn))
 /\
 (new_tn (NET lpn ltn pntnl tnpnl ml) = NET lpn (SUC ltn) pntnl tnpnl ml)
 `--)};

val last_pn = new_recursive_definition
 {name      = "last_pn",
  fixity    = Prefix,
  rec_axiom = net_thm,
  def       = (--`
 (last_pn (PNNET lpn ml) = lpn)
 /\
 (last_pn (NET lpn ltn pntnl tnpnl ml) = lpn)
 `--)};

val last_tn = new_recursive_definition
 {name      = "last_tn",
  fixity    = Prefix,
  rec_axiom = net_thm,
  def       = (--`
 (last_tn (TNNET ltn) = ltn)
 /\
 (last_tn (NET lpn ltn pntnl tnpnl ml) = ltn)
 `--)};

val new_pn_2_tn = new_recursive_definition
 {name      = "new_pn_2_tn",
  fixity    = Prefix,
  rec_axiom = net_thm,
  def       = (--`
 (new_pn_2_tn (NET lpn ltn pntnl tnpnl ml) pn tn = 
 (((pn <= lpn) /\ (tn <= ltn)) =>
 (NET lpn ltn (CONS (pn,tn) pntnl) tnpnl ml)|
 (NET lpn ltn pntnl tnpnl ml)))
 `--)};

val new_tn_2_pn = new_recursive_definition
 {name      = "new_tn_2_pn",
  fixity    = Prefix,
  rec_axiom = net_thm,
  def       = (--`
 (new_tn_2_pn (NET lpn ltn pntnl tnpnl ml) tn pn = 
 (((pn <= lpn) /\ (tn <= ltn)) =>
 (NET lpn ltn pntnl (CONS (tn,pn) tnpnl) ml)|
 (NET lpn ltn pntnl tnpnl ml)))
 `--)};

val mark_pn = new_recursive_definition
 {name      = "mark_pn",
  fixity    = Prefix,
  rec_axiom = net_thm,
  def       = (--`
 (mark_pn (PNNET lpn ml) pn = 
 ((pn <= lpn) => (PNNET lpn (CONS pn ml))|PNNET lpn ml))
 /\
 (mark_pn (NET lpn ltn pntnl tnpnl ml) pn = 
 ((pn <= lpn) => 
 (NET lpn ltn pntnl tnpnl (CONS pn ml))|
 (NET lpn ltn pntnl tnpnl ml)))
 `--)};

(*---------------defining the compiler----------------------------------*)

structure specification : SPECIFICATION = 
struct

(* grammar *)

val G = 
 {terminals   = ["end","statement"],
  startsymbol = "program",
  productions = 
   [{name  = "p1",
     left  = "program",
     right = ["statement_list"]}
    ,
    {name  = "p2",
     left  = "statement_list",
     right = ["end"]}
    ,
    {name  = "p3",
     left  = "statement_list",
     right = ["statement","statement_list"]}
   ]
 };

(* attributation *)

val attribute_sets = [{name="phase0", ty=(==`:one`==)},
                      {name="phase1", ty=(==`:net`==)},
                      {name="phase2", ty=(==`:net`==)}];
val start_set      = "phase0";
val result_set     = "phase2";
val init_attribute = (--`one`--);
val attributation_rules
                   = [{operation="p1",
                      r        =[{lhs=[{var="one1",set="phase0"},
                                       {var="one2",set="phase0"}],
                                   rhs={body=(--`empty_net`--),
                                        set ="phase1"}}],
                      s        =[{lhs=[{var="n1",set="phase1"},
                                       {var="n2",set="phase0"}],
                                   rhs={body=(--`empty_net`--),
                                        set ="phase2"}},
                                 {lhs=[{var="n1",set="phase1"},
                                       {var="n2",set="phase2"}],
                                  rhs={body=(--`
                                  let
                                   pn0 = last_pn (new_pn empty_net) in let
                                   tnx = last_tn n2                 in let
                                   n3  = new_tn_2_pn n2 tnx pn0
                                  in
                                   mark_pn n3 pn0
                                  `--),
                                  set ="phase2"}}]}
                     ,
                     {operation="p3",
                      r        =[{lhs=[{var="one",set="phase0"},
                                       {var="n",  set="phase1"}],
                                  rhs={body=(--`
                                  let
                                   n1 = new_tn n   in let
                                   tn = last_tn n1 in let
                                   n2 = new_pn n1  in let
                                   pn = last_pn n2
                                  in
                                   new_pn_2_tn n2 pn tn
                                  `--),
                                  set="phase1"}}],
                      s        =[{lhs=[{var="n1",set="phase1"},
                                       {var="n2",set="phase2"},
                                       {var="n3",set="phase0"}],
                                  rhs={body=(--`n1:net`--),
                                  set="phase2"}},
                                 {lhs=[{var="n1",set="phase1"},
                                       {var="n2",set="phase2"},
                                       {var="n3",set="phase2"}],
                                  rhs={body=(--`
                                  let
                                   tn = last_tn n1 in let
                                   pn = last_pn (new_pn n1)
                                  in
                                   new_tn_2_pn n3 tn pn
                                  `--),
                                  set="phase2"}}]}
                     ,
                     {operation="p2",
                      r        =[{lhs=[{var="one",set="phase0"},
                                       {var="n",set="phase1"}],
                                  rhs={body=(--`one`--),
                                  set="phase0"}},
                                 {lhs=[{var="n1",set="phase0"},
                                       {var="n2",set="phase2"}],
                                 rhs={body=(--`empty_net`--),
                                 set="phase2"}}],
                      s        =[]}
                     ,
                     {operation="end",
                      r        =[{lhs=[{var="one",set="phase0"},
                                       {var="one",set="phase0"}],
                                 rhs={body=(--`empty_net`--),
                                 set="phase2"}}],
                      s        =[]}
                     ,
                     {operation="statement",
                      r        =[{lhs=[{var="one",set="phase0"},
                                       {var="n",set="phase1"}],
                                 rhs={body=(--`empty_net`--),
                                 set="phase2"}}],
                      s        =[]}
                     ];
val prefix_rules         = "h";
val prefix_attributation = "k";
val simplify_attributation_CONV =
 EVERY_CONV [
  PURE_REWRITE_CONV [definition "-" "empty_net",
                     definition "-" "new_pn",
                     definition "-" "new_tn",
                     definition "-" "last_pn",
                     definition "-" "last_tn",
                     definition "-" "new_pn_2_tn",
                     definition "-" "new_tn_2_pn",
                     definition "-" "mark_pn"],
  PURE_REWRITE_CONV [definition "bool" "LET_DEF"],
  DEPTH_CONV BETA_CONV,
  REWRITE_CONV [theorem "arithmetic" "LESS_EQ_MONO",
                theorem "arithmetic" "NOT_SUC_LESS_EQ_0",
                theorem "arithmetic" "ZERO_LESS_EQ"]
 ];

(* code generation *)

val target_type              = (==`:net`==);
val init_target_value        = (--`empty_net`--);
val prefix_local_translation = "f";
val prefix_translation       = "g";
val translation_rules        =
 [UP_RULE   ("p1","r","a",(--`a:net`--))]; (* f_statement_list_p1 *)
val simplify_translation_CONV = ALL_CONV;

(* attributation + code generation *)

val compilation = "semantics";

end;

structure compiler = 
 new_compiler_definition(structure specification=specification);

(*------------example application------------------------------------------*)

(*---example expression 0 ---*)

val empty_program =
  --`p1 one
      (p2 one
       (end one)
      )`--;

val semantics_empty_program =
save_thm("semantics_empty_program",
 (compiler.compilation_CONV [2] 
 (compiler.mk_compilation empty_program))
);

(*---example expression 1 ---*)

val one_program =
  --`p1 one
      (p3 one
       (statement one)
       (p2 one
        (end one)
       )
      )`--;

val semantics_one_program =
save_thm("semantics_one_program",
 (compiler.compilation_CONV [2] 
 (compiler.mk_compilation one_program))
);

(*---example expression 2 ---*)

val two_program =
  --`p1 one
      (p3 one
       (statement one)
       (p3 one
        (statement one)
        (p2 one
         (end one)
        )
       )
      )`--;

val semantics_two_program =
save_thm("semantics_two_program",
 (compiler.compilation_CONV [2] 
 (compiler.mk_compilation two_program))
);

(*--- example expression n ---*)

fun mk_n_program n =
 let
  fun do_it n =
   if n<=0 then
    (--`p2 one (end one)`--)
   else
    let
     val t = do_it (n-1)
    in
     (--`p3 one (statement one) ^t`--)
    end
  val tn = do_it n
 in
  (--`p1 one ^tn`--)
 end;

fun semantics_n_program n =
 compiler.compilation_CONV [2] (compiler.mk_compilation (mk_n_program n));


(* Do some benchmarking *)

val _ = load_library{lib=(find_library "more_utils"),theory="-"};
val _ =
 benchmark.output_benchmark
 {filename_summary = "net_summary.txt",
  filename_details = "net_details.txt",
  mk_step  = (fn n => n+1),
  mk_index = (fn n => (2*n)+3),
  mk_rand  = mk_n_program,
  rator    = (fn t => compiler.compilation_CONV []
                      (compiler.mk_compilation t)),
  max_count = 10};
