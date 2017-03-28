(************************ postfix.sml ***********************************)
(*                                                                      *)
(* Author: Ralf Reetz                                                   *)
(* Date:   6.10.1994                                                    *)
(*                                                                      *)
(* Description:                                                         *)
(*                                                                      *)
(*   Example for the generator with the following grammar G=(V,T,P,S):  *)
(*                                                                      *)
(*   V = {Expr , Term , Form, Ide}                                      *)
(*   T = {PLUS , MULT , CL , LC, X, Y}                                  *)
(*   P = {p1 : Expr  -> Expr PLUS Term ,                                *)
(*        p2 : Expr  -> Term           ,                                *)
(*        p3 : Term  -> Term MULT Form ,                                *)
(*        p4 : Term  -> Form           ,                                *)
(*        p5 : Form  -> CL Expr LC     ,                                *)
(*        p6 : Form  -> Ide            ,                                *)
(*        p7 : Ide   -> X Ide          ,                                *)
(*        p8 : Ide   -> Y Ide          ,                                *)
(*        p9 : Ide   -> X              ,                                *)
(*        p10: Ide   -> Y              }                                *)
(*   S = Expr                                                           *)
(*                                                                      *)
(*   This is a toy example: The source language is a syntax for         *)
(*   arithmetic expressions with variables, addition and multiplication,*)
(*   where multiplication has a higher priority than addition.          *)
(*   Variables are non-empty identifiers, consisting of X's or Y's. The *)
(*   target language is the equivalent postfix notation, represented as *)
(*   a list of names, "+" and "*".                                      *)
(*   The attributes are organized as follows:                           *)
(*   ==`:one`== is  for the source language, ==`:string`== for the      *) 
(*   result of the attributation and ==`:string list`== for the target  *)
(*   language. The attributation is simple: in the first pass, all      *)
(*   relevant attributes are synthesised bottom-up. In the second pass, *)
(*   the intermediate attributes of attribute set char are changed to   *)
(*   the result attribute set.                                          *)
(*                                                                      *)
(* Used files:                                                          *)
(* Used modules:                                                        *)
(* Used theories:                                                       *)
(* Used libraries: generator, string, more_utils                        *)
(*                                                                      *)
(************************************************************************)

new_theory "postfix";

val _ = load_library{lib=(find_library "generator"),theory="-"};
val _ = load_library{lib=(find_library "string")   ,theory="-"};
val _ = load_library{lib=(find_library "more_utils"),theory="-"};

(*---------------defining the compiler----------------------------------*)

structure specification : SPECIFICATION = 
struct

(* grammar *)

val G = 
 {terminals   = ["MULT","PLUS","CL","LC","X","Y"],
  startsymbol = "Expr",
  productions = 
   [{name  = "p1",
     left  = "Expr",
     right = ["Expr","PLUS","Term"]}
    ,
    {name  = "p2",
     left  = "Expr",
     right = ["Term"]}
    ,
    {name  = "p3",
     left  = "Term",
     right = ["Term","MULT","Form"]}
    ,
    {name  = "p4",
     left  = "Term",
     right = ["Form"]}
    ,
    {name  = "p5",
     left  = "Form",
     right = ["CL","Expr","LC"]}
    ,
    {name  = "p6",
     left  = "Form",
     right = ["Ide"]}
    ,
    {name  = "p7",
     left  = "Ide",
     right = ["X","Ide"]}
    ,
    {name  = "p8",
     left  = "Ide",
     right = ["Y","Ide"]}
    ,
    {name  = "p9",
     left  = "Ide",
     right = ["X"]}
    ,
    {name  = "p10",
     left  = "Ide",
     right = ["Y"]}
   ]
 };

(* attributation *)

val attribute_sets = [{name="nothing",   ty=(==`:one`==)},
                      {name="char",      ty=(==`:ascii`==)},
                      {name="Identifier",ty=(==`:string`==)}];
val start_set      = "nothing";
val result_set     = "Identifier";
val init_attribute = (--`one`--);
val attributation_rules
                   = [{operation="MULT",
                      r        =[{lhs=[{var="one",set="nothing"},
                                       {var="s",set="nothing"}],
                                  rhs={body=(--`"*"`--),set="Identifier"}}],
                      s        =[]}
                     ,
                     {operation="PLUS",
                      r        =[{lhs=[{var="one",set="nothing"},
                                       {var="s",set="nothing"}],
                                  rhs={body=(--`"+"`--),set="Identifier"}}],
                      s        =[]}
                     ,
                     {operation="CL",
                      r        =[{lhs=[{var="one",set="nothing"},
                                       {var="s",set="nothing"}],
                                  rhs={body=(--`""`--),set="Identifier"}}],
                      s        =[]}
                     ,
                     {operation="LC",
                      r        =[{lhs=[{var="one",set="nothing"},
                                       {var="s",set="nothing"}],
                                  rhs={body=(--`""`--),set="Identifier"}}],
                      s        =[]}
                     ,
                     {operation="p1",
                      r        =[],
                      s        =[{lhs=[{var="one",set="nothing"},
                                       {var="s1",set="Identifier"},
                                       {var="s2",set="Identifier"},
                                       {var="s3",set="Identifier"}],
                                  rhs={body=(--`""`--),set="Identifier"}}]}
                     ,
                     {operation="p2",
                      r        =[],
                      s        =[{lhs=[{var="one",set="nothing"},
                                       {var="s",set="Identifier"}],
                                  rhs={body=(--`""`--),set="Identifier"}}]}
                     ,
                     {operation="p3",
                      r        =[],
                      s        =[{lhs=[{var="one",set="nothing"},
                                       {var="s1",set="Identifier"},
                                       {var="s2",set="Identifier"},
                                       {var="s3",set="Identifier"}],
                                  rhs={body=(--`""`--),set="Identifier"}}]}
                     ,
                     {operation="p4",
                      r        =[],
                      s        =[{lhs=[{var="one",set="nothing"},
                                       {var="s",set="Identifier"}],
                                  rhs={body=(--`""`--),set="Identifier"}}]}
                     ,
                     {operation="p5",
                      r        =[],
                      s        =[{lhs=[{var="one",set="nothing"},
                                       {var="s1",set="Identifier"},
                                       {var="s2",set="Identifier"},
                                       {var="s3",set="Identifier"}],
                                  rhs={body=(--`""`--),set="Identifier"}}]}
                     ,
                     {operation="p6",
                      r        =[],
                      s        =[{lhs=[{var="one",set="nothing"},
                                       {var="s",set="Identifier"}],
                                  rhs={body=(--`""`--),set="Identifier"}}]}
                     ,
                     {operation="X",
                      r        =[{lhs=[{var="one",set="nothing"},
                                       {var="one",set="nothing"}],
                                  rhs={body=(--`ASCII F T F T T F F F`--),
                                       set ="char"}}
                                 ,
                                 {lhs=[{var="char",set="char"},
                                       {var="s",set="Identifier"}],
                                  rhs={body=(--`""`--),set ="Identifier"}}],
                      s        =[]}
                     ,
                     {operation="Y",
                      r        =[{lhs=[{var="one",set="nothing"},
                                       {var="one",set="nothing"}],
                                  rhs={body=(--`ASCII F T F T T F F T`--),
                                       set ="char"}}
                                 ,
                                 {lhs=[{var="char",set="char"},
                                       {var="s",set="Identifier"}],
                                  rhs={body=(--`""`--),
                                       set ="Identifier"}}],
                      s        =[]}
                     ,
                     {operation="p7",
                      r        =[],
                      s        =[{lhs=[{var="one",set="nothing"},
                                       {var="x",set="char"},
                                       {var="s",set="Identifier"}],
                                 rhs={body=(--`STRING x s`--),
                                      set ="Identifier"}}]}
                     ,
                     {operation="p8",
                      r        =[],
                      s        =[{lhs=[{var="one",set="nothing"},
                                       {var="y",set="char"},
                                       {var="s",set="Identifier"}],
                                 rhs ={body=(--`STRING y s`--),
                                       set ="Identifier"}}]}
                     ,
                     {operation="p9",
                      r        =[],
                      s        =[{lhs=[{var="one",set="nothing"},
                                       {var="x",set="char"}],
                                 rhs ={body=(--`STRING x ""`--),
                                       set ="Identifier"}}]}
                     ,
                     {operation="p10",
                      r        =[],
                      s        =[{lhs=[{var="one",set="nothing"},
                                       {var="y",set="char"}],
                                 rhs ={body=(--`STRING y ""`--),
                                       set ="Identifier"}}]}
                     ];
val prefix_rules         = "h";
val prefix_attributation = "k";
val simplify_attributation_CONV = ALL_CONV;

(* code generation *)

val target_type              = (==`:string list`==);
val init_target_value        = (--`[]:string list`--);
val prefix_local_translation = "f";
val prefix_translation       = "g";
val translation_rules        =
 [UP_RULE   ("p1","r","a",(--`APPEND r ["+"]`--)),         (* f_Term_p1 *)
  UP_RULE   ("p3","r","a",(--`APPEND r ["*"]`--)),         (* f_Form_p3 *)
  DOWN_RULE ("p6","r","a",(--`APPEND r [(a:string)]`--))]; (* f_p6_Ide  *)
val simplify_translation_CONV = ALL_CONV;

(* attributation + code generation *)

val compilation = "semantics";

end;

structure compiler = 
 new_compiler_definition(structure specification=specification);

(*------------example application------------------------------------------*)

(*---example expression---*)

val CL_XX_PLUS_Y_LC_MULT_X =
   --`p2 one
       (p3 one
        (p4 one
         (p5 one
          (CL one)
          (p1 one
           (p2 one
            (p4 one
             (p6 one
              (p7 one
               (X one)
               (p9 one
                (X one)
               )
              )
             )
            )
           )
           (PLUS one)
           (p4 one
            (p6 one
             (p10 one
              (Y one)
             )
            )
           )
          )
          (LC one)
         )
        )
        (MULT one)
        (p6 one
         (p9 one
          (X one)
         )
        )
       )`--;

save_thm("semantics_CL_XX_PLUS_Y_LC_MULT_X",
 PURE_REWRITE_RULE [definition "list" "APPEND"]
 (compiler.compilation_CONV [] 
 (compiler.mk_compilation CL_XX_PLUS_Y_LC_MULT_X))
);

(*--- benchmark ---*)

(*
  Input:
   a number n and a term of type k_attribute_set TY_Expr
  Output:
   the term t will be added with itself n times
*)
fun mk_n_term t n =
 if n<=0 then
  t
 else
  let
   val t1 = mk_n_term t (n-1)
  in
   (--`p1 (one) ^t (PLUS (one)) (p4 (one)
       (p5 (one) (CL (one)) (^t1) 
       (LC (one)) ))`--)
  end;

val _ =
 benchmark.output_benchmark
 {filename_summary = "postfix_summary.txt",
  filename_details = "postfix_details.txt",
  mk_step  = (fn n => n+1),
  mk_index = (fn n => 29*n+23),
  mk_rand  = mk_n_term CL_XX_PLUS_Y_LC_MULT_X,
  rator    = (fn t => compiler.compilation_CONV []
                      (compiler.mk_compilation t)),
  max_count = 10};
