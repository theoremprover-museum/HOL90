(* File: Modules/Common/eval.sml *)

(* Description: This file contains the definitions of the evaluation
   relations that give the dynamic semantics of the ML Module system. *)

(* Reference: The "Definition", Section 7.3 *)

(* Value Descriptions      |- valdesc => vars *)

val {desc, induction_thm} = new_inductive_definition
{name = "eval_valdesc_DEF",
 fixity = Prefix,
 patt = ((--`(eval_valdesc (valdesc:valdesc) (s1:state) (s2:state)
                (vars:var set)):bool`--),[]),
 rules = [

(* Rule 184a *)
{hypotheses = [],
 side_conditions = [],
 conclusion = (--`(eval_valdesc (VARvaldesc (var:var) NONE) (s1:state)
                     (s2:state) {var}):bool`--)},

(* Rule 184b *)
{hypotheses = [(--`(eval_valdesc (valdesc:valdesc) (s1:state)
                       (s2:state) (vars:var set)):bool`--)],
 side_conditions = [],
 conclusion = (--`(eval_valdesc (VARvaldesc (var:var) (SOME (valdesc:valdesc)))
                     (s1:state) (s2:state) 
                     ({var} UNION (vars:var set))):bool`--)}]};

val [Rule184a,Rule184b] = map save_thm (zip ["Rule184a","Rule184b"] desc);
val eval_valdesc_induction_thm =
    save_thm("eval_valdesc_induction_thm",induction_thm);


(* Exception Descriptions     |- exdesc => excons *)

val {desc, induction_thm} = new_inductive_definition
{name = "eval_exdesc_DEF",
 fixity = Prefix,
 patt = ((--`(eval_exdesc (exdesc:exdesc) (s1:state) (s2:state)
                (excons:excon set)):bool`--),[]),
 rules = [

(* Rule 185a *)
{hypotheses = [],
 side_conditions = [],
 conclusion = (--`(eval_exdesc (EXCONexdesc (excon:excon) NONE) (s1:state)
                     (s2:state) {excon}):bool`--)},

(* Rule 185b *)
{hypotheses = [(--`(eval_exdesc (exdesc:exdesc) (s1:state)
                       (s2:state) (excons:excon set)):bool`--)],
 side_conditions = [],
 conclusion = (--`(eval_exdesc (EXCONexdesc(excon:excon)(SOME(exdesc:exdesc)))
                     (s1:state) (s2:state) 
                     ({excon} UNION (excons:excon set))):bool`--)}]};

val [Rule185a, Rule185b] = map save_thm (zip ["Rule185a"," Rule185b"] desc);
val eval_exdesc_induction_thm =
    save_thm("eval_exdesc_induction_thm",induction_thm);


