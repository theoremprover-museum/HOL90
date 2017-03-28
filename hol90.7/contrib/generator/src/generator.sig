(************************ generator.sig *********************************)
(*                                                                      *)
(* Author: Ralf Reetz                                                   *)
(* Date:   27.9.1994                                                    *)
(*                                                                      *)
(* Description:                                                         *)
(*                                                                      *)
(*   Signatures of a formal compiler compiler.                          *)
(*                                                                      *)
(*   functor new_generator_definition(grammar:GRAMMAR):GENERATOR makes  *)
(*   the needed definitions for a code generator for the given grammar  *)
(*   into the current theory and delivers a structure containing the    *)
(*   following:                                                         *)
(*                                                                      *)
(*   Notice that variables should not be supplied, they are computed    *)
(*   out of the supplied production rules. Furthermore, the grammar     *)
(*   should not contain useless variables and productions with empty    *)
(*   right sides. HOL should be in draft mode.                          *)
(*                                                                      *)
(* Used files:                                                          *)
(* Used modules:                                                        *)
(* Used theories:                                                       *)
(* Used libraries:                                                      *)
(*                                                                      *)
(************************************************************************)

datatype translation_rule =
   DOWNUP_RULE    of string* (* terminal                         *)
                     string* (* variable for the received result *)
                     string* (* variable for the own attribute   *)
                     term    (* body of the rule                 *)
 | DOWN_RULE      of string* (* production name                  *)
                     string* (* variable for the received result *)
                     string* (* variable for the own attribute   *)
                     term    (* body of the rule                 *) 
 | LEFTRIGHT_RULE of string* (* production name                  *)
                     string* (* first considered symbol          *)
                     string* (* second considered symbol         *)
                     string* (* variable for father's attribute  *)
                     string* (* variable for the received result *)
                     string* (* variable for the own attribute   *)
                     term    (* body of the rule                 *)
 | UP_RULE        of string* (* production name                  *)
                     string* (* variable for the received result *)
                     string* (* variable for the own attribute   *)
                     term;   (* body of the rule                 *) 

signature SPECIFICATION =
sig

(* grammar *)

val G : {productions :{name:string,left:string,right:string list} list,
         startsymbol :string,
         terminals   :string list};

(* attributation *)

val attribute_sets       : {name : string,
                            ty   : hol_type} list;
val start_set            : string;
val result_set           : string;
val init_attribute       : term;
val attributation_rules  : {operation : string,
                           r : {lhs : {var : string, set : string} list,
                                rhs : {body : term, set : string}
                               } list,
                           s : {lhs : {var : string, set : string} list,
                                rhs : {body : term, set : string}
                               } list
                           } list;
val prefix_rules         : string;
val prefix_attributation : string;
val simplify_attributation_CONV  : conv;

(* code generation *)

val target_type               : hol_type;
val init_target_value         : term;
val prefix_local_translation  : string;
val prefix_translation        : string;
val translation_rules         : translation_rule list;
val simplify_translation_CONV : conv;

(* attributation + code generation *)

val compilation : string;

end;

signature COMPILER =
sig

(* attributation *)

val mk_attributation : term -> term

val attributation_CONV : int list -> conv;

(* code generation *)

val mk_translation : term -> term

val translation_CONV : conv;

(* attributation + code generation *)

val mk_compilation : term -> term
val compilation_CONV : int list -> conv;

end;
