(************************ generator.sml *********************************)
(*                                                                      *)
(* Author: Ralf Reetz                                                   *)
(* Date:   27.9.1994                                                    *)
(*                                                                      *)
(* Description:                                                         *)
(*                                                                      *)
(*   see generator.sig. Because handling of an raise HOL_ERR raised by  *)
(*   a functor like new_compiler_definition here, IO is used to emit    *)
(*   error messages.                                                    *)
(*                                                                      *)
(* Used files:     generator.sig                                        *)
(* Used modules:   IO, multiple_rec_spec                                *)
(* Used theories:  apply_f_until_finished                               *)
(* Used libraries: mutrec, taut                                         *)
(*                                                                      *)
(************************************************************************)

functor new_compiler_definition
(structure specification : SPECIFICATION) : COMPILER =
struct

exception new_compiler_definition_error;

(*------- checking draftmode and adding needed stuff------------------------*)

val _ = if draft_mode() then
         new_parent "apply_f_until_finished"
        else
         (
          Portable.output
             (Portable.std_out,"Error in new_compiler_definition:\n"^
          "HOL not in draft mode. Make a new theory.\n")
          ;
          raise new_compiler_definition_error
         );

val theory_name = current_theory();

(*------------ preparing the input -----------------------------------------*)

open specification;

val T = #terminals G;
val S = #startsymbol G;
val P = #productions G;

val attr_name = prefix_attributation^"_attribute_sets";

(*------------ utilities ---------------------------------------------------*)

(*
  Global Input:
   attribute_sets
  Input:
   name of an attribute set
  Output:
   attribute type of the attribute set
*)
fun search_attr_ty search_name =
 let
  fun do_it [] =
   raise new_compiler_definition_error
  | do_it ({name : string, ty : hol_type}::t) =
   if search_name=name then ty else do_it t
 in
  do_it attribute_sets
 end;

(*------------checking input------------------------------------------------*)

(*
  Input:
   a list of strings
  Output:
   the first string of the input list, which is a name of a constant, the
   empty list if there's no such constant
*)
fun list_is_constant [] = 
 []
| list_is_constant (name::name_list) =
 if is_constant name then
  [name]
 else
  list_is_constant name_list;

(*--- check the attribute sets ---*)

val _ =
 let
  (*
    Input:
     list of attribute sets
    Output:
     a name of an attribute set, if it appears twice in the input;[] otherwise
  *)
  fun name_unique [] =
   []
  |   name_unique ({name:string,ty:hol_type}::t) =
   if mem name (map (#name) t) then
    [name]
   else
    name_unique t
  (*
    Global Input:
     attribute_sets, start_set, init_attribute, result_set, attr_name
    Output:
     raises new_compiler_definition_error if:
     a) start_set is not a member of attribute_sets
     b) result_set is not a member of attribute_sets
     c) the hol type of init_attribute is not the type of the start_set
     d) name for an attribute set appears twice in attribute_set
     e) name for an attribute set is already a constant
     f) is_<name> for an attribute set is already a constant
     g) attr_name is already a type
  *)
  fun check_sets () =
   if not(mem start_set (map (#name) attribute_sets)) then
    (
     IO.output(IO.std_out,"Error in new_compiler_definition:\n"^
     "no hol_type supplied for the starting attribute set "^start_set^
     ".\nCheck attribute_sets=... and start_set=...\n")
     ;
     raise new_compiler_definition_error
    )
   else if not(mem result_set (map (#name) attribute_sets)) then
    (
     IO.output(IO.std_out,"Error in new_compiler_definition:\n"^
     "no hol_type supplied for the final attribute set "^result_set^
     ".\nCheck attribute_sets=... and result_set=...\n")
     ;
     raise new_compiler_definition_error
    )
   else if not(mem {name=start_set,ty=(type_of init_attribute)}
   attribute_sets) then
    (
     IO.output(IO.std_out,"Error in new_compiler_definition:\n"^
     "hol_type of the initial attribute is not consistent with the"^
     " supplied\n starting attribute set. Check attribute_sets=..."^
     " and init_attribute=...\n")
     ;
     raise new_compiler_definition_error
    )
   else if not((name_unique attribute_sets)=[]) then
    (
     IO.output(IO.std_out,"Error in new_compiler_definition:\n"^
     "Attribute set "^(hd (name_unique attribute_sets))^
     " is defined twice.\nCheck attribute_sets=...\n")
     ;
     raise new_compiler_definition_error
    )
   else if not((list_is_constant(map (#name) attribute_sets))=[]) then
    (
     IO.output(IO.std_out,"Error in new_compiler_definition:\n"^
     "Attribute set "^(hd(list_is_constant(map (#name) attribute_sets)))^
     " is already a name of a constant. Choose another name.\n")
     ;
     raise new_compiler_definition_error
    )
   else if not
   ((list_is_constant(map (fn x => "is_"^(#name x)) attribute_sets))=[]) then 
    (
     IO.output(IO.std_out,"Error in new_compiler_definition:\n"^
     (hd(list_is_constant(map (fn x => "is_"^(#name x)) attribute_sets)))^
     " is already a name of a constant.\n Choose another name for the"^
     " according attribute set.\n")
     ;
     raise new_compiler_definition_error
    )
   else if is_type attr_name then
    (
     IO.output(IO.std_out,"Error in new_compiler_definition:\n"^
     attr_name^" is already a type.\n Choose another name for "^
     "prefix_attributation.\n")
     ;
     raise new_compiler_definition_error
    )
   else
    ()
 in
  check_sets()
 end;

(*--- check the rules ---*)

val _ =
 let
  val production_operations = map (#name) P
  (*
    Global Input:
     T,P, production_operations 
    Input:
     list of rules
    Output:
     raises an new_compiler_definition_error if:
     a) there's no receiving rule for a terminal t
     b) there's a synthesising rule for a terminal t
     c) there's not a receiving or a synthesising rule for a production
     d) operation is not a terminal or a production
  *)
  fun check_existing [] =
   ()
  |   check_existing ({operation : string,
                        r : {lhs : {var : string, set : string} list,
                             rhs : {body : term, set : string}
                            } list,
                        s : {lhs : {var : string, set : string} list,
                             rhs : {body : term, set : string}
                            } list
                       }::rule_list) =
   if mem operation T then
    (*--- checking terminal ---*)
    if r=[] then
     (
      IO.output(IO.std_out,"Error in new_compiler_definition:\n"^
      "There is no receiving rule for terminal "^operation)
      ;
      raise new_compiler_definition_error
     )
    else if not(s=[]) then
     (
      IO.output(IO.std_out,"Error in new_compiler_definition:\n"^
      "there is  at least one synthesising rule for terminal "^operation^
      ".\nJust remove all synthesing rules for terminals.")
      ;
      raise new_compiler_definition_error
     )
    else
     check_existing rule_list
   else if mem operation production_operations then
    (*--- checking production ---*)
    if (r=[]) andalso (s=[]) then
     (
      IO.output(IO.std_out,"Error in new_compiler_definition:\n"^
      "there is no synthesising rule and there is no receiving rule for"
      ^"for production "^operation^".\n"
      ^"Add at least one synthesing rule or one receiving rule for"
      ^"for production "^operation^".")
      ;
      raise new_compiler_definition_error
     )
    else
     check_existing rule_list      
   else
    (
     IO.output(IO.std_out,"Error in new_compiler_definition:\n"^
     "operation "^operation^" is not (a terminal or a production).")
     ;
     raise new_compiler_definition_error
    )
  (*
    Global Input:
     search_attr_ty
    Input:
     list of rules
    Output:
     raises an new_compiler_definition_error if:
     a) number of free variables of lhs of an srule is the number of
        symbols of the right side of the according production plus 1
     b) the free variables of rhs all appears on the lhs of a rule
     c) type of the right side is equal to the hol type of the supplied set
     d) number of free variables of lhs of an rrule is 2
  *)
  fun check_consistent [] =
   [()]
  |   check_consistent ({operation : string,
                        r : {lhs : {var : string, set : string} list,
                             rhs : {body : term, set : string}
                            } list,
                        s : {lhs : {var : string, set : string} list,
                             rhs : {body : term, set : string}
                            } list
                       }::rule_list) =
   let
    fun check_a {lhs : {var : string, set : string} list,
                 rhs : {body : term, set : string}} =
     let
      fun find_length [] =
       raise new_compiler_definition_error
      | find_length ({name:string,left:string,right:string list}::pl) =
       if name = operation then
        length right
       else
        find_length pl
     in
      if (length lhs) = ((find_length P)+1) then
       ()
      else
        (
         IO.output(IO.std_out,"Error in new_compiler_definition:\n"^
         "The number of the free variables of the left side of a\n"^
         "synthesising rule for operation "^operation^" is not equal to\n"^
         "the number of symbols of the right side of the according\n"^
         "production rule plus 1.\n")
         ;
         raise new_compiler_definition_error
        )        
     
     end
    fun check_b {lhs : {var : string, set : string} list,
                 rhs : {body : term, set : string}} =
     let
      (*
        Algorithm:
         because check_a is called before check_b, we are already sure, that
         a hol type was supplied for every variable of the left side
      *)
      fun var_2_term {var : string, set : string} =
       mk_var{Name=var,Ty=(search_attr_ty set)}
      val lvars = map var_2_term lhs
      fun do_it [] =
       ()
      | do_it (t::t_list) =
       if mem t lvars then
        do_it t_list
       else
        (
         IO.output(IO.std_out,"Error in new_compiler_definition:\n"^
         "The free variable "^(term_to_string t)^" on the right side\n"^
         "of a rule for operation "^operation^" is not a free variable\n"^
         "on the left side of the rule.\n")
         ;
         raise new_compiler_definition_error
        )        
     in
      do_it (free_vars(#body rhs)) 
     end
    fun check_c {lhs : {var : string, set : string} list,
                 rhs : {body : term, set : string}} =
     let
      val ty = (search_attr_ty (#set rhs)) handle _ =>
                (
                 IO.output(IO.std_out,"Error in new_compiler_definition:\n"^
                 "The attribute set "^(#set rhs)^", which appears for the\n"^
                 "right side of a rule for operation "^operation^", is not\n"^
                 "a member of attribute_set, i.e. there's no hol type\n"^
                 "supplied for this set.\n")
                 ;
                 raise new_compiler_definition_error
                )
      in
       if ty = type_of (#body rhs) then
        ()
       else
        (
         IO.output(IO.std_out,"Error in new_compiler_definition:\n"^
         "The type of the attribute set "^(#set rhs)^" for the right side\n"^
         "of a rule for operation "^operation^" is not equal to the type\n"^
         "of the body:\n"^
         term_to_string (#body rhs))
         ;
         raise new_compiler_definition_error
        )      
     end
    (*
      Algorithm:
       number of free variables of lhs and rhs are always equal, ensured by
       calling check_a/b/c before
    *)
    fun check_d {lhs : {var : string, set : string} list,
                 rhs : {body : term, set : string}} =
     if (length lhs) = 2 then
      ()
     else
      (
       IO.output(IO.std_out,"Error in new_compiler_definition:\n"^
       "The number of free variables in a receiving rule for operation\n"^
       operation^" with body:\n"^
       (term_to_string (#body rhs))^"\nis not 2.")
       ;
       raise new_compiler_definition_error
      ) 
   in
    map check_a s;
    map check_b r;
    map check_b s;
    map check_c r;
    map check_c s;
    map check_d r
   end
 in
  check_existing attributation_rules;
  check_consistent attributation_rules
 end;

(*------------some useful stuff------------------------------------------*)

(*---converting a type to a string regardless !Globals.max_print_depth---*)

fun type_2_string t = 
  System.PrettyPrint.pp_to_string 80 (fn p => (fn h => pp_type p h ~1)) t;

(*---converting a natural number into a string---*)

fun int_2_string n =
 let
  fun do_it n =
   if n=0 then
    ""
   else
    (do_it (n div 10))^(chr((n mod 10)+48))
 in
  if n=0 then "0" else do_it n
 end;

(*--- ---*)

fun nPrefix n = 
 if n=1 then 
  [Prefix] 
 else 
  Prefix::(nPrefix (n-1));

(*--- ---*)

(*
  Input:
    a theorem th as returns by define_mutual_functions,
    an arbitrary conversion and a term of one of those mutually recursive
    types as for define_mutual_functions
  Output:
    the application of the functions defined in th to the given
    term, simplified by the supplied conversion applied after every
    specialisation step
  Algorithm:
    bottom-up specialisation over the tree-kind-structure of the mutally
    recurcive types.
*)
fun mutrec_BETA_THEN_APPLY_CONV th simplify_attributation_CONV t =
  let
    (*
      Input:
        a term of the form --`constructor x1 ... xn`-- 
      Output:
        the term --`constructor`--
    *)
    fun dest_constructor t =
     if is_comb t then
      dest_constructor (#Rator(dest_comb t))
     else
      t
    (*
      Input:
        the theorem th, which is a conjunction of theorems of the
        form |- x1 x2 ... xn.F (constructor x1 ... xn) =...
      Output:
        the search structure for specialisation stored in def_data:
        list of pairs: a constructor with the according definitional theorem 
    *)
    fun build_def_data_entry th =
     let
      (*
        Input:
         a term
        Output:
         strips away all leading all-quantifiers
      *)
      fun dest_list_forall t =
       if is_forall t then 
        dest_list_forall(#Body(dest_forall t))
       else t
      val t1 = dest_list_forall (concl th)
      val t2 = if is_eq t1 then
                #Rand(dest_comb(#lhs(dest_eq t1)))
               else
                raise HOL_ERR{message=
                 "Supplied definitional theorem doesn't fit:\n"^
                 (term_to_string t1)^" hasn't an equation",
                 origin_function=
                 "mutrec_BETA_THEN_APPLY_CONV.build_def_data_entry",
                 origin_structure="generator"}
    in
     (dest_constructor t2,th)
    end
    val def_data = map build_def_data_entry (CONJUNCTS th)
    (*
      Input:
        a term of the form --`constructor x1 x2 x3 ... xn`--
      Output:
        list of terms x1 x2 ... xn
    *)
    fun split_cons t =
      if is_comb t then
        append
          (split_cons (#Rator(dest_comb t)))
          [#Rand(dest_comb t)]
      else
        []
    (*
      Global Input:
       def_data
      Input:
        a term t of the form --`constructor x1 x2 ... xn`--
      Output: 
        a theorem out of def_data, which is specialised with t
      Algorithm:
        search in def_data for a theorem with the same constructor as the 
        constructor of the term t. This theorem will then be specialised.
    *)
    fun spec t =
      let
        val term_constructor = dest_constructor t
        fun search_and_spec [] =
         raise HOL_ERR{message="Subterm\n"^
                               (term_to_string t)^
                  "\nof the supplied term doesn't fit the supplied theorem",
                       origin_function=
                       "mutrec_BETA_THEN_APPLY_CONV.search_and_spec",
                       origin_structure="generator"}
        | search_and_spec ((constructor,th)::tail) =
          if term_constructor=constructor then
           ISPECL (split_cons t) th
          else
           search_and_spec tail
      in
       search_and_spec def_data
      end
    (*
      Global Input:
        def_data
      Input:
        a term t
      Output:
        true iff the t has the form --`constructor x1 x2 x3 ... xn`--
      Algorithm:
        searches in def_data, whether the constructor of t is a member of
        def_data
    *)
    fun is_constructed t =
     let
      val term_constructor = dest_constructor t
      fun search [] = 
       false
      | search ((constructor,th)::tail) =
       (term_constructor=constructor)orelse(search tail)
     in
      search def_data
     end
    (*
      a rule - haven't replace SUBS with a specialised own one yet...
    *)
    fun SUBS_THEN_APPLY_LIST [] th =
     th
    | SUBS_THEN_APPLY_LIST (head::tail) th =
     SUBS_THEN_APPLY_LIST tail
     (RIGHT_CONV_RULE simplify_attributation_CONV (SUBS [head] th))
    (*
      the final function: bottom-up specialisation and simplification
    *)
    fun spec_bottom_up t =
     if is_constructed t then
      let
       val sub_terms = filter is_constructed (split_cons t)
       val sub_thms  = map spec_bottom_up sub_terms
       val top_thm   = spec t
      in
       SUBS_THEN_APPLY_LIST sub_thms top_thm
      end
     else
      ALL_CONV t
 in
  if is_constructed t then
   spec_bottom_up t
  else
   raise HOL_ERR{message=(term_to_string t)^
                 "\ndoesn't fit the supplied theorem\n"^
                 (term_to_string (concl th)),
                 origin_function="mutrec_BETA_THEN_APPLY_CONV",
                 origin_structure="new_compiler_definition"}
 end;

(*------------preparing the input-----------------------------------------*)

(* 
 V contains a list of variables with its production rule, i.e. the
 variable appears on the left side of the production rules. Since 
 there are no useless variables, every variable appears on a left
 side of some production rule.
*)
val V = 
 let
  (*
    Input:
     a production rule
    Output:
     a string containing the production rule
  *)
  fun rule2string {name=n,left=A,right=alpha} =
   let
    (*
     Input:
      list of strings
     Output:
      a string containing all supplied strings, seperated by a " "
    *)
    fun flat [] =
     ""
    | flat (h::t) =
     h^" "^(flat t)
   in
    n^" : "^A^" -> "^(flat alpha)
   end
  (*
    Input:
     a variable A, a production rule p with A on the left side and a list
    Output:
     inserts A if and only if A is not already in the supplied list and
     A is not a terminal. If A is in the list, it inserts the production
     rule for A
  *)
  fun insert A p l = 
   if (mem A T) then
    raise HOL_ERR{message=(A^" as the left side of production rule\n"^
                          (rule2string p)^"\nis a terminal"),
                  origin_function="insert",
                  origin_structure="generator"}
   else if (#right p)=[] then
    raise HOL_ERR{message=("Right side of production rule\n"^
                          (rule2string p)^"\nis empty"),
                  origin_function="insert",
                  origin_structure="generator"}
   else
    let
     fun do_insert [] =
      [(A,[p])]
     | do_insert (h::t) =
      if A=(fst h) then
       (*
         attention: the order of inserting p is relevant!
       *)
       (A,(append (snd h) [p]))::t
      else
       h::(do_insert t)
    in
     do_insert l
    end  
  fun compute_V [] l = 
   l
  | compute_V (p::pl) l = 
   compute_V pl (insert (#left p) p l)
 in
  compute_V P []
 end;

(*-----------generating mutually recursive types specification------------*)

(*
 convention:
 --`TY_x`-- stands for the type of productions rule for variable/terminal x
*)

(*
  Input:
   list of terminal names
  Output:
   type specification for the terminals
*)
fun gen_terminal_spec [] =
 []
|gen_terminal_spec (h::t) =
 {type_name    = "TY_"^h,
  constructors =
   [{name     = h,
     arg_info = [TypeInfo.existing (==`:'a`==)]}]}
 ::(gen_terminal_spec t);

(*
  Input:
   a list of variables and terminals
  Output:
   list of type names for the given variables and terminals
*)
fun gen_arg_info [] =
 []
| gen_arg_info (h::t) =
 (TypeInfo.being_defined ("TY_"^h))::(gen_arg_info t);

(*
  Input:
   a list of production rules
  Output:
   constructor specification for function gen_variable_spec
*)
fun gen_constructors [] =
 []
| gen_constructors ({name=n,left=A,right=Al}::t) =
 {name=n,
  arg_info = (TypeInfo.existing (==`:'a`==)::(gen_arg_info Al))}
 ::(gen_constructors t);

(*
  Input:
   a list of variables with its production rule, i.e. the
   variable appears on the left side of the production rules.
  Output:
   type specification for the variables
*)
fun gen_variable_spec [] =
 []
|gen_variable_spec ((A,pl)::t) =
 {type_name    = "TY_"^A,
  constructors = (gen_constructors pl)}
 ::(gen_variable_spec t);

structure ty_spec  =
struct

structure TypeInfo = TypeInfo;

open TypeInfo;

val mut_rec_ty_spec =
 append (gen_terminal_spec T) (gen_variable_spec V);

end;

structure DerivationTreeDef =
 MutRecDefFunc (structure ExtraGeneralFunctions = ExtraGeneralFunctions
                structure MutRecTyInput = ty_spec);

val DerivationTree_existence_thm =
 save_thm("DerivationTree_existence_thm", 
  DerivationTreeDef.New_Ty_Existence_Thm);

val DerivationTree_induction_thm =
 save_thm("DerivationTree_induction_thm", 
  DerivationTreeDef.New_Ty_Induct_Thm);

val DerivationTree_uniqueness_thm =
 save_thm("DerivationTree_thm", 
  DerivationTreeDef.New_Ty_Uniqueness_Thm);

structure DerivationTreeConsThms = ConsThmsFunc(DerivationTreeDef);

val DerivationTree_constructors_one_one =
 save_thm("DerivationTree_constructors_one_one",
  DerivationTreeConsThms.mutual_constructors_one_one);

val DerivationTree_constructors_distinct =
 save_thm("DerivationTree_constructors_distinct",
  DerivationTreeConsThms.mutual_constructors_distinct);

val DerivationTree_cases = 
 save_thm("DerivationTree_cases",
  DerivationTreeConsThms.mutual_cases);

(*-------new_attributation_definition---------------------------------------*)

exception internal_error;

(*--- utility functions ---*)

(*
  Global Input:
   prefix_rules
  Input:
   an operation and a string rs, which should be either "r" or "s"
  Output:
   the name of a synthezising ("s") or receiveing ("r") h for operation
*)
fun mk_hname operation rs =
 prefix_rules^"_"^rs^"_"^operation;

(*
  Global Input:
   prefix_rules
  Input:
   an operation and a string rs, which should be either "r" or "s"
  Output:
   the name of the applicability of synthezising ("s") or receiveing ("r") h 
   for operation
*)
fun mk_haname operation rs =
 "is_"^prefix_rules^"_"^rs^"_"^operation;

(*
  Global Input:
   attributation_rules
  Input:
   an operation
  Output:
   the rules supplied for that operation
*)
fun search_rules search_operation =
 let
  fun do_it [] =
   raise HOL_ERR
   {origin_function  ="new_attributation_definition",
    origin_structure ="generator",
    message          =
    ("No attributation rules supplied for operation "^search_operation)}
  | do_it ({operation : string,
                    r : {lhs : {var : string, set : string} list,
                         rhs : {body : term, set : string}
                        } list,
                    s : {lhs : {var : string, set : string} list,
                         rhs : {body : term, set : string}
                        } list}::rule_list) =
   if search_operation=operation then 
    if (r=[]) andalso (s=[]) then
     raise HOL_ERR
     {origin_function  ="new_attributation_definition",
      origin_structure ="generator",
      message          =
      ("No attributation rules supplied for operation "^search_operation)}
    else
     {operation=operation,r=r,s=s}
   else 
    do_it rule_list
 in
  do_it attributation_rules
 end;

(*--- type definition for the attribute sets ---*)

val attr_axiom = 
 let
  (*
    Global Input:
     attribute_sets, attr_name
    Output:
     recursive theorem for attribute sets
    Used Functions:
     nPrefix
  *)
  fun define_attribut_sets () =
   let
    fun set_2_string {name :string, ty : hol_type} =
     name^" of "^(type_to_string ty)
    fun do_it (h1::h2::t) =
     set_2_string h1^"|"^(do_it (h2::t))
    | do_it [h] =
     set_2_string h
   in
    define_type
     {name      = attr_name,
      fixities  = (nPrefix (length attribute_sets)),
      type_spec = [QUOTE (attr_name^"="^(do_it attribute_sets))]}
   end
 in
  define_attribut_sets ()
 end;

val attr_ty = mk_type{Args= [], Tyop = attr_name};

(*--- utilities, continued ---*)

(*
  Global Input:
   attr_ty
  Input:
   production rule, attribute type
  Output:
   let the rule be "p:A->B...Z", the attribute type "ty_a", then
   for term --`p (x1:ty_a) (x2:ta TY_B) ... (x26:ta TY_Z) : ta TY_A`--,
   the list [--`p`--,--`x1`--,...,--`x26`--] is returned
  Used Functions:
   int_2_string
*)
fun mk_parameter {name:string,left:string,right:string list} ty_a = 
 let
  (*
    Input:
     right side of a production rule, attribute type
    Output:
     let the right side be ["B",...,"Z"], the attribute type "ty_a", then
     [--`(x1:ty_a)`--,--`(x2:ty_a TY_B)`--,...,--`(x26:ty_a TY_Z)`--]
  *)
  fun mk_parameter1 right ty_a = 
   let
    fun mk_t1 n [] =
     []
    | mk_t1 n (symbol::symbol_list) =
     let
      val ty1 = mk_type{Args = [ty_a], Tyop = ("TY_"^symbol)}
     in
      (mk_var{Name = "x"^(int_2_string n), Ty = ty1})
      ::(mk_t1 (n+1) symbol_list)
     end
    val t1 = mk_t1 2 right
    val t2 = mk_var{Name = "x1", Ty = ty_a} 
   in
    t2::t1
   end 
  (*--- ---*)
  val t1  = mk_parameter1 right ty_a
  val ty1 = map (fn t => #Ty(dest_var t)) t1
  fun mk_ty2 [] =
   mk_type{Args = [ty_a], Tyop = ("TY_"^left)}
  | mk_ty2 (ty::ty_list) =
   (mk_type{Args = [ty,(mk_ty2 ty_list)], Tyop = "fun"})
  val t2  = mk_const{Name = name, Ty = (mk_ty2 ty1)}
 in
  t2::t1
 end;

(*
  Global Input:
   attr_ty
  Input:
   natural number n
  Output:
   ==`:attr_ty->attr_ty->...->attr_ty`==, where attr_ty occurs n+1
*)
fun mk_ty_h n =
 if n>0 then
  mk_type{Args=[attr_ty,mk_ty_h (n-1)],Tyop="fun"}
 else
  attr_ty;

(*--- definition of the rules ---*)

(*
  Global Input:
   prefix_attributation, attr_name, P, T, internal_error
  Used Functions:
   search_attr_ty, mk_hname
*)
val h_thms =
 let
  fun mk_h rs operation =
   let
    (*
      Global Input:
       prefix_attributation, search_attr_ty, attr_name
      Input:
       name of an attribute set
      Output:
       let name be "n", its attribute type be "ty", prefix_attributation be
       "h". Then the type constructor --`n:ty -> h_attribute_sets`-- is 
       returned.
    *)
    fun mk_attr_cstr name =
     let
      val ty1 = mk_type{Args = [],Tyop = attr_name}
      val ty2 = search_attr_ty name
     in
      mk_const{Name = name, Ty = (mk_type{Args = [ty2,ty1], Tyop = "fun"})}
     end
    (*
      Global Input:
       rs should be "r" or "s"
      Input:
       a rule
      Output:
       definitional equation of h for that rule
    *)
    fun mk_eq_h {lhs : {var : string, set : string} list,
                        rhs : {body : term, set : string}} =
     let
      (*
        Global input:
         operation
        Input:
         parameter of a rule
        Output:
         let var be "a", set be "M". Then --`M a`-- is returned
      *)
      fun mk_para {var : string, set : string} =
       mk_comb{Rator=(mk_attr_cstr set),
               Rand =(mk_var{Name=var,Ty=(search_attr_ty set)})}
      (*
        left side
      *)
      val t1 = map mk_para lhs
      val t2 = mk_hname operation rs
      val ty = mk_ty_h (length t1)
      val t3 = mk_var{Name = t2, Ty = ty}
      val t4 = list_mk_comb (t3,t1)
      (*
        right side
      *)
      val t5 = mk_attr_cstr (#set rhs)
      val t6 = mk_comb{Rator = t5, Rand = (#body rhs)}
     in
      mk_eq{lhs = t4, rhs = t6}
     end
     (*
       save the rules here
     *)
     val the_rules = search_rules operation
   in
    if rs = "r" then
     if (#r the_rules) = [] then
      raise internal_error
     else
      list_mk_conj(map mk_eq_h (#r the_rules))
    else
     if (#s the_rules) = [] then
      raise internal_error
     else
      list_mk_conj(map mk_eq_h (#s the_rules))
   end
  (*
    Global Input:
     attr_axiom, mk_hname
    Input:
     rs should be "r" or "s", a list of definitional terms for rules
     and, respectively, a list of symbols
    Output:
     definitions are made, the list of definitional theorems returned
  *)
  fun define [] =
   []
  | define ((def_term,operation,rs)::rest_list) =
   (multiple_rec_spec.new_multiple_recursive_specification
    {name      = (mk_hname operation rs),
     rec_axiom = attr_axiom,
     def       = def_term})  
   ::(define rest_list)
  (*
    Input:
     a list of operations
    Output:
     the definitional terms of the synthesysing or receiving h's of the
     operations
    Algorithm:
     Note that there's at least a synthesysing or a receiving h, because
     otherwise, a HOL_ERROR was raised before. But one of the
     synthesysing or receiving might be missed. Here, the internal
     error was raised by mk_h
  *)
  fun list_mk_h [] =
   []
  | list_mk_h (h::t) =
   append
   (append
   ([(mk_h "r" h,h,"r")] handle internal_error => [])
   ([(mk_h "s" h,h,"s")] handle internal_error => []))
   (list_mk_h t)
 in
  define (list_mk_h (append T (map (#name) P)))
 end;

(*--- definition of mapping a function over the attributes ---*)

  val attr_map_thm =
   let
    (*
      Global Input:
       T, V, prefix_attributation
      Output:
       defines a function, which applies a supplied functions to all attributes 
       of a derivation tree 
    *)
    fun define_map () =
     let
      (*
        prelimenary stuff
      *)
      val ty_a  = (==`:'a`==)
      val ty_b  = (==`:'b`==)
      val ty_ab = (==`:'a->'b`==)
      val t_f   = (--`f:'a->'b`--)
      (*
        Global Input:
         t_f, ty_a, ty_b
        Input:
         terminal
        Output:
         mapping for a terminal. For terminal "t", it has the form:
         --`map_t (t (A_t:'a)) = \f:'a->'b.t (f A_t)`--
      *)
      fun mk_map_terminal t =
       let
        (*
          left side of the definitional equation
        *)
        val t1  = mk_var{Name=("A_"^t),Ty=ty_a}       (* A_t           *)
        val ty1 = mk_type{Args=[ty_a],Tyop=("TY_"^t)} (* :'a TY_t      *)
        val ty2 = mk_type{Args=[ty_a,ty1],Tyop="fun"} (* :'a->'a TY_t  *)
        val t2  = mk_const{Name=t,Ty=ty2}             (* t:'a->'a TY_t *)
        val t3  = mk_comb{Rator=t2,Rand=t1}           (* t A_t         *)
        val ty3 = mk_type{Args=[ty_b],Tyop=("TY_"^t)} (* :'b TY_t      *)
        val ty4 = mk_type{Args=[ty_ab,ty3],Tyop="fun"}
        val ty5 = mk_type{Args=[ty1,ty4],Tyop="fun"}
        val t4  = mk_var{Name=("map_"^t),Ty=ty5}      (* map_t         *)
        val t5  = mk_comb{Rator=t4,Rand=t3}           (* map_t (t A_t) *)
        (*
          right side of the definition equation
        *)
        val t6  = mk_comb{Rator=t_f,Rand=t1}          (* f A_t         *)
        val ty6 = mk_type{Args=[ty_b,ty3],Tyop="fun"} (* :'b->'b TY_t  *)
        val t7  = mk_const{Name=t,Ty=ty6}             (* t:'b->'b TY_t *)
        val t8  = mk_comb{Rator=t7,Rand=t6}           (* t (f A_t)     *)
        val t9  = mk_abs{Bvar=t_f,Body=t8}            (* \f.t (f A_t)  *)
       in
        mk_eq{lhs=t5,rhs=t9}
       end
      (*
        Global Input:
         ty_a, ty_b, t_f
        Input:
         variable and a list of productions, where the given variable is on the
         left side of the productions, which should not be empty.
        Output:
         map for the given variable.
      *)
      fun mk_map_variable (A,pl) =
       let
        val ty1 = mk_type{Args=[ty_a],Tyop=("TY_"^A)} (* :'a TY_A *)
        val ty2 = mk_type{Args=[ty_b],Tyop=("TY_"^A)} (* :'b TY_A *)
        val ty3 = mk_type{Args=[ty_ab,ty2],Tyop="fun"}
        val ty4 = mk_type{Args=[ty1,ty3],Tyop="fun"}
        val t1  = mk_var{Name=("map_"^A),Ty=ty4}      (* map_A    *)
        (*
          Input:
           production
          Output:
          let the production be "p:A->B...Z". Then the result has the form:
          --`map_A (p x1 x2 ... x27) = (p (f x1) (map_B x2) ... (map_Z x27))`--
        *)
        fun mk_equation p =
         let
          (*--- left side of a definitional translation equation ---*)
          val t2 = mk_parameter p ty_a
          val t3 = list_mk_comb(hd t2,tl t2)
          val t4 = mk_comb{Rator=t1,Rand=t3}
          (*--- right side of a definitional translation equation ---*)
          (*
            Global Input:
             ty_f
            Input:
             --`xn:'a TY_X`--
            Output:
             --`(map_X xn f):'b TY_X`--
          *)
          fun mk_t5 t =
           let
            val ty1 = #Ty(dest_var t)                     (* 'a TY_X  *)
            val X   = implode(tl(tl(tl(explode
                      (#Tyop(dest_type ty1))))))
            val ty2 = mk_type{Args=[ty_b],Tyop=("TY_"^X)} (* 'b TY_X  *)
            val ty3 = mk_type{Args=[ty_ab,ty2],Tyop="fun"}
            val ty4 = mk_type{Args=[ty1,ty3],Tyop="fun"}
            val t1  = mk_var{Name="map_"^X,Ty=ty4}        (* map_X    *)
            val t2  = mk_comb{Rator=t1,Rand=t}            (* map_X xn *)
           in
            mk_comb{Rator=t2,Rand=t_f}
           end 
          val t5  = map mk_t5 (tl(tl t2))
          val t6  = mk_comb{Rator=t_f,Rand=(hd(tl t2))}            (* f x1 *)
          val t7  = inst [{redex=(==`:'a`==),residue=(==`:'b`==)}] (* p    *)
                    (hd t2)
          val t8  = list_mk_comb(t7,t6::t5)
          val t9  = mk_abs{Bvar=t_f,Body=t8}
         in  
          mk_eq{lhs=t4,rhs=t9}
         end
       in
        map mk_equation pl
       end
     in
      define_mutual_functions 
      {rec_axiom = DerivationTree_existence_thm,
       name      = ("map_"^prefix_attributation^"_DEF"),
       fixities  = SOME (nPrefix ((length V)+(length T))),
       def       = 
       (list_mk_conj (append (map mk_map_terminal T)
       (flatten(map mk_map_variable V))))}
     end
   in
    define_map()
   end;

(*--- definition of attribute set membership testing ---*)

(*
  Global Input:
   attr_ty, attr_axiom, attribute_sets
*)
val is_set_thms =
 let
  fun merge_map f [] [] =
   []
  | merge_map f (h1::t1) (h2::t2) =
   (f h1 h2)::(merge_map f t1 t2)
  val t1 =
   let
    (*--- left side ---*)
    fun mk_t1 [] =
     []
    | mk_t1 ({name : string, ty : hol_type}::set_list) =
     mk_comb{Rator = (mk_const{Name=name,
                               Ty  =(mk_type{Args=[ty,attr_ty],
                                             Tyop="fun"})}),
             Rand  = (mk_var{Name="a_name",Ty=ty})}
     ::(mk_t1 set_list)
   in
    mk_t1 attribute_sets
   end
  val ty1 = mk_type{Args=[],Tyop="bool"}
  val ty2 = mk_type{Args=[attr_ty,ty1],Tyop="fun"}
  fun mk_t2 name =
   let
    val t2 = mk_var{Name="is_"^name,Ty=ty2}
   in
    map (fn tx => mk_comb{Rator=t2,Rand=tx}) t1
   end
  (*--- right side ---*)
  fun mk_t3 name1 [] =
   []
  | mk_t3 name1 ({name : string, ty : hol_type}::set_list) =
   (if name1=name then (--`T`--) else (--`F`--))
   ::(mk_t3 name1 set_list)
  (*--- ---*)
  fun define_is_set [] =
   []
  | define_is_set ({name : string, ty : hol_type}::set_list) =
   let
    val t1 = merge_map (fn t1 => fn t2 => mk_eq{lhs=t1,rhs=t2}) 
             (mk_t2 name) (mk_t3 name attribute_sets)
    val t2 = list_mk_conj t1
   in
    (new_recursive_definition
    {name      = ("is_"^name),
     fixity    = Prefix,
     rec_axiom = attr_axiom,
     def       = t2})
    ::(define_is_set set_list)
   end
 in
  define_is_set attribute_sets
 end;

(*--- definition of the rule applicable test ---*)

(*
  Used Functions:
   search_rules, mk_haname, attr_ty, int_to_string, T, P
*)
val is_k_thms =
 let
  fun define_is_k operation rs rules =
   let
    (*--- left side ---*)
    (*
      Input:
       natural number
      Output:
       a list of length n of mutually distinct variables of type attr_ty
    *)
    fun mk_var_list n =
     if n>1 then
      mk_var{Name=("x"^(int_to_string n)),Ty=attr_ty}::(mk_var_list (n-1))
     else
      [mk_var{Name="x1",Ty=attr_ty}]
    (*
      Input:
       natural number
      Output:
       type ==`attr_ty->...->attry_ty->bool`==, where attr_ty appears n times
    *)
    fun mk_ty_is_h n =
     if n>0 then
      mk_type{Args=[attr_ty,mk_ty_is_h (n-1)],Tyop="fun"}
     else
      (==`:bool`==)
    val n_para = length(#lhs(hd rules))
    val ty1 = mk_ty_is_h n_para
    val t1  = mk_var{Name=(mk_haname operation rs),Ty=ty1}
    val t2  = mk_var_list n_para
    val t3  = list_mk_comb(t1,t2)
    (*--- right side ---*)
    fun mk_t4 [] [] =
     []
    | mk_t4 (t::t_list) ({var : string, set : string}::para_list) =
     let
      val ty1 = mk_type{Args=[],Tyop="bool"}
      val ty2 = mk_type{Args=[attr_ty,ty1],Tyop="fun"}
      val t1  = mk_const{Name="is_"^set,Ty=ty2}
     in
      (mk_comb{Rator=t1,Rand=t})::(mk_t4 t_list para_list)
     end
     fun mk_t5 [] =
      []
     | mk_t5 ({lhs : {var : string, set : string} list,
               rhs : {body : term, set : string}}::rule_list) =
      (list_mk_conj(mk_t4 t2 lhs))::(mk_t5 rule_list)
     val t5 = list_mk_disj(mk_t5 rules)
    in
     new_definition(mk_haname operation rs,mk_eq{lhs=t3,rhs=t5})
    end
  fun do_it operation =
   let
    val rules = search_rules operation
   in
    if (#r rules)=[] then
     [define_is_k operation "s" (#s rules)]
    else if (#s rules)=[] then
     [define_is_k operation "r" (#r rules)]
    else
     [define_is_k operation "r" (#r rules),
      define_is_k operation "s" (#s rules)]
   end
 in
  flatten(map do_it (append T (map (#name) P)))
 end;

(*--- definition of the attributation scheme ---*)

(*
  used Functions:
   mk_haname
*)
val k_thm =
 let
  fun define_attributation () =
   let
    (*
      Input:
       rs should be "s" or "r", operation, term list for attributes
    *)
    fun mk_rule_is_applicable rs operation t_list =
     let
      (*
        Input:
         natural number
        Output:
         type ==`attr_ty->...->attry_ty->bool`==, where attr_ty appears n 
         times 
      *)
      fun mk_ty_is_h n =
       if n>0 then
       mk_type{Args=[attr_ty,mk_ty_is_h (n-1)],Tyop="fun"}
       else
        (==`:bool`==)
      val ty1 = mk_ty_is_h (length t_list)
      val t1  = mk_const{Name=(mk_haname operation rs),Ty=ty1}
     in
      list_mk_comb(t1,t_list)
     end
    (*
      Global Input:
       prefix_attributation, attr_ty
      Input:
       terminal
      Output:
       attributation for a terminal. For terminal "t", 
       prefix_attributation "k", (mk_rule_is_applicable "r" t) 
       "rrule_is_applicable_t", prefix_rules "h", it has the form:
       --`k_t (t x1) = 
          \x.rrule_is_applicable_t => 
          (h_r_t x1 x,t (h_r_t x1 x))|(x1,t x1)`--
      Used Functions:
       mk_parameter, mk_rule_is_applicable, mk_hname, mk_ty_h
    *)
    fun mk_attributation_terminal t =
     let
      (*
        left side of the definitional equation
      *)
      val [t1,t2] = mk_parameter {name=t,left=t,right=[]} attr_ty
      val t3  = mk_comb{Rator=t1,Rand=t2}           (* t x1               *)
      val s1  = prefix_attributation^"_"^t
      val ty1 = hd(tl(#Args(dest_type(type_of t1))))
      val ty2 = mk_type{Args=[attr_ty,ty1], Tyop="prod"}
      val ty3 = mk_type{Args=[attr_ty,ty2], Tyop="fun"}
      val ty4 = mk_type{Args=[ty1,ty3], Tyop="fun"}
      val t4  = mk_var{Name=s1,Ty=ty4}              (* k_t                *)
      val t5  = mk_comb{Rator=t4,Rand=t3}           (* k_t (t x1)         *)
      (*
        right side of the definition equation
      *)
      val t6  = mk_var{Name="x",Ty=attr_ty}         (* x                  *)
      val t7  = mk_rule_is_applicable "r" t [t2,t6]
      val t8  = mk_const{Name = (mk_hname t "r"),
                         Ty   = (mk_ty_h 2)}        (* h_r_t              *)
      val t9  = list_mk_comb(t8,[t2,t6])            (* h_r_t x1 x         *)
      val t10 = mk_comb{Rator = t1, Rand = t9}      (* t(h_r_t x1 x)      *)
      val t11 = mk_pair{fst = t9, snd = t10}        (* (h_r_t 1x x,t(...))*)
      val t12 = mk_pair{fst = t2, snd = t3}         (* (x1, t x1)         *)
      val t13 = mk_cond{cond=t7,larm=t11,rarm=t12}  (* ...=>...|(x1,t x1) *)
      val t14 = mk_abs{Bvar=t6,Body=t13}
     in
      mk_eq{lhs=t5,rhs=t14}
     end
    (*
      Global Input:
       prefix_attributation
      Input:
       variable and a list of productions, where the given variable is on 
       the left side of the productions, which should not be empty.
      Output:
       attributation for a variable.
    *)
    fun mk_attributation_variable (A,pl) =
     let
      val ty1 = mk_type{Args=[attr_ty],Tyop=("TY_"^A)} (* :attr_ty TY_A *)
      val ty2 = mk_type{Args=[attr_ty,ty1],Tyop="prod"}
      val ty3 = mk_type{Args=[attr_ty,ty2],Tyop="fun"}
      val ty4 = mk_type{Args=[ty1,ty3],Tyop="fun"}
      val t1  = mk_var{Name=(prefix_attributation^"_"^A),Ty=ty4} (* k_A *)
      (*
        Global Input:
         attr_ty, t1
        Input:
         production
        Output:
        let the production be "p:A->B...Z", terminal "t", 
        prefix_attributation "k", (mk_rule_is_applicable rs p) 
        "rsrule_is_applicable_p", prefix_rules "h". If there are
        receiving and synthesising rules for p, then it has the form:
        --`k_A (p x1 x2 ... x27) = 
        \x.
        let
         xr = (rrule_is_applicable_p => h_r_p x x1|x1)
        in
         p (srule_is_applicable_p xr =>
         h_s_p xr (SND(k_B x2 xr)) ... (SND(k_Z x27 xr))|xr)
         (FST(k_B x2 xr)) ... (FST(k_Z x27 xr))`--
        if there are only receiving rules for p, then it has the form:
        --`k_A (p x1 x2 ... x27) = 
        \x.
        let
         xr = (rrule_is_applicable_p => h_r_p x x1|x1)
        in
         p xr (FST(k_B x2 xr)) ... (FST(k_Z x27 xr))`--
        if there are only synthesising rules for p, then it has the form:
        --`k_A (p x1 x2 ... x27) = 
        \x.p
         (srule_is_applicable_p x1 =>
         h_s_p x1 (SND(k_B x2 x1)) ... (SND(k_Z x27 x1))|x1)
         (FST(k_B x2 x1)) ... (FST(k_Z x27 x1))`--
      *)
      fun mk_equation p =
       let
        (*--- left side of a definitional translation equation ---*)
        val t2 = mk_parameter p attr_ty
        val t3 = list_mk_comb(hd t2,tl t2)
        val t4 = mk_comb{Rator=t1,Rand=t3}
        (*--- right side of a definitional translation equation ---*)
        val t5 = mk_var{Name="x",Ty=attr_ty} (* x *)
        val rules = search_rules (#name p)
        (*
          Global Input:
           prefix_attributation "k", attr_ty
          Input:
           --`xn:attr_ty TY_X`--, --`xi:attr_ty`--, false = FST, true = SND
          Output:
           --`FST (k_X xn xi)`-- or --`SND (k_X xn xi)`--
        *)
        fun mk_t6 b xi xn =
         let
          val ty1 = #Ty(dest_var xn)                   (*: attr_ty TY_X  *)
          val ty2 = mk_type{Args=[attr_ty,ty1], (* :attr_ty#attr_ty TY_X *)
                            Tyop="prod"}
          val ty3 = mk_type{Args=[attr_ty,ty2],Tyop="fun"}
          val ty4 = mk_type{Args=[ty1,ty3],Tyop="fun"}
          val X   = implode(tl(tl(tl(explode
                    (#Tyop(dest_type ty1))))))
          val t1  = mk_var{Name=(prefix_attributation^"_"^X),     (* k_X *)
                           Ty  =ty4}                       
          val t2  = mk_comb{Rator=t1,Rand=xn}                  (* k_X xn *)
          val t3  = mk_comb{Rator=t2,Rand=xi}               (* k_X xn xi *)
          val t4  = if b then
                     mk_const{Name="SND",
                            Ty  =(mk_type{Args=[ty2,ty1],Tyop="fun"})}
                    else
                     mk_const{Name="FST",
                            Ty  =(mk_type{Args=[ty2,attr_ty],Tyop="fun"})}
         in
          mk_comb{Rator=t4,Rand=t3}
         end
        val t7 =
         if (#r rules)=[] then
          let
           val t8  = map (mk_t6 false (hd(tl t2))) (tl(tl t2))  (* FST..  *)
           val t9  = map (mk_t6 true (hd(tl t2))) (tl(tl t2))   (* SND..  *)
           val t10 = mk_const{Name=(mk_hname (#name p) "s"),    (* h_s_p  *)
                              Ty  =(mk_ty_h (length t2-1))}
           val t11 = list_mk_comb(t10,((hd(tl t2))::t8))        (* h_s_p..*)
           val t12 = mk_rule_is_applicable "s" (#name p) (hd(tl t2)::t8)
           val t13 = mk_cond{cond=t12,larm=t11,rarm=(hd(tl t2))}
           val t14 = mk_var{Name="xs",Ty=attr_ty}               (* xr     *)
           val t15 = list_mk_comb(hd t2,t14::t9)
           val t16 = mk_pair{fst=t14,snd=t15}
           val t17 = mk_abs{Bvar=t14,Body=t16}
          in
           mk_let{func = t17, arg = t13}
          end
         else if (#s rules)=[] then
          let
           val t8  = mk_var{Name="xr",Ty=attr_ty}              (* xr     *)
           val t9  = map (mk_t6 true t8) (tl(tl t2))           (* FST..  *)
           val t10 = mk_rule_is_applicable "r" (#name p) 
                     [hd(tl t2),t5]
           val t11 = mk_const{Name=(mk_hname (#name p) "r"),   (* h_r_p  *)
                              Ty  =(mk_ty_h 2)}
           val t12 = list_mk_comb(t11,[hd(tl t2),t5])          (* h_r_p..*)
           val t13 = mk_cond{cond=t10,larm=t12,rarm=(hd(tl t2))} 
           val t14 = list_mk_comb(hd t2,t8::t9)
           val t15 = mk_pair{fst=t8,snd=t14}
           val t16 = mk_abs{Bvar=t8,Body=t15}
          in
           mk_let{func = t16, arg = t13}
          end
         else
          let
           val t8  = mk_var{Name="xr",Ty=attr_ty}              (* xr     *)
           val t9  = map (mk_t6 false t8) (tl(tl t2))          (* FST..  *)
           val t10 = map (mk_t6 true t8) (tl(tl t2))           (* SND..  *)
           val t11 = mk_const{Name=(mk_hname (#name p) "s"),   (* h_s_p  *)
                              Ty  =(mk_ty_h (length t2-1))}
           val t12 = list_mk_comb(t11,t8::t9)                  (* h_s_p..*)
           val t13 = mk_rule_is_applicable "s" (#name p) (t8::t9)
           val t14 = mk_cond{cond=t13,larm=t12,rarm=t8}
           val t15 = mk_var{Name="xs",Ty=attr_ty}              (* xs     *)
           val t16 = list_mk_comb(hd t2,t15::t10)
           val t17 = mk_pair{fst = t15, snd = t16}
           val t18 = mk_abs{Bvar = t15, Body = t17}
           val t19 = mk_let{func = t18, arg = t14}
           val t20 = mk_abs{Bvar = t8, Body = t19}
           val t21 = mk_rule_is_applicable "r" (#name p) ([hd(tl t2),t5])
           val t22 = mk_const{Name=(mk_hname (#name p) "r"),   (* h_r_p  *)
                              Ty  =(mk_ty_h 2)}
           val t23 = list_mk_comb(t22,[hd(tl t2),t5])          (* h_r_p..*)
           val t24 = mk_cond{cond=t21,larm=t23,rarm=(hd(tl t2))}
          in
           mk_let{func = t20, arg = t24}
          end
        val t8 = mk_abs{Bvar=t5,Body=t7}
       in
        mk_eq{lhs=t4,rhs=t8}
       end
     in
      map mk_equation pl
     end
   in
    define_mutual_functions 
    {rec_axiom = DerivationTree_existence_thm,
     name      = (prefix_attributation^"_DEF"),
     fixities  = SOME (nPrefix ((length V)+(length T))),
     def       = 
     (list_mk_conj (append (map mk_attributation_terminal T)
     (flatten(map mk_attributation_variable V))))}
   end
 in
  define_attributation()
 end;

(*--- definition of checking, wether attributation is completed ---*)

val is_result_thm =
 let
  fun define_is_result () =
   let
    (*
      prelimenary stuff
    *)
    val ty1 = mk_type{Args=[],Tyop="bool"}             (* :bool          *)
    val ty2 = mk_type{Args=[attr_ty,ty1],Tyop="fun"}   (* :attr_ty->bool *)
    val t1  = mk_const{Name=("is_"^result_set),Ty=ty2} (* is_result_set  *)
    (*
      Global Input:
       prefix_attributation, result_set, attr_ty, t1, ty1
      Input:
       terminal
      Output:
       mapping for a terminal. For terminal "t", prefix_attributation "k",
       result_set "result_set", it has the form:
       --`k_is_result_t (t A_t) = is_result_set A_t`--
    *)
    fun mk_k_is_result_terminal t =
     let
      (*
        left side of the definitional equation
      *)
      val t2  = mk_var{Name=("A_"^t),Ty=attr_ty}       (* A_t           *)
      val ty3 = mk_type{Args=[attr_ty],Tyop=("TY_"^t)} (* :attr_ty TY_t *)
      val ty4 = mk_type{Args=[attr_ty,ty3],Tyop="fun"}
      val t3  = mk_const{Name=t,Ty=ty4}                (* t             *)
      val t4  = mk_comb{Rator=t3,Rand=t2}              (* t A_t         *)
      val ty5 = mk_type{Args=[ty3,ty1],Tyop="fun"}
      val s1  = prefix_attributation^"_is_result_"^t 
      val t5  = mk_var{Name=s1,Ty=ty5}                 (* k_is_result_t *)
      val t6  = mk_comb{Rator=t5,Rand=t4}
      (*
        right side of the definition equation
      *)
      val t7  = mk_comb{Rator=t1,Rand=t2}
     in
      mk_eq{lhs= t6, rhs = t7}
     end
    (*
      Global Input:
       prefix_attributation, result_set, attr_ty, t1, ty1
      Input:
       variable and a list of productions, where the given variable is on 
       the left side of the productions, which should not be empty.
      Output:
       k_is_result_variable
    *)
    fun mk_k_is_result_variable (A,pl) =
     let
      val ty3 = mk_type{Args=[attr_ty],Tyop=("TY_"^A)} (* :attr_ty TY_A *)
      val ty4 = mk_type{Args=[ty3,ty1],Tyop="fun"}
      val s1  = prefix_attributation^"_is_result_"^A
      val t2  = mk_var{Name=s1,Ty=ty4}                 (* k_is_result_A *)
      (*
        Input:
         production
        Output:
         let the production be "p:A->B...Z". Then the result has the form:
         --`k_is_result_A (p x1 x2 ... x27) = 
           (is_result x1) /\ (k_is_result_B x2) ... (k_is_result_Z x27))`--
      *)
      fun mk_equation p =
       let
        (*--- left side of a definitional translation equation ---*)
        val t3 = mk_parameter p attr_ty
        val t4 = list_mk_comb(hd t3,tl t3)
        val t5 = mk_comb{Rator=t2,Rand=t4}
        (*--- right side of a definitional translation equation ---*)
        (*
          Global Input:
           attr_ty, prefix_attributation, ty2
          Input:
           --`xn:attr_ty`--
          Output:
           --`k_is_result xn`--
        *)
        fun mk_t6 t =
         let
          val ty5 = #Ty(dest_var t)                     (* attr_ty TY_X  *)
          val X   = implode(tl(tl(tl(explode
                    (#Tyop(dest_type ty5))))))
          val ty6 = mk_type{Args=[ty5,ty1],Tyop="fun"}
          val s1  = prefix_attributation^"_is_result_"^X
          val t1  = mk_var{Name=s1,Ty=ty6}              (* k_is_result_X *)
         in
          mk_comb{Rator=t1,Rand=t}
         end 
        val t6  = map mk_t6 (tl(tl t3))
        val t7  = mk_comb{Rator=t1,Rand=(hd(tl t3))}
        val t8  = list_mk_conj (t7::t6)
       in  
        mk_eq{lhs=t5,rhs=t8}
       end
     in
      map mk_equation pl
     end
   in
    define_mutual_functions 
    {rec_axiom = DerivationTree_existence_thm,
     name      = (prefix_attributation^"_is_result_DEF"),
     fixities  = SOME (nPrefix ((length V)+(length T))),
     def       = 
     (list_mk_conj (append (map mk_k_is_result_terminal T)
     (flatten(map mk_k_is_result_variable V))))}
   end
 in
  define_is_result()
 end;

(*--- definition of the complete attributation algorithm ---*)

(*
  Global Input:
   prefix_attributation, attribute_sets, result_set
  Output:
   definitional theorem for the attributation algorithm
  Used Functions:
   search_attr_ty
*)
  val (top_attributation_thm,REP_result_thm) =
   let
    val ty1 = mk_type{Args=[],Tyop=(prefix_attributation^"_attribute_sets")}
    val ty2 = search_attr_ty result_set
    val REP_result =
     let
      val ty3 = mk_type{Args=[ty1,ty2],Tyop="fun"}
      val ty4 = mk_type{Args=[ty2,ty1],Tyop="fun"}
      val t1  = mk_const{Name=result_set,Ty=ty4}         (* result_set     *)
      val t2  = mk_var{Name="x",Ty=ty2}                  (* x              *)
      val t3  = mk_var{Name=("REP_"^result_set),         (* REP_result_set *)
                       Ty  =ty3}
      val t4  = mk_comb{Rator=t1,Rand=t2}                (* result_set x   *)
      val t5  = mk_comb{Rator=t3,Rand=t4} (* REP_result_set (result_set x) *)
      val t6  = mk_eq{lhs=t5,rhs=t2}  (* REP_result_set (result_set x) = x *)
     in
      new_recursive_definition
      {name      = ("REP_"^result_set),
       fixity    = Prefix,
       rec_axiom = attr_axiom,
       def       = t6}
     end
    (* left side *)
    val ty3  = search_attr_ty start_set
    val ty4  = mk_type{Args=[ty3],Tyop=("TY_"^S)}
    val ty5  = mk_type{Args=[ty2],Tyop=("TY_"^S)}
    val ty6  = mk_type{Args=[ty4,ty5],Tyop="fun"}
    val t1   = mk_var{Name=prefix_attributation,Ty=ty6} (* k *)
    val t2   = mk_var{Name="x",Ty=ty4}                  (* x *)
    val t3   = mk_comb{Rator=t1,Rand=t2}                (* k x *)
    (* right side *)
    val ty7  = mk_type{Args=[ty3,attr_ty],Tyop="fun"}
    val t4   = mk_const{Name=start_set,Ty=ty7}                 (* start_set *)
    val ty8  = mk_type{Args=[attr_ty],Tyop=("TY_"^S)}
    val ty9  = mk_type{Args=[ty7,ty8],Tyop="fun"}
    val ty10 = mk_type{Args=[ty4,ty9],Tyop="fun"}
    val t5   = mk_const{Name="map_"^S,Ty=ty10}                     (* map_S *)
    val t6   = list_mk_comb(t5,[t2,t4])                (* map_S x start_set *)
    val t7   = mk_comb{Rator=t4,Rand=init_attribute}         (* start_set i *)
    val t8   = mk_var{Name="x1",Ty=ty8}                               (* x1 *)
    val ty11 = mk_type{Args=[attr_ty,ty8],Tyop="prod"}
    val ty12 = mk_type{Args=[attr_ty,ty11],Tyop="fun"}
    val ty13 = mk_type{Args=[ty8,ty12],Tyop="fun"}
    val t9   = mk_const{Name=(prefix_attributation^"_"^S),           (* k_S *)
                        Ty  =ty13}
    val t10  = list_mk_comb(t9,[t8,t7])             (* k_S x1 (start_set i) *)
    val ty14 = mk_type{Args=[ty11,ty8],Tyop="fun"}
    val t11  = mk_const{Name="SND",Ty=ty14}                          (* SND *)
    val t12  = mk_comb{Rator=t11,Rand=t10}     (* SND(k_S x1 (start_set i)) *)
    val t13  = mk_abs{Bvar=t8,Body=t12}    (* \x1.SND(k_S x1 (start_set i)) *)
    val ty15 = mk_type{Args=[],Tyop="bool"}
    val ty16 = mk_type{Args=[ty8,ty15],Tyop="fun"}
    val t14  = mk_const{Name=(prefix_attributation^"_is_result_"^S),
                        Ty  =ty16}                         (* k_is_result_S *)
    val ty17 = mk_type{Args=[ty8,ty8],Tyop="fun"}
    val ty18 = mk_type{Args=[ty17,ty17],Tyop="fun"}
    val ty19 = mk_type{Args=[ty16,ty18],Tyop="fun"}
    val t15  = mk_const{Name="apply_f_until_finished",Ty=ty19}
    val t16  = list_mk_comb(t15,[t14,t13,t6])
    val ty20 = mk_type{Args=[ty1,ty2],Tyop="fun"}
    val t17  = mk_const{Name=("REP_"^result_set),Ty=ty20} (* REP_result_set *)
    val ty21 = mk_type{Args=[ty20,ty5],Tyop="fun"}
    val ty22 = mk_type{Args=[ty8,ty21],Tyop="fun"}
    val t18  = mk_const{Name="map_"^S,Ty=ty22}                     (* map_S *)
    val t19  = list_mk_comb(t18,[t16,t17])    
   in
    (new_definition(prefix_attributation,mk_eq{lhs=t3,rhs=t19}),
    REP_result)
   end;

(*-------mk_attributation---------------------------------------------------*)

fun mk_attributation t = 
 #lhs(dest_eq(concl (SPEC t top_attributation_thm)));

(*-------attributation_CONV-------------------------------------------------*)

(*--- data structure for attributation_CONV ---*)

datatype ty_info = 
   terminal     of thm*         (* definition of rrule is applicable *)
                   term*thm*    (* definition of the rrule           *)
                   thm*         (* applicable-case theorem           *)
                   thm          (* not applicable-case theorem       *)
 | rproduction  of thm*         (* definition of rrule is applicable *)
                   term*thm*    (* definition of the rrule           *)
                   (term list)* (* recursive call terms              *)
                   thm*         (* applicable-case theorem           *)
                   thm          (* not applicable-case theorem       *)
 | sproduction  of thm*         (* definition of srule is applicable *)
                   term*thm*    (* definition of the srule           *)
                   (term list)* (* recursive call terms              *)
                   thm*         (* applicable-case theorem           *)
                   thm          (* not applicable-case theorem       *)
 | rsproduction of thm*         (* definition of rrule is applicable *)
                   term*thm*    (* definition of the rrule           *)
                   thm*         (* definition of srule is applicable *)
                   term*thm*    (* definition of srule               *)
                   (term list)* (* recursive call terms              *)
                   thm*         (* not applicable-case theorem       *)
                   thm*         (* rapplicable-case theorem          *)
                   thm*         (* sapplicable-case theorem          *)
                   thm;         (* rsapplicable-case theorem         *)

structure info_key : ORD_KEY =
struct

open LibBase;

type ord_key = string;

fun cmpKey (s1:ord_key,s2) =
 if s1<s2 then Less else if s1=s2 then Equal else Greater

end;

structure info_Dict = SplayDict(info_key);

val info = ref(info_Dict.mkDict():ty_info info_Dict.dict);

(*--- general functions on building data structure ---*)

fun new_info operation data =
 info:=info_Dict.insert((!info),operation,data);

fun search_info operation =
 info_Dict.find((!info),operation);

(*--- building data structure ---*)

(*
  Global Input:
   prefix_attributation, attr_ty, mk_haname, new_info, theory_name
  Output:
   As a side effect, the information needed for attributation_CONV
   is computed here.
*)
val _ =
 let
  (*
    Input:
     rs should be "s" or "r", operation, term list for attributes
  *)
  fun mk_rule_is_applicable rs operation t_list =
   let
    (*
      Input:
       natural number
      Output:
       type ==`attr_ty->...->attry_ty->bool`==, where attr_ty appears n 
       times 
    *)
    fun mk_ty_is_h n =
     if n>0 then
      mk_type{Args=[attr_ty,mk_ty_is_h (n-1)],Tyop="fun"}
     else
      (==`:bool`==)
    val ty1 = mk_ty_is_h (length t_list)
    val t1  = mk_const{Name=(mk_haname operation rs),Ty=ty1}
   in
    list_mk_comb(t1,t_list)
   end
  (* *)
  val terminal_TAC =
   EVERY [
    REPEAT STRIP_TAC,
    PURE_ONCE_REWRITE_TAC [k_thm],
    BETA_TAC,
    PURE_ASM_REWRITE_TAC [],
    (CONV_TAC (DEPTH_CONV COND_CONV)),
    REWRITE_TAC []
   ]
  (*
    Global Input:
     prefix_attributation, attr_ty, theory_name
    Input:
     terminal
    Output:
     from the definition here: 
      |- !x1.k_t (t x1) = \x.P x1 x => (R x1 x,t (R x1 x))|(x1,t x1)
     following terms (applicable-case theorem):
     |- !y x1 x.((P x1 x)=T) /\ ((R x1 x)=y) ==> (k_t (t x1) x = (y,t y)
     and (not applicable-case theorem):
     |- !x1 x.((P x1 x)=F) ==> (k_t (t x1) x = (x1,t x1))
     the definition of rrule is applicable and the definition of the rrule
     together with the theorems above are put together to form the
     information for attributation_CONV for the terminal "t".
    Used Functions:
     mk_parameter, mk_rule_is_applicable, mk_hname, mk_ty_h
  *)
  fun mk_info_terminal t =
   let
    (*
      prelimenary stuff
    *)
    val [t1,t2] = mk_parameter                    (* [t,x1]             *)
                  {name=t,left=t,right=[]} attr_ty
    val t3  = mk_comb{Rator=t1,Rand=t2}           (* t x1               *)
    val s1  = prefix_attributation^"_"^t
    val ty1 = hd(tl(#Args(dest_type(type_of t1))))
    val ty2 = mk_type{Args=[attr_ty,ty1], Tyop="prod"}
    val ty3 = mk_type{Args=[attr_ty,ty2], Tyop="fun"}
    val ty4 = mk_type{Args=[ty1,ty3], Tyop="fun"}
    val t4  = mk_const{Name=s1,Ty=ty4}            (* k_t                *)
    val t5  = mk_comb{Rator=t4,Rand=t3}           (* k_t (t x1)         *)
    val t6  = mk_var{Name="x",Ty=attr_ty}         (* x                  *)
    val t7  = mk_rule_is_applicable "r" t [t2,t6] (* P x1 x             *)
    val t8  = mk_const{Name = (mk_hname t "r"),   
                       Ty   = (mk_ty_h 2)}        (* R                  *)
    val t9  = list_mk_comb(t8,[t2,t6])            (* R x1 x             *)
    val t10 = mk_comb{Rator = t1, Rand = t9}      (* t(R x1 x)          *)
    val t11 = mk_pair{fst = t9, snd = t10}        (* (R 1x x,t(R x1 x)) *)
    val t12 = mk_pair{fst = t2, snd = t3}         (* (x1,t x1)          *)
    (*
      making the goal for applicable-case theorem
    *)
    val t15 = mk_eq{lhs=t7,rhs=(--`T`--)}  (* (P x1 x)=T                *)
    val t16 = mk_var{Name="y",Ty=attr_ty}  (* y                         *)
    val t17 = mk_eq{lhs=t9,rhs=t16}        (* (R x1 x)=y                *)
    val t18 = mk_comb{Rator=t5,Rand=t6}    (* k_t (t x1) x              *)
    val t19 = mk_comb{Rator=t1,Rand=t16}   (* t y                       *)
    val t20 = mk_pair{fst=t16,snd=t19}     (* (y,t y)                   *)
    val t21 = mk_eq{lhs=t18,rhs=t20}       (* k_t (t x1) x = (y,t y)    *)
    val t22 = mk_conj{conj1=t15,conj2=t17} (* (P x1 x)=T)/\((R x1 x)=y) *)
    val t23 = mk_imp{ant=t22,conseq=t21}
    val t24 = list_mk_forall([t16,t2,t6],t23)
    (*
      making the goal for not-applicable-case theorem
    *)
    val t25 = mk_eq{lhs=t7,rhs=(--`F`--)}  (* (P x1 x)=F                 *)
    val t26 = mk_eq{lhs=t18,rhs=t12}       (* (k_t (t x1) x = (x1,t x1)) *)
    val t27 = mk_imp{ant=t25,conseq=t26}
    val t28 = list_mk_forall([t2,t6],t27)
    (*
      storing information
    *)
    val _ = new_info t
            (terminal(
            (definition theory_name (mk_haname t "r")),
            t8,
            (definition theory_name (mk_hname t "r")),
            prove(t24,terminal_TAC),
            prove(t28,terminal_TAC)))
   in
    ()
   end
  (*
    Global Input:
     prefix_attributation
    Input:
     variable and a list of productions, where the given variable is on 
     the left side of the productions, which should not be empty.
    Output:
     information for attributation_CONV is computed and stored.
  *)
  fun mk_info_variable (A,pl) =
   let
    val ty1 = mk_type{Args=[attr_ty],Tyop=("TY_"^A)} (* :attr_ty TY_A *)
    val ty2 = mk_type{Args=[attr_ty,ty1],Tyop="prod"}
    val ty3 = mk_type{Args=[attr_ty,ty2],Tyop="fun"}
    val ty4 = mk_type{Args=[ty1,ty3],Tyop="fun"}
    val t1  = mk_const{Name=(prefix_attributation^"_"^A),Ty=ty4} (* k_A *)
    (*
      Global Input:
       attr_ty, t1
      Input:
       production
      Used Functions:
       mk_parameter
    *)
    fun mk_equation p =
     let
      val t2 = mk_parameter p attr_ty      (* [p,x1,...,xn]       *)
      val t3 = list_mk_comb(hd t2,tl t2)   (* p x1 ... xn         *)
      val t4 = mk_comb{Rator=t1,Rand=t3}   (* k_A (p x1 ... xn)   *)
      val t5 = mk_var{Name="x",Ty=attr_ty} (* x                   *)
      val t6 = mk_comb{Rator=t4,Rand=t5}   (* k_A (p x1 ... xn) x *)
      val rules = search_rules (#name p)
      fun mk_t7_8 t =
       let
        val s = "y"^(implode(tl(explode(#Name(dest_var t)))))
       in
        mk_var{Name=s,Ty=attr_ty}
       end
      val (t7::t8)  = map mk_t7_8 (tl t2)  (* y1 [y2,...,yn]      *)
      fun mk_t9_10 t =
       let
        val {Name,Ty} = dest_var t
        val s = "y"^(implode(tl(explode Name)))^"'"
       in
        mk_var{Name=s,Ty=Ty}
       end
      val (t9::t10) = map mk_t9_10 (tl t2) (* y1' [y2',...,yn']   *)
      val t11       = hd(tl t2)            (* x1                  *)
      val t12       = tl(tl t2)            (* x2 ... xn           *)
      val t13       = hd t2                (* p                   *)
      fun mk_t14 [] [] =
       []
      | mk_t14 (y::yl) (y'::y'l) =
       append [y,y'] (mk_t14 yl y'l)
      val t14       = mk_t14 t8 t10        (* [y2,y2',...,yn,yn'] *)
      val t15       = t11::t12             (* x1 ... xn           *)
      (*
        Global Input:
         prefix_attributation "k", attr_ty
        Input:
         --`xn:attr_ty TY_X`--, --`xi:attr_ty`--
        Output:
         --`(k_X xn xi)=(yn:attr_ty,yn':attr_ty TY_X)`--
      *)
      fun mk_call xi xn =
       let
        (* left side *)
        val ty1 = #Ty(dest_var xn)                   (*: attr_ty TY_X  *)
        val ty2 = mk_type{Args=[attr_ty,ty1], (* :attr_ty#attr_ty TY_X *)
                          Tyop="prod"}
        val ty3 = mk_type{Args=[attr_ty,ty2],Tyop="fun"}
        val ty4 = mk_type{Args=[ty1,ty3],Tyop="fun"}
        val X   = implode(tl(tl(tl(explode
                  (#Tyop(dest_type ty1))))))
        val t1  = mk_const{Name=(prefix_attributation^"_"^X),   (* k_X *)
                         Ty  =ty4}                       
        val t2  = mk_comb{Rator=t1,Rand=xn}                  (* k_X xn *)
        val t3  = mk_comb{Rator=t2,Rand=xi}               (* k_X xn xi *)
      	(* right side *)
        val yi  = implode("y"::(tl(explode(#Name(dest_var xn)))))
        val t4  = mk_var{Name=yi,Ty=attr_ty}              (* yn        *)
        val t5  = mk_var{Name=(yi^"'"),Ty=ty1}            (* yn'       *)
        val t6  = mk_pair{fst=t4,snd=t5}                  (* (yi,yi')  *)
       in
        mk_eq{lhs=t3,rhs=t6}
       end
      fun mk_t16 xn =
       let
        (* left side *)
        val ty1 = #Ty(dest_var xn)                   (*: attr_ty TY_X  *)
        val ty2 = mk_type{Args=[attr_ty,ty1], (* :attr_ty#attr_ty TY_X *)
                          Tyop="prod"}
        val ty3 = mk_type{Args=[attr_ty,ty2],Tyop="fun"}
        val ty4 = mk_type{Args=[ty1,ty3],Tyop="fun"}
        val X   = implode(tl(tl(tl(explode
                  (#Tyop(dest_type ty1))))))
        val t1  = mk_var{Name=(prefix_attributation^"_"^X),     (* k_X *)
                         Ty  =ty4}                       
       in
        t1
       end
      val t16 = map mk_t16 t12     
      val _ =
       if (#r rules)=[] then
        let
         val operation_TAC = 
          EVERY [
           REPEAT STRIP_TAC,
           PURE_ONCE_REWRITE_TAC [k_thm],
           BETA_TAC,
           PURE_ASM_REWRITE_TAC [],
           PURE_REWRITE_TAC [theorem "pair" "FST",theorem "pair" "SND"],
           PURE_ASM_REWRITE_TAC [],
           (CONV_TAC (DEPTH_CONV COND_CONV)),
           CONV_TAC(DEPTH_CONV let_CONV),
           REWRITE_TAC []
          ]
         (*---
           computing information for attributation_CONV. From definition
           as computed above:
           |- !x1...xn.k_A (p x1...xn) = 
           \x.let xs = P x1 (FST(k_B x2 x1))...(FST(k_Z xn x1)) => 
           S x1 (FST(k_B x2 x1))...(FST(k_Z xn x1))|x1 in
           (xs,p xs (SND (k_B x2 x1))...(SND (k_Z xn x1)))
           compute the following terms (applicable-case):
           !x1...xn x y1 y2 y2' ...yn yn'.
           ((Q x1 y2 ... yn)=T) /\ ((S x1 y2 ... yn)=y1) /\
           ((k_B x2 x1)=(y2,y2')) /\ ... /\ ((k_Z xn x1)=(yn,yn')) ==> 
           k_A (p x1...xn) x = (y1,p y1 y2' ... yn')
           and (not applicable case) :
           !x1...xn x y2 y2' ...yn yn'.
           ((Q x1 y2 ... yn)=F) /\ 
           ((k_B x2 x1)=(y2,y2')) /\ ... /\ ((k_Z xn x1)=(yn,yn')) ==> 
           k_A (p x1...xn) x = (x1,p x1 y2' ... yn')
         ---*)
         val t20 = mk_const{Name=(mk_hname (#name p) "s"),             (* S *)
                            Ty  =(mk_ty_h (length t2-1))}
         val t21 = list_mk_comb(t20,(t11::t8))            (* S x1 y2 ... yn *)
         val t22 = mk_rule_is_applicable                  (* Q x1 y2 ... yn *)
                   "s" (#name p) (t11::t8)
         val t23 = mk_eq{lhs=t22,rhs=(--`T`--)}      (* (Q x1 y2 ... yn)=T  *)
         val t24 = mk_eq{lhs=t21,rhs=t7}             (* (S x1 y2 ... yn)=y1 *)
         val t25 = map (mk_call t11) t12
         val t26 = list_mk_conj(append [t23,t24] t25)
         val t27 = list_mk_comb(t13,t7::t10)           (* p y1 y2' ... yn'  *)
         val t28 = mk_pair{fst=t7,snd=t27}
         val t29 = mk_eq{lhs=t6,rhs=t28}
         val t30 = mk_imp{ant=t26,conseq=t29}
         val t31 = list_mk_forall((append (append t15 [t5,t7]) t14),t30)
         (*
           not applicable-case
         *)
         val t32 = mk_eq{lhs=t22,rhs=(--`F`--)}      (* (Q x1 y2 ... yn)=F  *)
         val t33 = list_mk_conj(t32::t25)
         val t34 = list_mk_comb(t13,t11::t10)        (* p x1 y2'...yn'      *)
         val t35 = mk_pair{fst=t11,snd=t34}          (* (x1,p x1 y2'...yn') *)
         val t36 = mk_eq{lhs=t6,rhs=t35}
         val t37 = mk_imp{ant=t33,conseq=t36}
         val t38 = list_mk_forall(append t15 (t5::t14),t37)
         (*
           store the information
         *)
         val _ = new_info (#name p)
                 (sproduction
                 (
                  (definition "-" (mk_haname (#name p) "s")),
                  t20,
                  (definition "-" (mk_hname  (#name p) "s")),
                  t16,
                  prove(t31,operation_TAC),
                  prove(t38,operation_TAC)
                 ))
        in
         ()
        end
       else if (#s rules)=[] then
        let
         val operation_TAC = 
          EVERY [
           REPEAT STRIP_TAC,
           PURE_ONCE_REWRITE_TAC [k_thm],
           BETA_TAC,
           PURE_ASM_REWRITE_TAC [],
           (CONV_TAC (DEPTH_CONV COND_CONV)),
           CONV_TAC(DEPTH_CONV let_CONV),
           PURE_ASM_REWRITE_TAC [],
           PURE_REWRITE_TAC [theorem "pair" "FST",theorem "pair" "SND"],
           REWRITE_TAC []
          ]
         (*---
           computing information for attributation_CONV. From definition
           as computed above:
           |- !x1...xn.k_A (p x1...xn) = 
           \x.let xs = Q x1 (FST(k_B x2 x1))...(FST(k_Z xn x1)) => 
           S x1 (FST(k_B x2 x1))...(FST(k_Z xn x1))|x1 in
           (xs,p xs (SND (k_B x2 x1))...(SND (k_Z xn x1)))
           compute the following terms (applicable-case):
           !x1...xn x y1 y2 y2'...yn yn'.
           ((P x1 x)=T) /\ ((R x1 x)=y1) /\
           ((k_B x2 y1)=(y2,y2'))/\.../\((k_Z xn y1)=(yn,yn')) 
           ==> 
           k_A (p x1...xn) x = (y1,p y1 y2' ... yn')
           and (not applicable case) :
           !x1...xn x y2 y2'...yn yn'.
           ((P x1 x1)=F) /\ ((k_B x2 x1)=(y2,y2')/\.../\((k_Z xn x1)=(yn,yn'))
           ==>
           k_A (p x1...xn) x = (x1,p x1 y2' ... yn')
         ---*)
         (*
           applicable-case
         *)
         val t20 = mk_const{Name=(mk_hname (#name p) "r"),             (* R *)
                            Ty  =(mk_ty_h 2)}
         val t21 = list_mk_comb(t20,[t11,t5])                     (* R x1 x *)
         val t22 = mk_rule_is_applicable                          (* P x1 x *)
                   "r" (#name p) [t11,t5]
         val t23 = mk_eq{lhs=t22,rhs=(--`T`--)}              (* (P x1 x)=T  *)
         val t24 = mk_eq{lhs=t21,rhs=t7}                     (* (R x1 x)=y1 *)
         val t25 = map (mk_call t7) t12
         val t26 = list_mk_conj(append [t23,t24] t25)
         val t27 = list_mk_comb(t13,t7::t10)           (* p y1 y2' ... yn'  *)
         val t28 = mk_pair{fst=t7,snd=t27}
         val t29 = mk_eq{lhs=t6,rhs=t28}
         val t30 = mk_imp{ant=t26,conseq=t29}
         val t31 = list_mk_forall((append (append t15 [t5,t7]) t14),t30)
         (*
           not applicable-case
         *)
         val t32 = mk_eq{lhs=t22,rhs=(--`F`--)}              (* (P x1 x)=F  *)
         val t33 = map (mk_call t11) t12
         val t34 = list_mk_conj(t32::t33)
         val t35 = list_mk_comb(t13,t11::t10)        (* p x1 y2'...yn'      *)
         val t36 = mk_pair{fst=t11,snd=t35}          (* (x1,p x1 y2'...yn') *)
         val t37 = mk_eq{lhs=t6,rhs=t36}
         val t38 = mk_imp{ant=t34,conseq=t37}
         val t39 = list_mk_forall(append t15 (t5::t14),t38)
         (*
           store the information
         *)
         val _ = new_info (#name p)
                 (rproduction
                 (
                  (definition "-" (mk_haname (#name p) "r")),
                  t20,
                  (definition "-" (mk_hname  (#name p) "r")),
                  t16,
                  prove(t31,operation_TAC),
                  prove(t39,operation_TAC)
                 ))
        in
         ()
        end
       else
        let
         (*---
           computing information for attributation_CONV. From definition
           as computed above:
           |- !x1...xn.k_A (p x1...xn) = 
           \x.let xs = P x1 (FST(k_B x2 x1))...(FST(k_Z xn x1)) => 
           S x1 (FST(k_B x2 x1))...(FST(k_Z xn x1))|x1 in
           (xs,p xs (SND (k_B x2 x1))...(SND (k_Z xn x1)))
           compute the following terms (rsapplicable-case):
           !x1...xn x z y1 y2 y2' ... yn yn'.
           ((P x1 x)=T) /\ ((R x1 x)=y1) /\
           ((Q y1 y2 ... yn)=T) /\ (S y1 y2 ... yn) = z) /\
           ((k_B x2 y1)=(y2,y2')) /\ ... /\ ((k_Z xn y1)=(yn,yn') ==> 
           k_A (p x1...xn) x = (z,p z y2' ... yn')
           and (rapplicable case) :
           !x1...xn x y1 y2 y2' ... yn yn'.
           ((P x1 x)=T) /\ ((R x1 x) = y1) /\ ((Q y1 y2 ... yn)=F) /\
           ((k_B x2 y1)=(y2,y2')) /\ ... /\ ((k_Z xn y1)=(yn,yn')) ==> 
           k_A (p x1...xn) x = (y1,p y1 y2' ... yn')
           and (sapplicable case) :
           !x1...xn x y1 y2 y2' ... yn yn'.
           ((P x1 x)=F) /\ ((Q x1 y2 ... yn)=T) /\ ((S x1 y2 ... yn) = y1)/\
           ((k_B x2 x1)=(y2,y2')) /\ ... /\ ((k_Z xn x1)=(yn,yn')) ==> 
           k_A (p x1...xn) x = (y1,p y1 y2' ... yn')
           and (not applicable case) :
           !x1...xn x y2 y2'...yn yn'.
           ((P x1 x)=F) /\ ((Q x1 y2 ... yn)=F) /\
           ((k_B x2 x1)=(y2,y2')) /\ ... /\ ((k_Z xn x1)=(yn,yn')) ==> 
           k_A (p x1...xn) x = (x1,p x1 y2' ... yn')
         ---*)
         val operation_TAC = 
          EVERY [
           REPEAT STRIP_TAC,
           PURE_ONCE_REWRITE_TAC [k_thm],
           BETA_TAC,
           PURE_ASM_REWRITE_TAC [],
           (CONV_TAC (DEPTH_CONV COND_CONV)),
           CONV_TAC(DEPTH_CONV let_CONV),
           PURE_ASM_REWRITE_TAC [],
           PURE_REWRITE_TAC [theorem "pair" "FST",theorem "pair" "SND"],
           PURE_ASM_REWRITE_TAC [],
           (CONV_TAC (DEPTH_CONV COND_CONV)),
           REWRITE_TAC []
          ]
         (*
           rs applicable-case
         *)
         val t20 = mk_const{Name=(mk_hname (#name p) "r"),             (* R *)
                            Ty  =(mk_ty_h 2)}
         val t21 = list_mk_comb(t20,[t11,t5])                     (* R x1 x *)
         val t22 = mk_rule_is_applicable                          (* P x1 x *)
                   "r" (#name p) [t11,t5]
         val t23 = mk_eq{lhs=t22,rhs=(--`T`--)}              (* (P x1 x)=T  *)
         val t24 = mk_eq{lhs=t21,rhs=t7}                     (* (R x1 x)=y1 *)
         val t25 = mk_const{Name=(mk_hname (#name p) "s"),             (* S *)
                            Ty  =(mk_ty_h ((length t8)+1))}
         val t26 = list_mk_comb(t25,(t7::t8))               (* S y1 y2...yn *)
         val t27 = mk_var{Name="z",Ty=attr_ty}                         (* z *)
         val t28 = mk_eq{lhs=t26,rhs=t27}               (* (S y1 y2...yn)=z *)
         val t29 = mk_rule_is_applicable                    (* Q y1 y2...yn *)
                   "s" (#name p) (t7::t8)
         val t30 = mk_eq{lhs=t29,rhs=(--`T`--)}         (* (Q y1 y2...yn)=T *)
         val t31 = map (mk_call t7) t12
         val t32 = list_mk_conj(append [t23,t24,t30,t28] t31)
         val t33 = list_mk_comb(t13,t27::t10)           (* p z y2' ... yn'  *)
         val t34 = mk_pair{fst=t27,snd=t33}
         val t35 = mk_eq{lhs=t6,rhs=t34}
         val t36 = mk_imp{ant=t32,conseq=t35}
         val t37 = list_mk_forall((append (append t15 [t5,t27,t7]) t14),t36)
         (*
           r applicable-case
         *)
         val t40 = mk_eq{lhs=t29,rhs=(--`F`--)}            (* (Q y1...yn)=F *)
         val t41 = list_mk_conj(append [t23,t24,t40] t31)
         val t42 = list_mk_comb(t13,(t7::t10))            (* p y1 y2'...yn' *)
         val t43 = mk_pair{fst=t7,snd=t42}            (* (y1,p y1 y2'...yn' *)
         val t44 = mk_eq{lhs=t6,rhs=t43}
         val t45 = mk_imp{ant=t41,conseq=t44}
         val t46 = list_mk_forall((append (append t15 [t5,t7]) t14),t45)
         (*
           s applicable-case
         *)
         val t50 = mk_eq{lhs=t22,rhs=(--`F`--)}               (* (P x1 x)=F *)
         val t51 = mk_rule_is_applicable "s"                (* Q x1 y2...yn *)
                   (#name p) (t11::t8)
         val t52 = mk_eq{lhs=t51,rhs=(--`T`--)}         (* (Q x1 y2...yn)=T *)
         val t53 = map (mk_call t11) t12
         val t54 = list_mk_comb(t25,(t11::t8))              (* S x1 y2...yn *)
         val t55 = mk_eq{lhs=t54,rhs=t7}                (* (S y1 y2...yn)=y *)
         val t56 = list_mk_conj(append [t50,t52,t55] t53)
         val t57 = mk_imp{ant=t56,conseq=t44}
         val t58 = list_mk_forall((append (append t15 [t5,t7]) t14),t57)
         (*
           not applicable-case
         *)
         val t60 = mk_eq{lhs=t51,rhs=(--`F`--)}         (* (Q x1 y2...yn)=F *)
         val t61 = list_mk_conj(append [t50,t60] t53)
         val t62 = list_mk_comb(t13,(t11::t10))         (* p x1 y2' ... yn' *)
         val t63 = mk_pair{fst=t11,snd=t62}        (* (x1,p x1 y2' ... yn') *)
         val t64 = mk_eq{lhs=t6,rhs=t63}
         val t65 = mk_imp{ant=t61,conseq=t64}
         val t66 = list_mk_forall((append (append t15 [t5]) t14),t65)
         (*
           store the information
         *)
         val _ = new_info (#name p)
                 (rsproduction
                 (
                  (definition theory_name (mk_haname (#name p) "r")),
                  t20,
                  (definition theory_name (mk_hname  (#name p) "r")),
                  (definition theory_name (mk_haname (#name p) "s")),
                  t25,
                  (definition theory_name (mk_hname  (#name p) "s")),
                  t16,
                  prove(t66,operation_TAC),
                  prove(t46,operation_TAC),
                  prove(t58,operation_TAC),
                  prove(t37,operation_TAC)
                 ))
        in
         ()
        end
     in
      ()
     end
   in
    map mk_equation pl
   end
 in
  (map mk_info_terminal T);
  (map mk_info_variable V)
 end;

(*--- attributation_CONV ---*)

(*
  Global Input:
   is_set_thms
  Input:
   a definitional theorem on whether a rule is applicable
   |- !a1...an.P a1...an = Q a1...an and a list of constant terms [b1...bn]
   matching a1...an.
  Output:
   |- P b1...bn = T or |- P b1...bn = F
*)
val applicable_CONV =
 let
  val taut_thms = [Taut.TAUT_PROVE (--`F /\ x = F`--),
                   Taut.TAUT_PROVE (--`T /\ x = x`--),
                   Taut.TAUT_PROVE (--`F \/ x = x`--),
                   Taut.TAUT_PROVE (--`T \/ x = T`--)]
  fun do_it th t_list =
   RIGHT_CONV_RULE(PURE_REWRITE_CONV taut_thms)
   (RIGHT_CONV_RULE(PURE_REWRITE_CONV is_set_thms)
   (SPECL t_list th))
 in
  do_it
 end;

(*
  Global Input:
   simplify_attributation_CONV
  Input:
   term t= --`h_x`--, definitional theorem 
   th = |- (h_x x1...xn = ...) /\ ... /\ (h_x x1...xn = ...)
   term list t_list = [--`y1`--,...,--`yn`--]
  Output:
   |- h_x y1 ... yn = ...
*)
fun apply_rule_CONV t th t_list =
 (RIGHT_CONV_RULE simplify_attributation_CONV)
 (PURE_REWRITE_CONV [th] (list_mk_comb(t,t_list)));

(*
  Global Input:
   is_set_thms, taut_thms
  Input:
   --`k_Y (X x1 ... xn) x`-- with a variable/terminal Y,
   production/terminal(=operation) X, and attribute x
  Output:
   expanded definitions on k_Y and related stuff
  Used Functions:
   search_info, applicable_CONV, apply_rule_CONV
*)
fun expand_k_CONV t =
 let
  (*--- prepare input ---*)
  val (t1,[t2,t3]) = strip_comb t  (* (k_Y,[(X x1 ...xn),x]) *)
  val (t4,t5)      = strip_comb t2 (* (X,[x1,...,xn])        *)
  (*--- recursive calling ---*)
  fun merge [] [] =
   []
  |   merge (head1::tail1) (head2::tail2) =
   (head1,head2)::(merge tail1 tail2)
  fun call x (k_X,xi) =
   expand_k_CONV (list_mk_comb(k_X,[xi,x]))
  fun flatten_call_result th_list =
   flatten (map (fn th => let
                           val {fst,snd} = dest_pair
                                           (#rhs(dest_eq(concl th)))
                          in
                           [fst,snd]
                          end
                 ) th_list)
  fun select_first (h1::(h2::t)) = 
   h1::(select_first t)
  | select_first [] =
   []
  (*--- the main part ---*)
  fun case_CONV (terminal (P,t_R,R,APP,NAPP)) =
   (*
     Algorithm:
      from the definition:
      |- !x1.k_t (t x1) = \x.P x1 x => (R x1 x,t (R x1 x))|(x1,t x1)
      it follows that t1=k_t, t4=t, t5=x1. First prove, whether P holds(th1).
      If P holds, then specialize APP
      |- !y x1 x.((P x1 x)=T) /\ ((R x1 x)=y) ==> (k_t (t x1) x = (y,t y)
      where y has to be derived(th2). otherwise specialise NAPP
      |- !x1 x.((P x1 x)=F) ==> (k_t (t x1) x = (x1,t x1))
   *)
   let
    val t10  = append t5 [t3]
    val th1 = applicable_CONV P t10 (* does P hold ? *)
   in
    if (#rhs(dest_eq(concl th1)))=(--`T`--) then
     let
      val th2 = apply_rule_CONV t_R R t10 (* derive y *)
     in
      MP
      (SPECL ((#rhs(dest_eq(concl th2)))::t10) APP)
      (CONJ th1 th2)
     end
    else
     MP
     (SPECL t10 NAPP)
     th1
   end     
  | case_CONV (rproduction (P,t_R,R,C,APP,NAPP)) =
   (*
     Algorithm:
      from the definition:
      |- !x1...xn.k_A (p x1...xn) = 
      \x.let xs = P x1 (FST(k_B x2 x1))...(FST(k_Z xn x1)) => 
      S x1 (FST(k_B x2 x1))...(FST(k_Z xn x1))|x1 in
      (xs,p xs (SND (k_B x2 x1))...(SND (k_Z xn x1)))
      First prove, whether P holds. If P holds, then specialize
      !x1...xn x y1 y2 y2'...yn yn'.
      ((P x1 x)=T) /\ ((R x1 x)=y1) /\
      ((k_B x2 y1)=(y2,y2'))/\.../\((k_Z xn y1)=(yn,yn')) 
      ==> 
      k_A (p x1...xn) x = (y1,p y1 y2' ... yn')
      where y1 is derived(th2) and y2 y2'...yn yn' are derived(th3). Otherwise
      specialize
      !x1...xn x y2 y2'...yn yn'.
      ((P x1 x1)=F) /\ ((k_B x2 x1)=(y2,y2')/\.../\((k_Z xn x1)=(yn,yn'))
      ==>
      k_A (p x1...xn) x = (x1,p x1 y2' ... yn')
   *)
   let
    (*--- does P hold? ---*)
    val t10 = [hd t5,t3]
    val th1 = applicable_CONV P t10
   in
    if (#rhs(dest_eq(concl th1)))=(--`T`--) then
     let
      val th2 = apply_rule_CONV t_R R t10                     (* derive y1 *)
      val t11 = #rhs(dest_eq(concl th2))                             (* y1 *)
      val th3 = map (call t11) (merge C (tl t5))
      val t12 = flatten_call_result th3             (* [y2,y2',...,yn,yn'] *)
     in
      MP
      (SPECL (append(append t5 [t3]) (t11::t12)) APP)
      (LIST_CONJ (th1::(th2::th3)))
     end
    else
     let
      val th3 = map (call (hd t5)) (merge C (tl t5))
      val t12 = flatten_call_result th3             (* [y2,y2',...,yn,yn'] *)
     in
      MP
      (SPECL (append t5 (t3::t12)) NAPP)
      (LIST_CONJ (th1::th3))
     end
   end
  | case_CONV (sproduction (Q,t_S,S,C,APP,NAPP)) =
   (*
     Algorithm:
      from the definition:
      |- !x1...xn.k_A (p x1...xn) = 
      \x.let xs = Q x1 (FST(k_B x2 x1))...(FST(k_Z xn x1)) => 
      S x1 (FST(k_B x2 x1))...(FST(k_Z xn x1))|x1 in
      (xs,p xs (SND (k_B x2 x1))...(SND (k_Z xn x1)))
      First, derive y2 y2'...yn yn'(th1). Derive, whether Q holds(th2). If Q 
      holds, then spezialise
      !x1...xn x y1 y2 y2' ...yn yn'.
      ((Q x1 y2 ... yn)=T) /\ ((S x1 y2 ... yn)=y1) /\
      ((k_B x2 x1)=(y2,y2')) /\ ... /\ ((k_Z xn x1)=(yn,yn')) ==> 
      k_A (p x1...xn) x = (y1,p y1 y2' ... yn')
      where y1 has to be derived(th3). Otherwise, spezialise
      !x1...xn x y2 y2' ...yn yn'.
      ((Q x1 y2 ... yn)=F) /\ 
      ((k_B x2 x1)=(y2,y2')) /\ ... /\ ((k_Z xn x1)=(yn,yn')) ==> 
      k_A (p x1...xn) x = (x1,p x1 y2' ... yn')
   *)
   let
    val th1 = map (call (hd t5)) (merge C (tl t5))
    val t10 = flatten_call_result th1             (* [y2,y2',...,yn,yn'] *)
    val t11 = select_first t10                    (* y2...yn *)
    val t12 = (hd t5)::t11                        (* x1 y2...yn *)
    val th2 = applicable_CONV Q t12               (* derive Q *)
   in
    if (#rhs(dest_eq(concl th2)))=(--`T`--) then
     let
      val th3 = apply_rule_CONV t_S S t12                     (* derive y1 *)
      val t13 = #rhs(dest_eq(concl th3))                             (* y1 *)
     in
      MP
      (SPECL (append (append t5 [t3]) (t13::t10)) APP)
      (LIST_CONJ (th2::(th3::th1)))
     end
    else
     MP
     (SPECL (append t5 (t3::t10)) NAPP)
     (LIST_CONJ (th2::th1))
   end
  | case_CONV (rsproduction (P,t_R,R,Q,t_S,S,C,NAPP,RAPP,SAPP,RSAPP)) =
   (*
     Algorithm:
      from the definition:
      |- !x1...xn.k_A (p x1...xn) = 
      \x.let xs = P x1 (FST(k_B x2 x1))...(FST(k_Z xn x1)) => 
      S x1 (FST(k_B x2 x1))...(FST(k_Z xn x1))|x1 in
      (xs,p xs (SND (k_B x2 x1))...(SND (k_Z xn x1)))
      First, derive P(th1). If P holds, then derive y1(th2). Now, recursive
      calling is done(th3). Finally, derive Q(th4) and z(th5). 
      Spezialise(P and Q holds):
      !x1...xn x z y1 y2 y2' ... yn yn'.
      ((P x1 x)=T) /\ ((R x1 x)=y1) /\
      ((Q y1 y2 ... yn)=T) /\ (S y1 y2 ... yn) = z) /\
      ((k_B x2 y1)=(y2,y2')) /\ ... /\ ((k_Z xn y1)=(yn,yn') ==> 
      k_A (p x1...xn) x = (z,p z y2' ... yn')
      or (P holds):
      !x1...xn x y1 y2 y2' ... yn yn'.
      ((P x1 x)=T) /\ ((R x1 x) = y1) /\ ((Q y1 y2 ... yn)=F) /\
      ((k_B x2 y1)=(y2,y2')) /\ ... /\ ((k_Z xn y1)=(yn,yn')) ==> 
      k_A (p x1...xn) x = (y1,p y1 y2' ... yn')
      or (S holds):
      !x1...xn x y1 y2 y2' ... yn yn'.
      ((P x1 x)=F) /\ ((Q x1 y2 ... yn)=T) /\ ((S x1 y2 ... yn) = y1)/\
      ((k_B x2 x1)=(y2,y2')) /\ ... /\ ((k_Z xn x1)=(yn,yn')) ==> 
      k_A (p x1...xn) x = (y1,p y1 y2' ... yn')
      or (nothing holds):
      !x1...xn x y2 y2'...yn yn'.
      ((P x1 x)=F) /\ ((Q x1 y2 ... yn)=F) /\
      ((k_B x2 x1)=(y2,y2')) /\ ... /\ ((k_Z xn x1)=(yn,yn')) ==> 
      k_A (p x1...xn) x = (x1,p x1 y2' ... yn')
   *)
   let
    val t10 = [hd t5,t3]
    val th1 = applicable_CONV P t10
   in
    if (#rhs(dest_eq(concl th1)))=(--`T`--) then
     let
      val th2 = apply_rule_CONV t_R R t10                     (* derive y1 *)
      val t11 = #rhs(dest_eq(concl th2))                             (* y1 *)
      val th3 = map (call t11) (merge C (tl t5))
      val t12 = flatten_call_result th3             (* [y2,y2',...,yn,yn'] *)
      val t13 = select_first t12                    (* y2...yn *)
      val t14 = t11::t13                            (* y1 y2...yn *)
      val th4 = applicable_CONV Q t14               (* derive Q *)
     in
      if (#rhs(dest_eq(concl th4)))=(--`T`--) then
       let
        val th5 = apply_rule_CONV t_S S t14                     (* derive z *)
        val t15 = #rhs(dest_eq(concl th5))                             (* z *)
       in
        MP
        (SPECL (append (append t5 [t3,t15,t11]) t12) RSAPP)
        (LIST_CONJ (th1::(th2::(th4::(th5::th3)))))
       end
      else
       MP
       (SPECL (append (append t5 [t3,t11]) t12) RAPP)
       (LIST_CONJ (th1::(th2::(th4::th3))))
     end
    else
     let
      val th3 = map (call (hd t5)) (merge C (tl t5))
      val t12 = flatten_call_result th3             (* [y2,y2',...,yn,yn'] *)
      val t13 = select_first t12                    (* y2...yn *)
      val t14 = (hd t5)::t13                        (* x1 y2...yn *)
      val th4 = applicable_CONV Q t14               (* derive Q *)
     in
      if (#rhs(dest_eq(concl th4)))=(--`T`--) then
       let
        val th5 = apply_rule_CONV t_S S t14                     (* derive z *)
        val t15 = #rhs(dest_eq(concl th5))                             (* z *)
       in
        MP
        (SPECL (append (append t5 [t3,t15]) t12) SAPP)
        (LIST_CONJ (th1::(th4::(th5::th3))))
       end
      else
       MP
       (SPECL (append t5 (t3::t12)) NAPP)
       (LIST_CONJ (th1::(th4::th3)))
     end
   end
 in
  RIGHT_CONV_RULE simplify_attributation_CONV
  (case_CONV (search_info (#Name(dest_const t4))))
 end;

(*
  Global Input:
   top_attributation_thm, attr_map_thm, is_result_thm, expand_k_CONV, 
   REP_result_thm
*)
fun attributation_CONV maxl t = 
 let
  (*--- preparing input ---*)
  val x             = #Rand(dest_comb t)
  val th1           = SPEC x (top_attributation_thm)
  val th2           = BETA_RULE(PURE_REWRITE_RULE [attr_map_thm] th1)
  val (t1,[t3,t2])  = strip_comb(#rhs(dest_eq(concl th2)))
  val (t4,[finished,f,x0])      = strip_comb t3
  val [apply_0_thm,apply_n_thm] = CONJUNCTS 
   (definition "apply_f_until_finished" "apply_f_cond_n_times")
  val taut_thms = [Taut.TAUT_PROVE (--`F /\ x = F`--),
                   Taut.TAUT_PROVE (--`T /\ x = x`--),
                   Taut.TAUT_PROVE (--`F \/ x = x`--),
                   Taut.TAUT_PROVE (--`T \/ x = T`--)]
  (*---  ---*)
  fun finished_CONV t = 
   PURE_REWRITE_RULE ((definition "-" ("is_"^result_set))::taut_thms)
   (PURE_REWRITE_CONV [is_result_thm]
   (mk_comb{Rator=finished,Rand=t}))
  (*--- ---*)
  (*
    Input:
     term of the form --`SND (x,y)`--
    Output:
     theorem |- SND (x,y) = y
  *)
  fun SND_CONV  t =
   let
    val {fst,snd} = dest_pair (#Rand(dest_comb t))
   in
    ISPECL [fst,snd] (theorem "pair" "SND")
   end
  (*
    Used Functions:
     finished_CONV, expand_k_CONV
  *)
  fun apply_until finished f th x0 tn (n:int) maxl =
   let
    val th1 = finished_CONV (#rhs(dest_eq(concl th)))
   in
    if ((not(maxl=[]))andalso(n>=(hd maxl)))orelse
   ((#rhs(dest_eq(concl th1)))=(--`T`--)) then
     (th1,th)
    else
     apply_until finished f  
     (RIGHT_CONV_RULE SND_CONV
     (RIGHT_CONV_RULE(RAND_CONV expand_k_CONV)
     (REWRITE_RULE [th,th1] 
     (BETA_RULE(ISPECL [finished,f,x0,tn] apply_n_thm)))))   
     x0 (--`SUC ^tn`--) (n+1) maxl
   end
  val (th3,th4) =  (* finished_thm, number of passes, result_thm *)
   (apply_until finished f 
   (ISPECL [finished,f,x0] apply_0_thm)
   x0 (--`0`--) 0 maxl)
 in
  (* is finished? *)
  if (#rhs(dest_eq(concl th3)))=(--`T`--) then
   let
    (* solving attributation *)
    val (t_ap,[t_finished,t_f,t_x,t_n]) = strip_comb(#lhs(dest_eq(concl th4)))
    val t_y = #rhs(dest_eq(concl th4))
    val th5 = EXISTS(mk_exists{Bvar=(--`n:num`--),Body=
              mk_eq{lhs=(list_mk_comb(t_ap,
                                     [t_finished,t_f,t_x,(--`n:num`--)])),
                    rhs=(#rhs(dest_eq(concl th4)))}},t_n) th4
    val th6 = ISPECL [t_finished,t_f,t_y,t_x]
              (theorem "apply_f_until_finished" 
              "apply_f_until_finished_TERMINATE_CASE")
    val th7 = MP th6 (CONJ (EQT_ELIM th3) th5)
    (* mapping into the result set *)
    val (t_map,[_,t_fmap]) = strip_comb(#rhs(dest_eq(concl th1)))
    val th8 = PURE_REWRITE_RULE [REP_result_thm]
              (BETA_RULE(PURE_REWRITE_CONV [attr_map_thm] 
              (list_mk_comb(t_map,[(#rhs(dest_eq(concl th7))),t_fmap]))))
   in
    RIGHT_CONV_RULE (fn t => th8)
    (RIGHT_CONV_RULE (RATOR_CONV(RAND_CONV (fn t => th7))) th2)
   end
  else
   CONJ th3 th4
 end;

(*-------new_translation_definition-----------------------------------------*)

(*
  Global Input:
   translation_rules, prefix_local_translation, search_attr_ty, result_set,
   target_type, P
  Output:
   definitional theorems for the definition of the translation rules
*)
val translation_rules_thms =
 let
  fun search_right search_name =
   let
    fun do_it [] = 
     raise new_compiler_definition_error
    | do_it ({name:string,left:string,right:string list}::p_list) =
     if search_name=name then
      right
     else
      do_it p_list
   in
    do_it P
   end
  val ty_a = search_attr_ty result_set
  val ty_r = target_type
  val f    = prefix_local_translation
  val ty1 = mk_type{Args=[ty_a,ty_r],Tyop="fun"}   (* :ty_a->ty_r *)
  val ty2 = mk_type{Args=[ty_r,ty1],Tyop="fun"}    (* :ty_r->(ty_a->ty_r) *)
  val ty3 = mk_type{Args=[ty_a,ty2],Tyop="fun"}(* :ty_a->ty_r->(ty_a->ty_r) *)
  fun define_rule [] =
   []
  | define_rule ((DOWNUP_RULE (t,r,a,rhs))::r_list) =
   let
    val t1 = mk_var{Name=(f^"_"^t^"_"^t),Ty=ty2}
    val t2 = mk_var{Name=r,Ty=ty_r}
    val t3 = mk_var{Name=a,Ty=ty_a}
    val t4 = list_mk_comb(t1,[t2,t3])
    val t5 = mk_eq{lhs=t4,rhs=rhs}
   in
    (new_definition((f^"_"^t^"_"^t),t5))::(define_rule r_list)
   end
  | define_rule ((DOWN_RULE (pname,r,a,rhs))::r_list) =
   let
    val A  = hd(search_right pname)
    val t1 = mk_var{Name=(f^"_"^pname^"_"^A),Ty=ty2}
    val t2 = mk_var{Name=r,Ty=ty_r}
    val t3 = mk_var{Name=a,Ty=ty_a}
    val t4 = list_mk_comb(t1,[t2,t3])
    val t5 = mk_eq{lhs=t4,rhs=rhs}
   in
    (new_definition((f^"_"^pname^"_"^A),t5))::(define_rule r_list)
   end
  | define_rule ((LEFTRIGHT_RULE (pname,X,Y,a1,r,a2,rhs))::r_list) =
   let
    val t1 = mk_var{Name=(f^"_"^pname^"_"^X^"_"^Y),Ty=ty3}
    val t2 = mk_var{Name=a1,Ty=ty_a}
    val t3 = mk_var{Name=r,Ty=ty_r}
    val t4 = mk_var{Name=a2,Ty=ty_a}
    val t5 = list_mk_comb(t1,[t2,t3,t4])
    val t6 = mk_eq{lhs=t5,rhs=rhs}
   in
    (new_definition((f^"_"^pname^"_"^X^"_"^Y),t6))::(define_rule r_list)
   end
  | define_rule ((UP_RULE (pname,r,a,rhs))::r_list) =
   let
    (*
      Algorithm:
       The right side of the production pname hast at least one element
    *)
    fun last (h1::(h2::rest)) =
     if rest=[] then
      h2
     else
      last (h2::rest)
    | last [h] =
     h
    val A  = last(search_right pname)
    val t1 = mk_var{Name=(f^"_"^A^"_"^pname),Ty=ty2}
    val t2 = mk_var{Name=r,Ty=ty_r}
    val t3 = mk_var{Name=a,Ty=ty_a}
    val t4 = list_mk_comb(t1,[t2,t3])
    val t5 = mk_eq{lhs=t4,rhs=rhs}
   in
    (new_definition((f^"_"^A^"_"^pname),t5))::(define_rule r_list)
   end
 in
  define_rule translation_rules
 end;

(*
  Global Input:
  result_set, target_type, prefix_local_translation, prefix_translation
  Used Functions:
  search_attr_ty
*)
val (traverse_definition,translate_definition) = 
 let
  (*
    preparing the input
  *)
  val ty_a = search_attr_ty result_set
  val ty_r = target_type
  val f    = prefix_local_translation
  val g    = prefix_translation
  (*
    Input:
     terminal
    Ouput:
     translation for the given terminal. For terminal "t", g="g"
     and f="f", it has the form:
     --`g_t (t A_t) = \f.f_t_t (f A_t) A_t`--,
     where --`f_t_t`-- is an already defined local translation.
     If f_t_t is not defined, the folloing is computed:
     --`g_t (t A_t) = \f.f A_t`--
  *)
  fun mk_traverse_terminal t =
   let
    (*
      left side of the definitional equation
    *)
    val t1  = mk_var{Name=("A_"^t),Ty=ty_a}        (* A_t *)
    val t2  = mk_type{Args=[ty_a],Tyop=("TY_"^t)}  (* :TY_t *)
    val t3  = mk_type{Args=[ty_a,t2],Tyop="fun"}   (* :ty_a->TY_t *)
    val t4  = mk_const{Name=t,Ty=t3}               (* t *)
    val t5  = mk_comb{Rator=t4,Rand=t1}            (* t A_t *)
    val t6  = mk_type{Args=[ty_a,ty_r],Tyop="fun"} (* :ty_a->ty_r *)
    val t7  = mk_type{Args=[t6,ty_r],Tyop="fun"}   (* :(ty_a->ty_r)->ty_r *)
    val t8  = mk_type{Args=[t2,t7],Tyop="fun"} (* :TY_t->(ty_a->ty_r)->ty_r *)
    val t9  = mk_var{Name=g^"_"^t,Ty=t8}           (* g_t *)
    val t10 = mk_comb{Rator=t9,Rand=t5}            (* g_t (t A_t) *)
    (*
      right side of the definition equation
    *)
    val t11 = mk_var{Name=f,Ty=t6}                  (* f *)
    val t12 = mk_comb{Rator=t11,Rand=t1}            (* f A_t *)
    val t13 = mk_type{Args=[ty_r,t6],Tyop="fun"}    (* :ty_r->(ty_a->ty_r) *)
    val t14 = if is_constant (f^"_"^t^"_"^t) then
               let
                val t15 = mk_const{Name=(f^"_"^t^"_"^t),Ty=t13} (* f_t_t *)
               in
                list_mk_comb(t15,[t12,t1])
               end
              else
               t12
    val t15 = mk_abs{Bvar=t11,Body=t14}
   in
    mk_eq{lhs=t10,rhs=t15}
   end
  (*
    Global Input:
     ty_a
    Input:
     variable and a list of productions, where the given variable is on the
     left side of the productions, which should not be emgy.
    Output:
     translations for the given variable. For a variable "A", g="g"
     and f="f", it has the form:
     --`g_A ...`--
  *)
  fun mk_traverse_variable (A,pl) =
   let
    val ty1 = mk_type{Args=[ty_a],Tyop=("TY_"^A)}    (* :ty_a TY_A        *)
    val ty2 = mk_type{Args=[ty_a,ty_r],Tyop="fun"}   (* :ty_a->ty_r       *)
    val ty3 = mk_type{Args=[ty2,ty_r],Tyop="fun"}    (* :ty_a->ty_a->ty_r *)
    val ty4 = mk_type{Args=[ty1,ty3],   (* :(ty_a TY_A)->ty_a->ty_a->ty_r *)
                      Tyop="fun"}
    val t5 = mk_var{Name=(g^"_"^A),Ty=ty4} (* g_A            *)
    val t6 = mk_var{Name=f,Ty=ty2}        (* f:ty_a->ty_r  *)
    (*
      Input:
       the name and the right side of a production rule. For a production 
       named "p" and a right side "B ... Z", it has the form:
      Output:
       --`g_A (p A_p B ... Z) = ...`--
    *)
    fun mk_rule rulename right = 
     let
      (*--- left side of a definitional translation equation ---*)
      (*
        Global Input:
         ty_a
        Input:
         right side of a production rule: a list of symbols ["B",...,"Z"].
        Output:
         ==`:(ty_a TY_B) -> ... -> (ty_a TY_Z)`==
      *)
      fun mk_t7 [alpha] =
       mk_type{Args=[ty_a],Tyop=("TY_"^alpha)}
      | mk_t7 (alpha::alphal) =
       mk_type{Args=[mk_t7 [alpha],(mk_t7 alphal)],
               Tyop="fun"}
      (*  ==`:ty_a -> (ty_a TY_B) -> ... -> (ty_a TY_Z) -> (ty_a TY_A)`== *)
      val t7 = mk_type{Args=[ty_a,mk_t7 (append right [A])],Tyop="fun"}
      val t8 = mk_const{Name=rulename,Ty=t7}        (* p *)
      val t9 = mk_var{Name=("A_"^rulename),Ty=ty_a} (* A_p *)
      (*
        Input:
         right side of a production rule: a list of symbols ["B",...,"Z"].
        Output:
         [--`x26:ty_a TY_B`--,...,--`x2:ty_a TY_Z`--]
      *)
      fun mk_t10 [] =
       []
      | mk_t10 (alpha::alphal) =
       (mk_var{Name="x"^(int_2_string ((length alphal)+1)),
               Ty  =(mk_t7[alpha])})::(mk_t10 alphal)
      val t10 = list_mk_comb(t8,t9::(mk_t10 right))   (* (p A_p x26 ... x2) *)
      val t11 = mk_comb{Rator=t5,Rand=t10}        (* g_A (p A_p x26 ... x2) *)
      (*--- ride side of a definitional translation equation ---*)
      (*
        local dummy translations fd1 : \z y1.z and fd2: \y1 z y2.z
      *)
      val (fd1,fd2) = let
                       val z  = mk_var{Name="z",Ty=ty_r}
                       val y1 = mk_var{Name="y1",Ty=ty_a}
                       val y2 = mk_var{Name="y2",Ty=ty_a}
                       val t1 = list_mk_abs([z,y1],z)
                       val t2 = list_mk_abs([y1,z,y2],z)
                      in
                       (t1,t2)
                      end
      (*
        part of the right side of a definition translation equation: case 1
      *)
      val ty5 = mk_type{Args=[ty_r,ty2],         (* :ty_r->ty_a->ty_r       *)
                        Tyop="fun"}
      val ty6 = mk_type{Args=[ty_a],             (* :ty_a TY_B              *)
                        Tyop=("TY_"^(hd right))}
      val ty7 = mk_type{Args=[ty2,ty_r],         (* :ty_a->ty_r->ty_r       *)
                        Tyop="fun"}
      val ty8 = mk_type{Args=[ty6,ty7],
                        Tyop="fun"}              (* :(ty_a TY_B) -> ty7     *)
      val t12 = mk_comb{Rator=t6,Rand=t9}        (* f A_p                   *)
      val t13 = if is_constant (f^"_"^rulename^"_"^(hd right)) then

                 mk_const{Name=                  (* f_p_B                   *)
                          (f^"_"^rulename^"_"^(hd right)),
                          Ty=ty5}
                else
                 fd1
      val t14 = mk_var{Name=                     (* g_B                     *)
       (g^"_"^(hd right)),Ty=ty8}
      val t15 = mk_var{Name=("x"^                (* x26                     *)
       (int_2_string(length right))),Ty=ty6}
      val t16 = mk_comb{Rator=t14,
                        Rand =t15}               (* g_B x26                 *)
      val t17 = mk_comb{Rator=t13,
                        Rand =t12}               (* f_p_B (f A_p)           *)
      val t22 = mk_comb{Rator=t16,               (* g_B x26 (f_p_B (f A_p)) *)
                        Rand =t17} 
      (*
        part of the right side of a definition translation equation: case 2
        applied to case 1
      *)
      fun mk_t23 [alpha] n =
       t22
      | mk_t23 (alpha2::(alpha1::alphal)) n =
       let
        val ty9  = mk_type{Args=[ty_a],
                           Tyop=("TY_"^alpha2)} (* :ty_a TY_alpha2 *)
        val ty10 = mk_type{Args=[ty9,ty7],      (* :(ty_a TY_alpha2)->ty7 *)
                           Tyop="fun"}
        val t50  = mk_var{Name=(g^"_"^alpha2), (* g_alpha2 *)
                          Ty  =ty10}
        val t51 = mk_var                        (* p_alpha2 *)
                   {Name=(("x"^(int_2_string n))),
                    Ty  =ty9}
        val t52 = if is_constant (f^"_"^rulename^"_"^alpha1^"_"^alpha2) then
                   mk_const                      (* f_p_alpha1_alpha2 *)
                   {Name=(f^"_"^rulename^"_"^alpha1^"_"^alpha2),
                    Ty  =(mk_type{Args=[ty_a,ty5],Tyop="fun"})}
                  else
                   fd2
        val t53 = mk_comb{Rator=t52,Rand=t9}    (* f_p_alpha1_alpha2 A_p *)
        val t54 = mk_t23 (alpha1::alphal) (n+1) (* recursive rest *)
        val t55 = mk_comb{Rator=t53,
                          Rand =t54} (* f_p_alpha1_alpha2 A_p rest *)
        val t60 = mk_comb{Rator=t50,
                          Rand =t51} (* g_alpha2 p_alpha2 *)
       in
        mk_comb{Rator=t60,Rand=t55}
       end
      fun reverse [] =
       []
      | reverse (h::t) =
       (reverse t) @ [h]
      val t23 = mk_t23 (reverse right) 1
      (*
        right side of a definition translation equation: case 3 applied 
        to case 2 applied to case 1
      *)
      fun last [x] =
       x
      | last (x1::(x2::xl)) = 
       last (x2::xl)
      val t24 = if is_constant(f^"_"^(last right)^"_"^rulename) then 
                 mk_const{Name=(f^"_"^(last right)^"_"^rulename),Ty=ty5}
                else
                 fd1
      val t25 = mk_comb{Rator=t24,Rand=t23}
      val t26 = mk_comb{Rator=t25,Rand=t9} 
      val t27 = mk_abs{Bvar=t6,Body=t26}
     in  
      mk_eq{lhs=t11,rhs=t27}
     end
    fun mk_t29 [] =
     []
    | mk_t29 ({name=n,left=(B:string),right=alpha}::pl) =
     (mk_rule n alpha)::(mk_t29 pl)
    val t29 = mk_t29 pl
   in
    t29
   end
  (*
    Global Input:
     DerivationTree_existenc_thm
    Used Functions:
     nPrefix, mk_traverse_terminal, mk_traverse_variable
  *)
  fun mk_traverse () =
   define_mutual_functions 
   {rec_axiom = DerivationTree_existence_thm,
    name      = g^"_DEF1",
    fixities  = SOME (nPrefix ((length V)+(length T))),
    def       = 
    (list_mk_conj (append (map mk_traverse_terminal T)
    (flatten(map mk_traverse_variable V))))}
  (*
    Global Input:
     ty_a, ty_r
    Output:
     new_definition is executed. For startsymbol "S", g="g" and
     init_result_value = --`i`--, it has the form: 
     --`g w = g_S w (\A.i)`--
  *)
  fun mk_translate () =
   let
    (*
      left side
    *)
    val ty1 = mk_type{Args=[ty_a],Tyop=("TY_"^S)} (* :TY_S         *)
    val t1  = mk_var{Name="w",Ty=ty1}             (* w:TY_S        *)
    val ty2 = mk_type{Args=[ty1,ty_r],Tyop="fun"} (* :TY_S->ty_r   *)
    val t2  = mk_var{Name=g,Ty=ty2}              (* g:TY_S->ty_r *)
    val t3  = mk_comb{Rator=t2,Rand=t1}           (* g w          *)
    (*
      right side
    *)
    val ty3 = mk_type{Args=[ty_a,ty_r],Tyop="fun"}   (* :ty_a->ty_r       *)
    val ty4 = mk_type{Args=[ty3,ty_r],Tyop="fun"}    (* :ty_a->ty_r->ty_r *)
    val ty5 = mk_type{Args=[ty1,ty4],Tyop="fun"} (* :TY_S->ty_a->ty_r->ty_r *)
    val t4  = mk_const{Name=(g^"_"^S),Ty=ty5}       (* g_S              *)
    val t5  = mk_var{Name="A",Ty=ty_a}               (* A                 *)
    val t6  = mk_abs{Bvar=t5,Body=init_target_value} (* \A.i              *)
    val t7  = mk_comb{Rator=t4,Rand=t1}              (* g_S w            *)
    val t8  = mk_comb{Rator=t7,Rand=t6}              (* g_S w (\A.A)     *)
   in
    new_definition(g^"_DEF",mk_eq{lhs=t3,rhs=t8})
   end
 in
  (mk_traverse(),mk_translate())
 end;

(*-----------mk_translation-----------------------------------------------*)

(*
  Input:
   a term t of the type of the startsymbol, i.e.
   representing a complete derivative tree
  Output:
   the translation as defined in translate_definition applied to the
   given term
*)
fun mk_translation t = 
 #lhs(dest_eq(concl (SPEC t translate_definition)));

(*----------- translation_CONV ---------------------------------------------*)

(*
  Global Input:
   translation_rules_thms, simplify_translation_CONV, translate_definition
  Input:
   a conversion and a term of the form a returned by mk_translation
  Output:
   the term is stated to be equal to a form, where the translation 
   definitions were expanded and simplified by the given conversion
  Algorithm:
   let translate_definition be of the form |- !w.f w = f1 w (\A.A) and
   the given term of the form --`f t`--. Then:
   t1 is of the form  --`t`--
   th1 is of the form |- f t = f1 t (\A.A)
   th2 is of the form |- f1 t = (\x.f2)
   th3 is of the form |- f t = (\x.f2) (\A.A)
*)
fun translation_CONV t = 
  if (is_comb t)andalso((#Rator(dest_comb t))=
  (#Rator(dest_comb(#lhs(dest_eq(#Body(dest_forall(concl 
  translate_definition))))))))then
   let
    val t1  = #Rand(dest_comb t)
    val th1 = SPEC t1 translate_definition
    val th2 = mutrec_BETA_THEN_APPLY_CONV 
               traverse_definition
               (EVERY_CONV [ONCE_DEPTH_CONV BETA_CONV,
                            PURE_REWRITE_CONV translation_rules_thms,
                            simplify_translation_CONV])
              t1
    val th3 = RIGHT_CONV_RULE(RATOR_CONV (fn t => th2)) th1
   in
    BETA_RULE(BETA_RULE th3)
   end
  else
   raise HOL_ERR{origin_function="TRANSLATION_THEN_APPLY_CONV",
                 origin_structure="new_compiler_definition",
                 message=(term_to_string t)^"\nhas not the form\n"^
                         (term_to_string 
   (#lhs(dest_eq(#Body(dest_forall(concl translate_definition))))))};

(*--------------- compilation definition -----------------------------------*)

val compilation_thm =
 let
  val (k,[x]) = strip_comb(#lhs(dest_eq(#Body(dest_forall(concl
                top_attributation_thm)))))
  val (g,_)   = strip_comb(#lhs(dest_eq(#Body(dest_forall(concl
                translate_definition)))))
  val ty      = mk_type{Args=[type_of x,target_type],Tyop="fun"}
  val t1      = mk_var{Name=compilation,Ty=ty}
  val t2      = mk_comb{Rator=t1,Rand=x}
  val t3      = mk_comb{Rator=k,Rand=x}
  val t4      = mk_comb{Rator=g,Rand=t3}
  val t5      = mk_eq{lhs=t2,rhs=t4}
  val t6      = mk_forall{Bvar=x,Body=t5}
 in
  new_definition(compilation,t6)
 end;

(*--------------- mk_compilation -------------------------------------------*)

fun mk_compilation t =
 #lhs(dest_eq(concl (SPEC t compilation_thm)));

(*--------------- compilation_CONV -----------------------------------------*)

fun compilation_CONV maxl t = 
 let
  val (c,[x])   = strip_comb t 
  val t1        = mk_attributation x
  val th1       = attributation_CONV maxl t1
 in
  (* attributation finished ? *)
  if is_conj(concl th1) then
   (* no *)
   th1
  else
   (* yes *)
   let
    val t2  = mk_translation (#rhs(dest_eq(concl th1)))
    val th2 = translation_CONV t2
    val th3 = SPEC x compilation_thm
    val th4 = RIGHT_CONV_RULE (RAND_CONV (fn t => th1)) th3
   in
    RIGHT_CONV_RULE (fn t => th2) th4
   end
 end;


end; (* struct *)
