(********
The theorems to prove are the analogies of the following ones, for 
a non-mutually recursive type:

val foo_Axiom = define_type{name = "foo_Axiom",
			    fixities = [Prefix,Prefix,Prefix,Prefix],
			    type_spec =
			    `foo = FOO1 of 'a
			         | FOO2 of ('a # 'a)
                                 | FOO3 of ('a # num # bool)
                                 | FOO4 of ('a # num # 'a # bool)`};

val foo_induction_thm = prove_induction_thm foo_Axiom;
val foo_cases_thm = prove_cases_thm foo_induction_thm;
val foo_constructors_one_one = prove_constructors_one_one foo_Axiom;
val foo_constructors_distinct = prove_constructors_distinct foo_Axiom;

Constructors are distinct:
- val foo_constructors_distinct =
  |- (!x1 x0 x. ~(FOO1 x = FOO2 x0 x1)) /\
     (!b n x' x. ~(FOO1 x = FOO3 x' n b)) /\
     (!b x1 n x0 x. ~(FOO1 x = FOO4 x0 n x1 b)) /\
     (!b n x x1 x0. ~(FOO2 x0 x1 = FOO3 x n b)) /\
     (!b x1' n x0' x1 x0. ~(FOO2 x0 x1 = FOO4 x0' n x1' b)) /\
     (!b' x1 n' x0 b n x. ~(FOO3 x n b = FOO4 x0 n' x1 b')) : thm

Constructors are 1-1:
- val foo_constructors_one_one =
  |- (!x x'. (FOO1 x = FOO1 x') = x = x') /\
     (!x0 x1 x0' x1'.
       (FOO2 x0 x1 = FOO2 x0' x1') = (x0 = x0') /\ (x1 = x1')) /\
     (!x n b x' n' b'.
       (FOO3 x n b = FOO3 x' n' b') = (x = x') /\ (n = n') /\ (b = b')) /\
     (!x0 n x1 b x0' n' x1' b'.
       (FOO4 x0 n x1 b = FOO4 x0' n' x1' b') =
       (x0 = x0') /\ (n = n') /\ (x1 = x1') /\ (b = b')) : thm

Constructors are onto:
- val foo_cases_thm =
  |- !f.
       (?x. f = FOO1 x) \/
       (?x0 x1. f = FOO2 x0 x1) \/
       (?x n b. f = FOO3 x n b) \/
       (?x0 n x1 b. f = FOO4 x0 n x1 b) : thm

**********)

(* This functions proves that constructors are distinct, ie, for each TY
   among the mutually recursive types, if CON1 and CON2 are two different
   constructors, we will prove that a term of type TY constructed with
   the constructor CON1 cannot be equal to one constructed with the
   CON2 constructor, and so on.
   BUG: this cannot be used twice, as it defines some functions (named
   dist_aux_ftn_TY for each type TY of the mutually recursive types),
   so an attempt to do it again will result in a attempt to define these
   functions. *)

fun prove_mutual_constructors_distinct rec_thm =

let

    (* decompose takes as arguments a term that is a constructor applied
       to some args and the list of args stripped off so far; it strips
       off the rest of the args, returning the constructor by itself
       and the complete list of args *)
    fun decompose (tm, args_so_far) =
        if is_comb tm then
            let val {Rator, Rand} = dest_comb tm in
                decompose (Rator, Rand :: args_so_far)
            end
        else
            (tm, args_so_far)

(* the first thing I want to to is tear apart rec_thm to find out what 
   all the constructors and their args are *)
val temp = map strip_forall
    (strip_conj (snd (strip_exists
		      (snd (strip_forall (concl (rec_thm)))))))
val applied_cons_list = map (fn x => rand (lhs (snd x))) temp
(* now need to divide the this list up into separate lists, one for each 
   type in the mutually recursive type set, to get this going, send
   in true as first_item, and [] as current_sublist and completed_sublists,
   and any type whatsoever as current_type *)
fun divide_list first_item (item::rest_list) current_type current_sublist
    completed_sublists =
    let val new_type = type_of item
    in
	if first_item orelse (new_type = current_type) then
	    divide_list false rest_list new_type (item::current_sublist)
	    completed_sublists
	else
	    divide_list false rest_list new_type [item]
	    ((rev current_sublist)::completed_sublists)
    end
  | divide_list first_item  [] current_type current_sublist
    completed_sublists =
    (rev ((rev current_sublist)::completed_sublists))
val divided_list = divide_list true applied_cons_list (==`:bool`==) [] []
val temp = map (map (fn x => decompose (x, []))) divided_list
val cons_var_list = map split temp
(* Now we need to generate some new variable names for the arguments.
   We will need to generate clauses like
   ~(CONS1 <args for CONS1> = CONS2 <args for CONS2>)
   and the problem is that the args for CONS1, which are variables,
   may have the same name as the args for CONS2, and we need to qualify
   over all of them separately. *)
val all_vars = flatten (flatten (map snd cons_var_list))
(* note all_vars is used below, not as a parameter *)
fun add_differently_named_vars (cons_list, vars_list) = 
    let val new_vars_list = 
	map (fn y => map (fn x => variant all_vars x) y) vars_list
    in
	(cons_list, vars_list, new_vars_list)
    end
val cons_var_newvar_list = map add_differently_named_vars cons_var_list

fun make_ineq cons1 x_args cons2 y_args =
    let val eq_term = mk_eq {lhs = list_mk_comb (cons1, x_args),
			     rhs = list_mk_comb (cons2, y_args)}
	val not_eq_term = mk_comb {Rator = --`~`--, Rand = eq_term}
	val temp_result = list_mk_forall (y_args, not_eq_term)
    in
	list_mk_forall (x_args, temp_result)
    end

(* the following function takes the constructor first in the list, (say
   it is CONS1) and combines it, in turn, with the rest of the constructors
   on the list (say they are CONS2 ... CONS7), into items that look like
   !<x_args for CONS1> <y_args for CONS2>.
         ~(CONS1 <x_args for CONS1> = CONS2 <y_args for CONS2>)
                   ...
   !<x_args for CONS1> <y_args for CONS7>.
         ~(CONS1 <x_args for CONS1> = CONS7 <y_args for CONS7>)    *)
fun mk_conjuncts
    cons1 cons1_x_args (cons2::more_cons) (cons2_y_args::more_args) =
    (make_ineq cons1 cons1_x_args cons2 cons2_y_args)::
    mk_conjuncts cons1 cons1_x_args more_cons more_args
  | mk_conjuncts cons1 cons1_x_args [] [] = []
  | mk_conjuncts _ _ _ _ = raise HOL_ERR
    {message = "improper constructor or variable args",
     origin_function = "mk_conjuncts",
     origin_structure = "prove_mutual_constructors_distinct"}

(* this function makes all the conjuncts for one type *)
fun mk_all_conjuncts (con::cons_list, 
		      x_args::x_args_list, y_args::y_args_list) = 
    if (cons_list = []) then
	([] : term list)
    else
	(mk_conjuncts con x_args cons_list y_args_list)@
	(mk_all_conjuncts (cons_list, x_args_list, y_args_list))
  | mk_all_conjuncts (_, _, _) = raise HOL_ERR
    {message = "improper constructor or variable args",
     origin_function = "mk_all_conjuncts",
     origin_structure = "prove_mutual_constructors_distinct"}
val conjuncts_list = map mk_all_conjuncts cons_var_newvar_list
(* now, the problem is that there may be types that have only one 
   constructor, so the list of conjuncts may be empty, so we have
   to filter out these empty lists *)
val filtered_list = filter (fn x => x <> []) conjuncts_list
(* goals is a list, containining one goal for each type;
   each goal says that the the constructors for that type are distinct *)
val goals = map list_mk_conj filtered_list

(* Now I need to define functions (I call then distinctness functions)
   that return a different (natural) number
   when applied to items constructed with each constructor *)

val num_ty = ==`:num`==
fun mk_function_variable the_type =
    mk_var {Name = "dist_aux_ftn_"^(#Tyop (dest_type the_type)),
	    Ty = mk_type {Tyop = "fun", Args = [the_type, num_ty]}}
fun mk_def_term ftn_var old_type (app_con::app_con_list) count = 
    let val new_type = type_of app_con
	val new_ftn_var = 
	    if new_type = old_type then	ftn_var
	    else mk_function_variable new_type
	val new_conjunct =
	    mk_eq {lhs = mk_comb {Rator = new_ftn_var, Rand = app_con},
		   rhs = mk_const {Name = Lib.int_to_string count,
				   Ty = num_ty}}
    in
	if app_con_list = [] then
	    new_conjunct
	else
	    mk_conj {conj1 = new_conjunct,
		     conj2 = mk_def_term new_ftn_var new_type app_con_list
		             (count + 1)}
    end
  | mk_def_term _ _ [] _ = raise HOL_ERR
    {message = "empty constructor list",
     origin_function = "mk_all_conjuncts",
     origin_structure = "prove_mutual_constructors_distinct"}
(* the conjuncts of def_term say that there are a bunch of functions (the
   distinctness functions), one for each type, and they all return
   different numbers when applied to terms made from different
   constructors *)
val def_term = 
    let val old_type = type_of (hd applied_cons_list)
    in
	mk_def_term (mk_function_variable old_type) old_type 
	applied_cons_list 0
    end
val dist_aux_ftns_thm = define_mutual_functions rec_thm def_term

(* OK, now the way that we go about proving the theorem is this -- 
   we need to prove, for example,
         ~(CON1 <args for CON1> = CON2 <args for CON2>)
   using STRIP_TAC, this breaks down to showing
         CON1 <args for CON1> = CON2 <args for CON2> ==> F
   So we assume
         CON1 <args for CON1> = CON2 <args for CON2>
   We apply the appropriate distinctness function, getting
         n1 = n2
   where n1 and n2 are two different natural numbers.
   We apply num_EQ_CONV and get 
         F   
   and we're done *)

fun solve_goal_tac dist_ftn (asms, gl) =
    let val asm = hd asms
	val thm1 = AP_TERM dist_ftn (ASSUME asm)
	val thm2 = REWRITE_RULE [dist_aux_ftns_thm] thm1
	val thm3 = CONV_RULE Num_lib.num_EQ_CONV thm2
    in
	ACCEPT_TAC thm3 (asms, gl)
    end

fun mk_function_const the_type =
    mk_const {Name = "dist_aux_ftn_"^(#Tyop (dest_type the_type)),
	      Ty = mk_type {Tyop = "fun", Args = [the_type, num_ty]}}

fun prove_one_type_distinct gl =
    let val one_conj = if is_conj gl then (#conj1 (dest_conj gl)) else gl
	val the_type = type_of (lhs (rand (snd (strip_forall one_conj))))
	val dist_ftn = mk_function_const the_type
    in
	TAC_PROOF (([], gl),
		   REPEAT STRIP_TAC THEN solve_goal_tac dist_ftn)
    end

val distinctness_theorems = map prove_one_type_distinct goals

in
    distinctness_theorems
end   (* of prove_mutual_constructors_distinct *)





val rec_thm = MLpat_rec_thm;

    (* decompose takes as arguments a term that is a constructor applied
       to some args and the list of args stripped off so far; it strips
       off the rest of the args, returning the constructor by itself
       and the complete list of args *)
    fun decompose (tm, args_so_far) =
        if is_comb tm then
            let val {Rator, Rand} = dest_comb tm in
                decompose (Rator, Rand :: args_so_far)
            end
        else
            (tm, args_so_far)

(* the first thing I want to to is tear apart rec_thm to find out what 
   all the constructors and their args are *)
val temp = map strip_forall
    (strip_conj (snd (strip_exists
		      (snd (strip_forall (concl (rec_thm)))))))
val applied_cons_list = map (fn x => rand (lhs (snd x))) temp
(* now need to divide the this list up into separate lists, one for each 
   type in the mutually recursive type set, to get this going, send
   in true as first_item, and [] as current_sublist and completed_sublists,
   and any type whatsoever as current_type *)
fun divide_list first_item (item::rest_list) current_type current_sublist
    completed_sublists =
    let val new_type = type_of item
    in
	if first_item orelse (new_type = current_type) then
	    divide_list false rest_list new_type (item::current_sublist)
	    completed_sublists
	else
	    divide_list false rest_list new_type [item]
	    ((rev current_sublist)::completed_sublists)
    end
  | divide_list first_item  [] current_type current_sublist
    completed_sublists =
    (rev ((rev current_sublist)::completed_sublists))
val divided_list = divide_list true applied_cons_list (==`:bool`==) [] []
val temp = map (map (fn x => decompose (x, []))) divided_list

(* At this stage, I will eliminate from the list the constructors 
   that have no arguments, since they won't be needed in the theorem *)
val temp2 = map (filter (fn x => snd x <> [])) temp

val cons_var_list = map split temp2
(* Now we need to generate some new variable names for the arguments.
   We will need to generate clauses like
   ~(CONS1 <args for CONS1> = CONS2 <args for CONS2>)
   and the problem is that the args for CONS1, which are variables,
   may have the same name as the args for CONS2, and we need to qualify
   over all of them separately. *)
val all_vars = flatten (flatten (map snd cons_var_list))
(* note all_vars is used below, not as a parameter *)
fun add_differently_named_vars (cons_list, vars_list) = 
    let val new_vars_list = 
	map (fn y => map (fn x => variant all_vars x) y) vars_list
    in
	(cons_list, vars_list, new_vars_list)
    end
val cons_var_newvar_list = map add_differently_named_vars cons_var_list

fun mk_var_eq_conj (x_var::x_vars) (y_var::y_vars) =
    if x_vars = [] then
	mk_eq {lhs = x_var, rhs = y_var}
    else
	mk_conj {conj1 = mk_eq {lhs = x_var, rhs = y_var},
		 conj2 = mk_var_eq_conj x_vars y_vars}
  | mk_var_eq_conj _ _ = raise HOL_ERR
    {message = "different number of args",
     origin_function = "mk_var_eq_conj",
     origin_structure = "prove_mutual_constructors_one_one"}

fun mk_1_1_statement con x_vars y_vars =
    let val appl_x = list_mk_comb (con, x_vars)
	val appl_y = list_mk_comb (con, y_vars)
	val left = mk_eq {lhs = appl_x, rhs = appl_y}
	val eq_term = mk_eq {lhs = left, 
			     rhs = mk_var_eq_conj x_vars y_vars}
	val forall_term = list_mk_forall (y_vars, eq_term)
    in
	list_mk_forall (x_vars, forall_term)
    end

fun mk_goal_for_one_type (con::cons_list, x_vars::x_vars_list, 
		       y_vars::y_vars_list) =
    if (cons_list = []) then
	mk_1_1_statement con x_vars y_vars
    else
	mk_conj {conj1 = mk_1_1_statement con x_vars y_vars,
		 conj2 = mk_goal_for_one_type (cons_list, x_vars_list,
					       y_vars_list)}
  | mk_goal_for_one_type (_, _, _) = raise HOL_ERR
    {message = "different number of conses or args",
     origin_function = "mk_goal_for_one_type",
     origin_structure = "prove_mutual_constructors_one_one"}

val goals = map mk_goal_for_one_type cons_var_newvar_list

(* STOPPED HERE
   Now I that have the goals, I need to know how to prove them... *)

(*
foo_constructors_one_one = prove_constructors_one_one foo_Axiom;

- val foo_constructors_one_one =
  |- (!x x'. (FOO1 x = FOO1 x') = x = x') /\
     (!x0 x1 x0' x1'.
       (FOO2 x0 x1 = FOO2 x0' x1') = (x0 = x0') /\ (x1 = x1')) /\
     (!x n b x' n' b'.
       (FOO3 x n b = FOO3 x' n' b') = (x = x') /\ (n = n') /\ (b = b')) /\
     (!x0 n x1 b x0' n' x1' b'.
       (FOO4 x0 n x1 b = FOO4 x0' n' x1' b') =
       (x0 = x0') /\ (n = n') /\ (x1 = x1') /\ (b = b')) : thm
*)

