(* File: contrib/holML/theories/src/more_lists/mk_more_lists.sml *)

(* Set the path to write the theory to. *)

local
    val path = (!HOLdir)^"contrib/holML/theories/"^
	       Globals.theory_file_type^"/"
in
    val _ = theory_path := path :: (!Globals.theory_path)
end;

val _ = new_theory "more_list";

val _ = add_theory_to_sml "list";

(* fold right  (FOLDR f [a,b] y = f a (f b y)) *)

val FOLDR_DEF = new_recursive_definition
 {name = "FOLDR_DEF",
  fixity = Prefix,
  rec_axiom = list_Axiom,
  def = --`(FOLDR (f:'a->'b->'b) ([]:'a list) (start:'b) = start) /\
           (FOLDR f (CONS x l) start = f x (FOLDR f l start))`--};

(* fold left (FOLDL f [a,b] y = f (f y a) b)  *)

val FOLDL_DEF = new_recursive_definition
 {name = "FOLDL_DEF",
  fixity = Prefix,
  rec_axiom = list_Axiom,
  def = --`(FOLDL (f:'b->'a->'b) ([]:'a list) = \start:'b.start) /\
           (FOLDL f (CONS x l) = \start:'b. (FOLDL f l) (f start x))`--};

val FILTER_DEF = new_recursive_definition
 {name = "FILTER_DEF",
  fixity = Prefix,
  rec_axiom = list_Axiom,
  def = (--`(FILTER pred [] = []) /\
	    (FILTER pred (CONS (hd:'a) tl) =
	     (pred hd => CONS hd (FILTER pred tl) | (FILTER pred tl)))`--)};

(* non-empty lists *)

val nonemptylist_Axiom = define_type{name = "nonemptylist_Axiom",
				     fixities = [Prefix,Prefix],
				     type_spec =
				     `nonemptylist = ONE of 'a
				              | MORE of 'a => nonemptylist`};

val nonemptylist_induction_thm =
    save_thm("nonemptylist_induction_thm",
	      prove_induction_thm nonemptylist_Axiom)
val nonemptylist_cases_thm =
    save_thm("nonemptylist_cases_thm",
	     prove_cases_thm nonemptylist_induction_thm);
val nonemptylist_constructors_one_one =
    save_thm("nonemptylist_constructors_one_one",
    prove_constructors_one_one nonemptylist_Axiom);
val nonemptylist_constructors_distinct =
    save_thm("nonemptylist_constructors_distinct",
	     prove_constructors_distinct nonemptylist_Axiom);

(* mapping functions on nonempty lists *)

val nonempty_MAP_DEF = new_recursive_definition 
    {name = "nonempty_MAP_DEF",
     fixity = Prefix,
     rec_axiom = nonemptylist_Axiom,
     def = (--`(nonempty_MAP (f:'a -> 'b) (ONE x) = ONE (f x)) /\
	       (nonempty_MAP f (MORE x xs) =
		MORE (f x) (nonempty_MAP f xs))`--)};

(* fold right on nonempty lists *) 

val nonempty_FOLDR_DEF = new_recursive_definition
 {name = "nonempty_FOLDR_DEF",
  fixity = Prefix,
  rec_axiom = nonemptylist_Axiom,
  def = --`(nonempty_FOLDR (f:'a->'b->'b) (start:'b) (ONE x) = f x start) /\
             (nonempty_FOLDR f start (MORE y l) =
	      f y (nonempty_FOLDR f start l))`--};


(* This definition of "foldr" is different from the usual definition *)
(* on (possibly empty) lists since I can use a starting value        *)
(* provided by the list:                                             *)
(* nonempty_FOLDR_TO_ONE f [a,b,c] = f a (f b c)                           *)

val nonempty_FOLDR_TO_ONE_DEF = new_recursive_definition
 {name = "nonempty_FOLDR_TO_ONE_DEF",
  fixity = Prefix,
  rec_axiom = nonemptylist_Axiom,
  def = --`(nonempty_FOLDR_TO_ONE (f:'a->'a->'a) (ONE x) = x) /\
           (nonempty_FOLDR_TO_ONE f (MORE y l) =
	    f y (nonempty_FOLDR_TO_ONE f l))`--};


val nonempty_FOLDL_DEF = new_recursive_definition
 {name = "nonempty_FOLDL_DEF",
  fixity = Prefix,
  rec_axiom = nonemptylist_Axiom,
  def = (--`(nonempty_FOLDL start (f:'b -> 'a ->'b) (ONE x) = f start x) /\
	    (nonempty_FOLDL start f (MORE x xs) =
	     nonempty_FOLDL (f start x) f xs)`--)};


val nonempty_FOLDL_WITH_INIT_DEF = new_recursive_definition
    {name = "nonempty_FOLDL_WITH_INIT_DEF",
     fixity = Prefix,
     rec_axiom = nonemptylist_Axiom,
     def = (--`(nonempty_FOLDL_WITH_INIT f (ONE x) = (x:'a)) /\
	       (nonempty_FOLDL_WITH_INIT f (MORE x xs) =
		nonempty_FOLDL x f xs)`--)};
	   
val option_Axiom =
    define_type{name = "option_Axiom", fixities = [Prefix,Prefix],
		type_spec = `option = NONE | SOME of 'a`};

val option_induction_thm =
    save_thm("option_induction_thm",
	      prove_induction_thm option_Axiom)
val option_cases_thm =
    save_thm("option_cases_thm",
	     prove_cases_thm option_induction_thm);
val option_constructors_one_one =
    save_thm("option_constructors_one_one",
    prove_constructors_one_one option_Axiom);
val option_constructors_distinct =
    save_thm("option_constructors_distinct",
	     prove_constructors_distinct option_Axiom);


val SOME_arg_DEF = new_recursive_definition
    {name = "SOME_arg_DEF", fixity = Prefix, rec_axiom = option_Axiom,
     def = (--`SOME_arg (SOME (x:'a)) = x`--)};


val _ = export_theory ();
