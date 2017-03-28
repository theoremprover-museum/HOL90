(* File: contrib/holML/theories/src/finmap/mk_finmap.sml *)

local
    val path = (!HOLdir)^"contrib/holML/theories/"^
	       Globals.theory_file_type^"/"
in
    val _ = theory_path := path :: (!Globals.theory_path)
end;

val _ = new_theory "finmap";

val _ = new_parent "more_list"
val _ = use ((!HOLdir)^"contrib/holML/theories/src/more_list/more_list.sml");

val _ = load_library_in_place (find_library "part_fun");
val _ = add_theory_to_sml "lift";
val _ = add_theory_to_sml "partial_functions";

val _ = load_library_in_place num_lib;

val finmap_Axiom = define_type 
{name = "finmap_Axiom", 
 fixities = [Prefix],
 type_spec = `finmap = FINMAP of 'a`};

val finmap_constructors_one_one =
    save_thm("finmap_constructors_one_one",
             prove_constructors_one_one finmap_Axiom)
val finmap_induction_thm =
    save_thm("finmap_induction_thm", prove_induction_thm finmap_Axiom)
val finmap_cases_thm =
    save_thm("finmap_cases_thm", prove_cases_thm finmap_induction_thm)


val FINMAP_arg_DEF = new_recursive_definition
    {name = "FINMAP_arg_DEF", fixity = Prefix, rec_axiom = finmap_Axiom,
     def = --`FINMAP_arg (FINMAP (l:'a)) = l`--}

val empty_finmap_DEF = new_definition
("empty_finmap_DEF",
 --`(empty_finmap:(('a#'b))list finmap) = (FINMAP NIL)`--)

val list_lookup_DEF =
    new_recursive_definition
    {name = "list_lookup_DEF",
     fixity = Prefix,
     rec_axiom = list_Axiom,
     def = (--`(list_lookup key NIL = undefined) /\
	       (list_lookup key (CONS (h:('a # 'b)) t) = 
		((key = (FST h)) => lift (SND h) | list_lookup key t))`--)};

val finmap_lookup_DEF =
    new_recursive_definition
    {name = "finmap_lookup_DEF",
     fixity = Prefix,
     rec_axiom = finmap_Axiom,
     def = (--`finmap_lookup key (FINMAP l) = 
                 list_lookup key (l:('a # 'b) list)`--)};

(* insert things so that list is ordered, smallest keys at the front *)
val list_insert_DEF =
    new_recursive_definition
    {name = "list_insert_DEF",
     fixity = Prefix,
     rec_axiom = list_Axiom,
     def = (--`(list_insert less key item NIL = CONS (key, item) NIL) /\
	       (list_insert less key item (CONS (h:'a # 'b) t) =
		 (less (FST h) (key) => CONS h (list_insert less key item t) |
                  (key = (FST h) => CONS (key, item) t |
		   CONS (key, item) (CONS h t))))`--)}

val finmap_insert_DEF =
    new_recursive_definition
    {name = "finmap_insert_DEF",
     fixity = Prefix,
     rec_axiom = finmap_Axiom,
     def = (--`finmap_insert less key item (FINMAP l) = 
                 FINMAP (list_insert less key item (l:('a # 'b) list))`--)};

(* finmap_modify f g returns map f modified by g; in other words,
   Dom (finmap_modify f g) = (Dom f) union (Dom g) and
   (finmap_modify f g)(x) = if x in Dom g then g(x) else f(x) *)

val list_modify_DEF = new_recursive_definition
    {name = "list_modify_DEF", fixity = Prefix, rec_axiom = list_Axiom,
     def = --`(list_modify less f NIL = f) /\
	      (list_modify less f (CONS (h:'a # 'b) t) =
		list_modify less (list_insert less (FST h) (SND h) f) t)`--}

val finmap_modify_DEF = new_definition
("finmap_modify_DEF",
 --`finmap_modify less (f:(('a#'b)list)finmap) g = 
    (f = empty_finmap => g
      | FINMAP (list_modify less (FINMAP_arg f) (FINMAP_arg g)))`--)

local
   val temp = ISPEC (--`\l. (f:(('a#'b)list)finmap) = FINMAP l`--) SELECT_AX
   val temp2 = PURE_REWRITE_RULE [FORALL_IMP_CONV (concl temp)] temp
   val select2 = SPEC (--`f:(('a#'b)list)finmap`--) (BETA_RULE (GEN_ALL temp2))
   val foo1 = MP select2 (ISPEC (--`f:(('a#'b)list)finmap`--) finmap_cases_thm)
   val foo2 = PURE_REWRITE_RULE [FINMAP_arg_DEF]
       (AP_TERM (--`FINMAP_arg:(('a#'b)list)finmap -> ('a#'b)list`--) foo1) 
in
    val empty_finmap_is_zero = save_thm
    ("empty_finmap_is_zero",
     TAC_PROOF
     (([], --`!less (f:(('a#'b)list)finmap). 
	          (finmap_modify less empty_finmap f = f) /\
	          (finmap_modify less f empty_finmap = f)`--),
      REPEAT GEN_TAC THEN REWRITE_TAC [finmap_modify_DEF] THEN
      COND_CASES_TAC THENL
      [ACCEPT_TAC (SYM 
		   (ASSUME (--`(f:(('a#'b)list)finmap) = empty_finmap`--))),
       REWRITE_TAC [empty_finmap_DEF, list_modify_DEF, FINMAP_arg_DEF] THEN
       (* at this point the subgoal looks like FINMAP (FINMAP_arg f) = f;
	the following tactics, and the local defs above are a general
	method for solving this sort of problem *)
       ONCE_REWRITE_TAC [foo2] THEN SUBST_OCCS_TAC [([2], foo1)] THEN
       REFL_TAC]))
end

val list_max_DEF =
    new_recursive_definition
    {name = "list_max_DEF",
     fixity = Prefix,
     rec_axiom = list_Axiom,
     def = (--`(list_max (NIL:num list) = 0) /\
               (list_max (CONS n l) =
		 ((list_max l < n) => n | list_max l))`--)};

val list_member_DEF =
    new_recursive_definition
    {name = "list_member_DEF",
     fixity = Prefix,
     rec_axiom = list_Axiom,
     def = (--`(list_member item (NIL:'a list) = F) /\
               (list_member item (CONS h t) = 
		((h = item) => T | list_member item t))`--)};

val list_prop = --`\l. !n. list_member n l ==> (n <= list_max l)`--

val thm1 = TAC_PROOF 
(([], --`^list_prop []`--),
 BETA_TAC THEN GEN_TAC THEN REWRITE_TAC [list_member_DEF, list_max_DEF])

val thm2 = TAC_PROOF 
(([], --`!t. ^list_prop t ==> (!h. ^list_prop (CONS h t))`--),
    BETA_TAC THEN GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN GEN_TAC THEN
    REWRITE_TAC [list_member_DEF, list_max_DEF] THEN COND_CASES_TAC THENL
    [REWRITE_TAC [ASSUME (--`(h:num) = n`--)] THEN COND_CASES_TAC THENL
     [REWRITE_TAC [theorem "arithmetic" "LESS_EQ_REFL"],
      ACCEPT_TAC (PURE_REWRITE_RULE [theorem "arithmetic" "NOT_LESS"]
		  (ASSUME (--`~(list_max t < n)`--)))],
     DISCH_TAC THEN COND_CASES_TAC THENL
     (let val lt_thm = MATCH_MP
	  (ASSUME (--`!n. list_member (n:num) t ==> n <= list_max t`--))
	      (ASSUME (--`list_member (n:num) t`--))
	  val thm1 = MATCH_MP
	      (theorem "arithmetic" "LESS_IMP_LESS_OR_EQ")
	      (ASSUME (--`list_max t < h`--))
	  val thm2 = MATCH_MP
	      (theorem "arithmetic" "LESS_EQ_TRANS") 
	      (CONJ lt_thm thm1) in
	      [ACCEPT_TAC thm2, ACCEPT_TAC lt_thm] end)])

(* |- !l n. list_member n l ==> n <= list_max l *)
val max_member_thm =
BETA_RULE (MP (ISPEC list_prop list_INDUCT) (CONJ thm1 thm2))

(* |- m < SUC m *)
val thm3 = MATCH_MP 
    (theorem "arithmetic" "LESS_EQ_IMP_LESS_SUC")
    (SPEC (--`m:num`--) (theorem "arithmetic" "LESS_EQ_REFL"))

(* |- !n m. n <= m ==> n < SUC m *)
val thm4 = TAC_PROOF
    (([], --`!n m. n <= m ==> n < SUC m`--),
	GEN_TAC THEN GEN_TAC THEN
	PURE_REWRITE_TAC [definition "arithmetic" "LESS_OR_EQ"] THEN
	STRIP_TAC THENL
	[ACCEPT_TAC (MATCH_MP (theorem "arithmetic" "LESS_TRANS")
		     (CONJ (ASSUME (--`n < m`--)) thm3)),
	 ASM_REWRITE_TAC [thm3]])

(* suc_max_greater: |- !l n. list_member n l ==> n < SUC (list_max l) *)
local val vars = [--`l:num list`--, --`n:num`--] 
in
    val suc_max_greater = 
	GENL vars
	(IMP_TRANS (SPECL vars max_member_thm)
	 (SPECL [--`n:num`--, --`list_max l`--] thm4))
end

(* less_imp_not_eq: |- !n m. m < n ==> ~(n = m) *)
local val blah2 = REWRITE_RULE [definition "arithmetic" "LESS_OR_EQ"] 
               (theorem "arithmetic" "NOT_LESS")
      val blah4 = snd (EQ_IMP_RULE (SPEC_ALL blah2))
      val blah6 = REWRITE_RULE [DE_MORGAN_THM] (CONTRAPOS blah4)
      val blah7 = UNDISCH blah6
      val blah8 = DISCH (hd (hyp blah7)) (CONJUNCT2 blah7)
in
    val less_imp_not_eq = GEN_ALL blah8
end

(* |- !l n. list_member n l ==> ~(SUC (list_max l) = n) *)
val member_imp_not_suc_max =
GEN_ALL
(IMP_TRANS (SPEC_ALL suc_max_greater)
 (SPECL [--`SUC (list_max l)`--, --`n:num`--] less_imp_not_eq))

(* |- !l. ~(list_member (SUC (list_max l)) l) *)
val suc_max_not_member = GEN_ALL
(REWRITE_RULE [] 
    (CONTRAPOS (SPECL [--`l:num list`--, --`SUC (list_max l)`--]
		member_imp_not_suc_max)))

(* |- !l. ?n. ~(list_member n l) *)
val exists_not_member = 
TAC_PROOF 
(([], --`!(l:num list). ?n. ~(list_member n l)`--),
 GEN_TAC THEN EXISTS_TAC (--`SUC (list_max l)`--) THEN
 ACCEPT_TAC (SPEC_ALL suc_max_not_member))

val dom_list_helper_DEF =
    new_recursive_definition
    {name = "dom_list_helper_DEF",
     fixity = Prefix,
     rec_axiom = list_Axiom,
     def = (--`(dom_list_helper (NIL:('a # 'b) list) = (NIL:'a list)) /\
               (dom_list_helper (CONS h t) =
                      (CONS (FST h) (dom_list_helper t)))`--)}

val dom_list_DEF =
    new_recursive_definition
    {name = "dom_list_DEF",
     fixity = Prefix,
     rec_axiom = finmap_Axiom,
     def = (--`dom_list (FINMAP l) = dom_list_helper (l:('a # 'b) list)`--)}


val finmap_dom_DEF =
    new_recursive_definition
    {name = "finmap_dom_DEF",
     fixity = Prefix,
     rec_axiom = finmap_Axiom,
     def = (--`finmap_dom (FINMAP l) =
	    FOLDR (\ (x:'a # 'b) s.(FST x) INSERT s) l {}`--)};

val finmap_range_DEF =
    new_recursive_definition
    {name = "finmap_range_DEF",
     fixity = Prefix,
     rec_axiom = finmap_Axiom,
     def = (--`finmap_range (FINMAP l) =
	    FOLDR (\ (x:'a # 'b) s.(SND x) INSERT s) l {}`--)};

val restrict_finmap_DEF =
    new_recursive_definition
    {name = "restrict_finmap_DEF",
     fixity = Prefix,
     rec_axiom = finmap_Axiom,
     def = (--`restrict_finmap (FINMAP f) set =
	    FINMAP(FILTER (\x:'a # 'b. FST x IN set) f)`--)};

val bij_inv_DEF = new_definition
("bij_inv_DEF",
 --`bij_inv (f1:'a -> 'b) (f2:'b -> 'a) = (ONE_ONE f1) /\ (ONTO f1) /\
    (!(a:'a). f2 (f1 a) = a) /\ (!(b:'b). f1 (f2 b) = b)`--)

val _ = load_library_in_place (find_library "utils");

open ExtraGeneralFunctions;

(* f_one_one_member:
   |- !l a f. ONE_ONE f ==> (list_member a l = list_member (f a) (MAP f l)) *)
local val list_prop2 = 
          --`\l. list_member (a:'a) l ==> 
	      list_member ((f:'a->'b) a) (MAP f l)`--
      val tmp_thm = BETA_RULE (SPEC list_prop2 list_INDUCT)
      val tmp_thm2 = DISCH_ALL (SPEC_ALL (UNDISCH tmp_thm))
      val map_thm = definition "list" "MAP"
      val tmp_thm3 = CONTRAPOS 
	  (SPECL [--`h:'a`--, --`a:'a`--] 
	   (ASSUME (--`!x1 x2. ((f:'a->'b) x1 = f x2) ==> (x1 = x2)`--)))
      val tmp_thm4 = MP tmp_thm3 (ASSUME (--`~((h:'a) = a)`--))
      val list_prop3 =
	  --`\l. list_member ((f:'a->'b) a) (MAP f l) ==> 
	      list_member (a:'a) l`--
      val tmp_thm5 = BETA_RULE (SPEC list_prop3 list_INDUCT)
      val tmp_thm6 = DISCH_ALL (SPEC_ALL (UNDISCH tmp_thm5))
      val tmp_thm7 = SPECL [--`h:'a`--, --`a:'a`--] 
	  (ASSUME (--`!x1 x2. ((f:'a->'b) x1 = f x2) ==> (x1 = x2)`--))
      val tmp_thm8 = MP tmp_thm7 (ASSUME (--`(f:'a->'b) h = f a`--))
      val tmp_thm9 = CONTRAPOS (DISCH_ALL 
		(AP_TERM (--`f:'a->'b`--) (ASSUME (--`(h:'a) = a`--))))
      val tmp_thm10 = MP tmp_thm9 (ASSUME (--`~((f:'a->'b) h = f a)`--))
in
    val f_one_one_member = 
	TAC_PROOF
	(([], --`!l (a:'a) (f:'a->'b). (ONE_ONE f) ==> 
	    ((list_member a l) = (list_member (f a) (MAP f l)))`--),
	 REPEAT GEN_TAC THEN PURE_REWRITE_TAC [ONE_ONE_DEF] THEN
	 DISCH_TAC THEN EQ_TAC THENL
	 [MP_IMP_TAC tmp_thm2 THEN REWRITE_TAC [list_member_DEF] THEN
	  GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN COND_CASES_TAC THENL
	  [DISCH_TAC THEN 
	   REWRITE_TAC [ASSUME (--`(h:'a) = a`--), map_thm, list_member_DEF],
	   REWRITE_TAC [map_thm, list_member_DEF, tmp_thm4] THEN
	   FIRST_ASSUM ACCEPT_TAC],
	  MP_IMP_TAC tmp_thm6 THEN REWRITE_TAC [map_thm, list_member_DEF]
	  THEN GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN COND_CASES_TAC THENL
	  [DISCH_TAC THEN REWRITE_TAC [tmp_thm8],
	   REWRITE_TAC [tmp_thm10] THEN FIRST_ASSUM ACCEPT_TAC]])
end

val o_DEF = definition "combin" "o_DEF"

(* map_comp: |- !l f1 f2. MAP f2 (MAP f1 l) = MAP (f2 o f1) l *)
local val list_prop = --`\(l:'a list). !f1 f2. 
          MAP (f2:'b->'c) (MAP f1 l) = MAP (f2 o f1) l`--
      val tmp_thm = BETA_RULE (ISPEC list_prop list_INDUCT)
      val map_thm = definition "list" "MAP"
in
    val map_comp = TAC_PROOF
    (([],
      --`!l (f1:'a->'b) (f2:'b->'c). MAP f2 (MAP f1 l) = MAP (f2 o f1) l`--),
     MP_IMP_TAC tmp_thm THEN REWRITE_TAC [map_thm] THEN
     GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
     ASM_REWRITE_TAC [o_DEF] THEN
     BETA_TAC THEN REFL_TAC)
end

(* bij_imp_map_id:
    |- !l f1 f2. bij_inv f1 f2 ==> (MAP (f1 o f2) l = l) *)
local
    val list_prop = --`\(l:'a list). !(f1:'b->'a) (f2:'a->'b).
	(bij_inv f1 f2) ==> ((MAP (f1 o f2) l) = l)`--
    val tmp_thm = BETA_RULE (SPEC list_prop list_INDUCT)
    val map_thm = definition "list" "MAP"
    val bij_thm = PURE_REWRITE_RULE [bij_inv_DEF]
	  (ASSUME (--`bij_inv f1 (f2:'a->'b)`--))
    val tmp_thm2 = CONJUNCT2 (CONJUNCT2 (CONJUNCT2 bij_thm))
    val thm_thm3 = MP (SPEC_ALL 
	(ASSUME (--`!(f1:'b->'a) f2.
		 bij_inv f1 f2 ==> (MAP (f1 o f2) t = t)`--))) 
	(ASSUME (--`bij_inv (f1:'b->'a)  f2`--))
in
    val bij_imp_map_id = TAC_PROOF
	(([], --`!(l:'a list) (f1:'b->'a) (f2:'a->'b). (bij_inv f1 f2) ==> 
	    ((MAP (f1 o f2) l) = l)`--),
	    MP_IMP_TAC tmp_thm THEN REWRITE_TAC [map_thm] THEN
	    GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN 
	    DISCH_TAC THEN REWRITE_TAC [o_DEF, tmp_thm2, thm_thm3] THEN
	    BETA_TAC THEN REFL_TAC)
end

val bij_term = --`bij_inv from_num (to_num:'a->num)`--

(* exists_not_dom:
    |- !f.
       (?from_num to_num. bij_inv from_num to_num) ==>
       (?x. ~(list_member x (dom_list f))) *)
local val tm1 = --`(from_num:num->'a) 
          (SUC (list_max (MAP to_num (dom_list (f:(('a#'b)list)finmap)))))`--
      val tmp_thm = SPEC 
	  (--`MAP (to_num:'a->num) (dom_list (f:(('a#'b)list) finmap))`--)
	  suc_max_not_member
      val bij_thm1 = ASSUME bij_term
      val bij_thm = PURE_REWRITE_RULE [bij_inv_DEF] bij_thm1
      val tmp_thm2 = CONJUNCT1 bij_thm
      val tmp_thm3 = ISPECL 
	  [--`MAP (to_num:'a->num) (dom_list (f:(('a#'b)list)finmap))`--,
	   --`SUC (list_max (MAP (to_num:'a->num)
			     (dom_list (f:(('a#'b)list)finmap))))`--,
	   --`from_num:num->'a`--] f_one_one_member
      val tmp_thm4 = PURE_REWRITE_RULE [MP tmp_thm3 tmp_thm2] tmp_thm
      val tmp_thm5 = ISPECL
	  [--`dom_list (f:(('a#'b)list)finmap)`--,
	   --`to_num:'a -> num`--, --`from_num:num->'a`--] map_comp
      val tmp_thm6 = PURE_REWRITE_RULE [tmp_thm5] tmp_thm4
      val tmp_thm7 = MP (ISPECL [--`dom_list (f:(('a#'b)list)finmap)`--,
				 --`from_num:num->'a`--, --`to_num:'a->num`--]
			 bij_imp_map_id) bij_thm1
      val tmp_thm8 = PURE_REWRITE_RULE [tmp_thm7] tmp_thm6
in
    val exists_not_member_dom = TAC_PROOF
	(([],
	  --`!(f:(('a#'b)list) finmap). 
	  (?from_num (to_num:'a -> num). bij_inv from_num to_num) ==>
	      (?(x:'a). ~(list_member x (dom_list f)))`--),
	 GEN_TAC THEN STRIP_TAC THEN EXISTS_TAC tm1 THEN ACCEPT_TAC tmp_thm8)
end

val in_dom_DEF = new_definition
("in_dom_DEF",
 --`in_dom (f:(('a#'b)list) finmap) x = list_member x (dom_list f)`--)

(* exists_not_in_dom:
  |- !f. (?from_num to_num. bij_inv from_num to_num) ==> (?x. ~(in_dom f x)) *)
val exists_not_in_dom = TAC_PROOF
    (([], --`!(f:(('a#'b)list)finmap). 
                  (?(from_num:num->'a) to_num. bij_inv from_num to_num) ==>
		  (?x. ~(in_dom f x))`--),
     PURE_REWRITE_TAC [in_dom_DEF] THEN ACCEPT_TAC exists_not_member_dom)

val WOP = theorem "arithmetic" "WOP";

val bij_thm = ASSUME bij_term
val bij2 = PURE_REWRITE_RULE [bij_inv_DEF] bij_thm
val from_to = CONJUNCT2 (CONJUNCT2 (CONJUNCT2 bij2))
val to_from = CONJUNCT1 (CONJUNCT2 (CONJUNCT2 bij2));

(* from_thm:
   |- !f from_num to_num.
       bij_inv from_num to_num ==>
       ((?n. ~(in_dom f (from_num n))) = (?a. ~(in_dom f a))) *)
val from_thm = TAC_PROOF
    (([], 
      --`!(f:(('a#'b)list) finmap) (from_num:num->'a) to_num.
      (bij_inv from_num to_num) ==>
	  ((?(n:num). ~(in_dom f (from_num n))) =
	   (?(a:'a). ~(in_dom f a)))`--),
     REPEAT STRIP_TAC THEN EQ_TAC THENL
     [STRIP_TAC THEN EXISTS_TAC (--`(from_num:num->'a) n`--) THEN
      FIRST_ASSUM ACCEPT_TAC,
      STRIP_TAC THEN EXISTS_TAC (--`(to_num:'a->num) a`--) THEN
      ASM_REWRITE_TAC [from_to]]);

(* almost_there: 
   |- !f from_num to_num.
       bij_inv from_num to_num ==>
       (?n. ~(in_dom f (from_num n)) /\ (!m. m < n ==> in_dom f (from_num m)))
*)
local
    val foo1 = SPEC 
	(--`\(n:num). ~(in_dom (f:(('a#'b)list) finmap) (from_num n))`--) WOP
    val foo2 = REWRITE_RULE [] (BETA_RULE foo1)
    val foo4 = EXISTS (--`?(to_num:'a->num). bij_inv from_num to_num`--,
		       --`to_num:'a->num`--) bij_thm
    val foo5 = EXISTS
	(--`?from_num (to_num:'a->num). bij_inv from_num to_num`--,
	 --`from_num:num->'a`--) foo4
    val foo6 = MP (SPEC_ALL exists_not_in_dom) foo5
    val foo7 = REWRITE_RULE [SYM (UNDISCH (SPEC_ALL from_thm))] foo6
in
    val almost_there = TAC_PROOF 
	(([], 
	  --`!f (from_num:num->'a) to_num. (bij_inv from_num to_num) ==>
	      (?n. ~(in_dom (f:(('a#'b)list) finmap) (from_num n)) /\
	       !m. m < n ==> (in_dom f (from_num m)))`--),
	 REPEAT STRIP_TAC THEN MP_IMP_TAC foo2 THEN ACCEPT_TAC foo7)
end;

(* select2:   |- !P. (?x. P x) ==> P ($@ P) *)
local
    val temp = SPEC (--`P:'a -> bool`--) SELECT_AX;
    val temp2 = PURE_REWRITE_RULE [FORALL_IMP_CONV (concl temp)] temp
in
    val select2 = GEN_ALL temp2
end;

(* exists_next_thm:
  |- !f from_num to_num less.
      bij_inv from_num to_num /\ (!a a'. less a a' = to_num a < to_num a') ==>
      (?a. ~(in_dom f a) /\ (!a'. less a' a ==> in_dom f a'))  *)
local
    val foo1 = UNDISCH (SPEC_ALL almost_there)
    val tm = --`\n. ~(in_dom (f:(('a#'b)list) finmap) (from_num n)) /\ 
	(!m. m < n ==> in_dom f (from_num m))`--
    val tm2 = --`(from_num:num->'a) ($@^tm)`--
    val foo3 = BETA_RULE (ISPECL [tm] select2)
    val foo4 = MP foo3 foo1
    val foo5 = SPEC (--`(to_num:'a->num) a'`--) (CONJUNCT2 foo4)
    val foo6 = PURE_REWRITE_RULE [from_to] foo5
in
    val exists_next_thm = TAC_PROOF
	(([], 
	  --`!(f:(('a#'b)list) finmap) (from_num:num->'a) to_num less.
	  ((bij_inv from_num to_num) /\ 
	   (!(a:'a) a'. less a a' = (to_num a < to_num a'))) ==>
	      (?a. ~(in_dom f a) /\
	       (!a'. less a' a ==> (in_dom f a')))`--),
	 REPEAT STRIP_TAC THEN EXISTS_TAC tm2 THEN CONJ_TAC THENL
	 [ACCEPT_TAC (CONJUNCT1 foo4),
	  GEN_TAC THEN REWRITE_TAC 
	  [ASSUME (--`!a a'. less a a' = (to_num:'a->num) a < to_num a'`--),
	   to_from] THEN ACCEPT_TAC foo6])
end;

val next_dom_DEF = new_definition
("next_dom_DEF",
 --`next_dom less (f:(('a#'b)list) finmap) = @a. ~(in_dom f a) /\
        (!a'. less a' a ==> (in_dom f a'))`--);

(* next_dom_thm: 
 |- !f from_num to_num less.
       bij_inv from_num to_num /\ (!a a'. less a a' = to_num a < to_num a') ==>
       ~(in_dom f (next_dom less f)) /\
	   (!a'. less a' (next_dom less f) ==> in_dom f a') *)
local
    val P_term = --`\a. ~(in_dom (f:(('a#'b)list) finmap) a) /\
	(!a'. less a' a ==> (in_dom f a'))`--
    val foo1 = BETA_RULE (SPEC P_term select2)
    val foo2 = UNDISCH_ALL (hd (IMP_CANON (SPEC_ALL exists_next_thm)))
    val foo3 = MP foo1 foo2
in
    val next_dom_thm = save_thm
	("next_dom_thm",
	 TAC_PROOF
	 (([], --`!(f:(('a#'b)list) finmap) (from_num:num->'a) to_num less.
	   ((bij_inv from_num to_num) /\ 
	    (!(a:'a) a'. less a a' = (to_num a < to_num a'))) ==>
	   (~(in_dom f (next_dom less f)) /\
	    (!a'. less a' (next_dom less f) ==> (in_dom f a')))`--),
	 REPEAT GEN_TAC THEN STRIP_TAC THEN PURE_REWRITE_TAC [next_dom_DEF]
	 THEN ACCEPT_TAC foo3))
end;


(* going to need a lemma that says: 
   !l l' f. ONE_ONE f ==> (nonempty_MAP f l = nonempty_MAP f l' = l = l')
   in order to show that 
   nonempty_MAP lift E_1_n = nonempty_MAP lift E_1_n'
   implies E_1_n = E_1_n' *)

(* The way I will try to prove this is to induct on the length of the non-
   empty list. So first I'll define the length of a NElist, where the length
   of (ONE x) = 0, in order to provide a base case for induction. *)

val ne_length_DEF =
    new_recursive_definition
    {name = "ne_length_DEF",
     fixity = Prefix,
     rec_axiom = nonemptylist_Axiom,
     def = --`(ne_length (ONE (x:'a)) = 0) /\
              (ne_length (MORE x n) = (ne_length n) + 1)`--}

local
    val prop = --`\(n:'a nonemptylist). 
	ne_length (nonempty_MAP (f:'a->'b) n) = ne_length n`--
    val tmp_induction = BETA_RULE (SPEC prop nonemptylist_induction_thm)
    val spec_induction = DISCH_ALL (SPEC_ALL (UNDISCH tmp_induction))
in
    val length_preserved = store_thm("length_preserved",
	(--`!(n:'a nonemptylist) (f:'a -> 'b).
	  ne_length (nonempty_MAP f n) = ne_length n`--),
	 GEN_TAC THEN GEN_TAC THEN MP_IMP_TAC spec_induction THEN CONJ_TAC THEN
	 GEN_TAC THEN REWRITE_TAC [nonempty_MAP_DEF, ne_length_DEF] THEN
	 DISCH_TAC THEN REWRITE_TAC [theorem "arithmetic" "EQ_MONO_ADD_EQ"]
	 THEN FIRST_ASSUM ACCEPT_TAC)
end;

val length_0_thm = store_thm ("length_0_thm",
    (--`!(l:'a nonemptylist). (ne_length l = 0) = (?x. l = (ONE x))`--),
     GEN_TAC THEN EQ_TAC THENL
     [STRIP_ASSUME_TAC (SPEC (--`l:'a nonemptylist`--) 
			nonemptylist_cases_thm) THENL
      [DISCH_TAC THEN EXISTS_TAC (--`x:'a`--) THEN FIRST_ASSUM ACCEPT_TAC,
       ASM_REWRITE_TAC [ne_length_DEF, theorem "arithmetic" "ADD_EQ_0"] THEN
       STRIP_TAC THEN 
       CONTR_TAC (CONV_RULE Num_lib.num_EQ_CONV (ASSUME (--`1 = 0`--)))],
      STRIP_TAC THEN ASM_REWRITE_TAC [ne_length_DEF]])

local
    val tmp1 = SYM (SPEC (--`ne_length (n':'a nonemptylist)`--) 
		    (theorem "arithmetic" "ADD1"))
in
    val length_suc_thm = store_thm("length_suc_thm",
	(--`!(l:'a nonemptylist). (ne_length l = SUC n) =
	  (?x l2. (l = (MORE x l2)) /\ (ne_length l2 = n))`--),
	 GEN_TAC THEN EQ_TAC THENL
	 [STRIP_ASSUME_TAC (SPEC (--`l:'a nonemptylist`--) 
			    nonemptylist_cases_thm) THENL
	  [ASM_REWRITE_TAC [ne_length_DEF, theorem "arithmetic" "SUC_NOT"],
	   ASM_REWRITE_TAC [ne_length_DEF, theorem "arithmetic" "ADD1",
			    theorem "arithmetic" "EQ_MONO_ADD_EQ"] THEN
	   DISCH_TAC THEN EXISTS_TAC (--`x:'a`--) THEN 
	   EXISTS_TAC (--`n':'a nonemptylist`--) THEN ASM_REWRITE_TAC []],
	  STRIP_TAC THEN 
	  ASM_REWRITE_TAC [ne_length_DEF, theorem "arithmetic" "ADD1"]])
end

local
    val one_one_thm = REWRITE_RULE [ONE_ONE_DEF] 
	(ASSUME (--`ONE_ONE (f:'a->'b)`--))
    val one_one_thm2 = IMP_ANTISYM_RULE 
	(SPECL [--`x:'a`--, --`x':'a`--] one_one_thm)
	(DISCH (--`(x:'a) = x'`--)
	 (AP_TERM (--`f:'a->'b`--) (ASSUME (--`(x:'a) = x'`--))))
    fun finish_tac (asms, gl) =
	let val forall_asm = Lib.first is_forall asms
	    val thm1 = SPECL [--`l2:'a nonemptylist`--,
			      --`l2':'a nonemptylist`--] (ASSUME forall_asm)
	    val thm2 = CONJ (ASSUME (--`ne_length (l2:'a nonemptylist) = n`--))
		(ASSUME (--`ne_length (l2':'a nonemptylist) = n`--))
	    val thm3 = MP thm1 thm2
	    val thm4 = MP thm3 (ASSUME (#ant (dest_imp (concl (thm3)))))
	in
	    ASM_REWRITE_TAC [thm4] (asms, gl)
	end
in
    val almost_thm = TAC_PROOF
	(([], --`ONE_ONE f ==> !n l l'. 
	    ((ne_length (l:'a nonemptylist) = n) /\
	     (ne_length (l':'a nonemptylist) = n)) ==>
	    ((nonempty_MAP f l = nonempty_MAP (f:'a->'b) l') ==> (l = l'))`--),
	    DISCH_TAC THEN INDUCT_TAC THENL
	    [REWRITE_TAC [length_0_thm] THEN GEN_TAC THEN GEN_TAC THEN
	     STRIP_TAC THEN ASM_REWRITE_TAC
	     [nonempty_MAP_DEF, nonemptylist_constructors_one_one,
	      one_one_thm],
	     REWRITE_TAC [length_suc_thm] THEN GEN_TAC THEN GEN_TAC THEN
	     STRIP_TAC THEN ASM_REWRITE_TAC
	     [nonempty_MAP_DEF, nonemptylist_constructors_one_one,
	      one_one_thm2] THEN
	     STRIP_TAC THEN finish_tac])
end

local
    fun length_tac (asms, gl) = 
	let val thm1 = ASSUME (hd asms)
	    val thm2 = AP_TERM (--`ne_length:'b nonemptylist->num`--) thm1
	    val thm3 = SYM (REWRITE_RULE [length_preserved] thm2)
	in
	    REWRITE_TAC [thm3] (asms, gl)
	end
in
    val exists_n_thm = TAC_PROOF
	(([], --`(nonempty_MAP (f:'a->'b) l = nonempty_MAP f l') ==>
	  ?n. (ne_length l = n) /\ (ne_length l' = n)`--),
	 DISCH_TAC THEN EXISTS_TAC (--`ne_length (l:'a nonemptylist)`--) THEN
	 length_tac)
end

local
    fun transform_tac (asms, gl) =
	let val thm1 = ASSUME (hd asms)
	    val thm2 = MP exists_n_thm thm1
	in
	    STRIP_ASSUME_TAC thm2 (asms, gl)
	end
    fun finish2_tac (asms, gl) =
	let val thm1 = MP almost_thm (ASSUME (--`ONE_ONE (f:'a->'b)`--))
	    val thm2 = MP (SPEC_ALL thm1)
		(CONJ (ASSUME (--`ne_length (l:'a nonemptylist) = n`--))
		 (ASSUME (--`ne_length (l':'a nonemptylist) = n`--)))
	    val thm3 = MP thm2 
		(ASSUME (--`nonempty_MAP (f:'a->'b) l = nonempty_MAP f l'`--))
	in
	    ACCEPT_TAC thm3 (asms, gl)
	end
in
    val nonempty_MAP_thm = store_thm ("nonempty_MAP_thm",
	(--`!l l' f. ONE_ONE f ==> 
	    ((nonempty_MAP f l = nonempty_MAP (f:'a->'b) l') = (l = l'))`--),
	 REPEAT GEN_TAC THEN DISCH_TAC THEN EQ_TAC THEN DISCH_TAC THENL
	 [transform_tac THEN finish2_tac,
	  ACCEPT_TAC (AP_TERM (--`nonempty_MAP (f:'a->'b)`--) 
		      (ASSUME (--`(l:'a nonemptylist) = l'`--)))])
end



val _ = export_theory ();
