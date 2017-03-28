new_theory "groups";
load_library{lib = abs_theory_lib, theory = "-"};
open Abs_theory;
open Psyntax;

fun define_theorem name th = (save_thm (name,th); add_to_sml[(name,th)]);

val SYM_RULE = CONV_RULE(ONCE_DEPTH_CONV SYM_CONV);

new_parent "monoid";

add_obligs "monoid";

abs_add_theory_to_sml "monoid";

new_abstract_entity 
 {Name="group",
  Predicate=(--`(!x .fn x (id:'a) = x) /\
	        (!x .fn id x = x) /\
	        (!x .fn x (inv x) = id ) /\
	        (!x. fn (inv x) x = id) /\
	        (!x y z. (fn x (fn y z)) = (fn (fn x y) z))`--)
 };

val GROUP_EXTENDS_MONOID = abs_prove(
--`!g:'a group. monoid_oblig(monoid (id g) (fn g))`--,
      STRIP_THOBS_TAC
      THEN EXPAND_THOBS_TAC
      THEN ASM_REWRITE_TAC []
      );

define_theorem "IDENTITY_UNIQUE"
   (instantiate_abs_thm[{abs_term=(--`m:('a)monoid`--),
			 rep_term=(--`monoid (id(g:('a)group))(fn g)`--),
			 validation=GROUP_EXTENDS_MONOID}]
                       IDENTITY_UNIQUE);

define_theorem "OP_DETERMINES_IDENTITY"
   (instantiate_abs_thm[{abs_term=(--`m1:('a)monoid`--),
			 rep_term=(--`monoid (id(g1:('a)group))(fn g1)`--),
			 validation=GROUP_EXTENDS_MONOID},
			{abs_term=(--`m2:('a)monoid`--),
			 rep_term=(--`monoid (id(g2:('a)group))(fn g2)`--),
			 validation=GROUP_EXTENDS_MONOID}]
                       OP_DETERMINES_IDENTITY);

val group_sq =
    new_definition("group_sq",
		   (--`group_sq (g:('a)group) a 
		       = (monoid_sq (monoid(id g)(fn g)) a)`--));

val group_sq_thm 
    = instantiate_abstract_definition 
        [{abs_term=(--`m:'a monoid`--),
          rep_term=(--`monoid(id (g:'a group))(fn g)`--)}]
        monoid_sq group_sq;

define_theorem "LEFT_CANCELLATION" (abs_prove
 (--`! (g:('a)group) x y a. ((fn g) a x = ((fn g) a y)) ==> (x = y)`--,
	      STRIP_THOBS_TAC
	      THEN REPEAT STRIP_TAC
	      THEN ACCEPT_TAC 
	      let val t1 = ASSUME(--`!x y z. fn (g:('a)group) x(fn g y z)
				     = fn g(fn g x y)z`--)
		  and t2 = ASSUME (--`!x. fn (g:('a)group)(inv g x)x = id g`--)
		  and t3 = ASSUME (--`!x. fn (g:('a)group)(id g) x  = x`--)
		  and t4 = ASSUME (--`fn (g:('a)group) a x = fn g a y`--)
	      in
	      SYM_RULE (REWRITE_RULE [t1,t2,t3] 
			(REWRITE_RULE [t2,t3,t4] 
			 (ISPECL [(--`(inv g (a:'a))`--),
                                  (--`a:'a`--),(--`x:'a`--)] t1)))
	      end));

define_theorem "INVERSE_INVERSE_LEMMA" 
(abs_prove(
  --`!g:'a group. !a. inv g (inv g a) = a`--,
  STRIP_THOBS_TAC
  THEN GEN_TAC
  THEN ACCEPT_TAC 
	let val t1 = ASSUME(--`!x. fn (g:'a group) x(inv g x) = id g`--)
	    and t2 = ASSUME(--`!x. fn (g:'a group) (inv g x)x = id g`--)
            and LC_LEMMA = (ISPECL [--`inv (g:'a group) (inv g a)`--,
                                    --`a:'a`--,--`inv g (a:'a)`--]
			    o UNDISCH 
                            o ISPEC(--`g:('a)group`--)) LEFT_CANCELLATION 
	in
	MATCH_MP LC_LEMMA (TRANS (ISPEC(--`(inv g)(a:'a)`--)t1) 
				 (SYM_RULE (ISPEC (--`a:'a`--)t2)))
	end));


    
val inv_3_is_inv = 
  abs_prove(--`!(g:num group) a. inv g(inv g(inv g a)) = inv g a`--,
	STRIP_THOBS_TAC
	THEN Imp_rewrite.IMP_REWRITE_TAC[INVERSE_INVERSE_LEMMA]);

val _ = export_theory();
    
