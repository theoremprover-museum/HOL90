load_library{lib = abs_theory_lib, theory = "monoid"};
open Abs_theory;
open Psyntax;

val monoid_th = new_abstract_entity
    {Name = "monoid",
     Predicate = (--`(! x. op x (e:'a) = x) /\
		     (! x. op e x = x) /\
		     (! x y z. (op x (op y z)) = (op (op x y) z))`--)};
    
val SYM_RULE = CONV_RULE(ONCE_DEPTH_CONV SYM_CONV);

fun define_theorem name th = (save_thm (name,th); add_to_sml[(name,th)]);
    
define_theorem "IDENTITY_UNIQUE"
  (abs_prove(
   --`!(m:'a monoid) f.
           (!a. (op m a f = a) /\ (op m f a = a))
            ==> (f = (e m))`--,
  STRIP_THOBS_TAC
   THEN REPEAT GEN_TAC
   THEN STRIP_GOAL_THEN 
         (fn thm => SUBST1_TAC (SYM_RULE 
                      (CONJUNCT1 (SPEC (--`e (m:('a)monoid)`--) thm))))
   THEN ASM_REWRITE_TAC []));

    
define_theorem "OP_DETERMINES_IDENTITY"
    (abs_prove
     ( --`! m1 (m2:('a)monoid) . (op m1 = (op m2)) ==> (e m1 = (e m2))`--,
      STRIP_THOBS_TAC
      THEN STRIP_TAC
      THEN let val t1 = ASSUME (--`!x:'a. op m1 (e m1) x = x`--)
	   in SUBST_TAC (map SYM_RULE [SPEC (--`e m2:'a`--) t1])
	   end
      THEN let val t2 = ASSUME (--`!x:'a. op m2 x (e m2) = x`--)
	   in SUBST_TAC (map SYM_RULE [SPEC(--`e m1:'a`--) t2])
	   end
      THEN ASM_REWRITE_TAC [])
     );
	
val _ = new_definition("monoid_sq",
        --`monoid_sq (m:('a)monoid) a = (op m a a)`--)

val _ = export_theory();

    
