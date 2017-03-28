(*===========================================================================*)
(*                                                                           *)
(*   FILE:         mk_min_max.sml                                            *)
(*   EDITOR:       Paul Curzon                                               *)
(*   DATE:         June 1991                                                 *)
(*   DESCRIPTION:  Maximum and Minimum                                       *)
(*                                                                           *)
(*===========================================================================*)


(*=================================  HISTORY  ===============================*)
(*									     *)
(*   This file is part of the more_arithmetic theory in the bags library by  *)
(*     Philippe Leveilley						     *)
(*   Conversion to HOL12 and editing was done by 			     *)
(*     Wim Ploegaerts						             *)
(*									     *)
(*   HOL90 Version April 1993 by PC                                          *)
(*                                                                           *)
(*===========================================================================*)

(*
val path = 
   (!Globals.HOLdir)^"library/more_arithmetic/theories/"^Globals.theory_file_type^"/"
*)

val path = 
   "../"^Globals.theory_file_type^"/"

val _ = theory_path := path::(!theory_path);


local
fun delete_theory name = 
    System.system("/bin/rm -f "^name^".thms "^name^".holsig")
in
  val _ = delete_theory (path^"min_max")
end;


new_theory "min_max";

val ZERO_LESS_EQ = theorem "arithmetic" "ZERO_LESS_EQ";
val NOT_LESS = theorem "arithmetic" "NOT_LESS";
val LESS_OR_EQ = definition "arithmetic" "LESS_OR_EQ";
val LESS_EQ_SUC_REFL = theorem "arithmetic" "LESS_EQ_SUC_REFL";
val LESS_EQ_MONO = theorem "arithmetic" "LESS_EQ_MONO";

(*===========================================================================*)
(*									     *)
(* 			      MIN AND MAX by PL				     *)
(*									     *)
(*===========================================================================*)



val MAX_DEF = new_definition
    ("MAX_DEF",
     (--`MAX n p = ((n <= p) => p | n)`--)
);

val MAX_0 = store_thm
    ("MAX_0",
     (--`!n. MAX 0 n = n`--),
     REWRITE_TAC [MAX_DEF, ZERO_LESS_EQ]
);
 

val MAX_SYM = store_thm
    ("MAX_SYM",
     (--`!n p. MAX n p = MAX p n`--),
     REPEAT GEN_TAC THEN
     ASM_CASES_TAC (--`n:num=p`--) THENL
     [ (* n = p *)
         ASM_REWRITE_TAC []
     , (* ~ n = p *)
         REWRITE_TAC [MAX_DEF] THEN
         ASM_CASES_TAC (--`n <= p`--) THEN
         ASM_REWRITE_TAC [LESS_OR_EQ] THEN
         POP_ASSUM_LIST (fn [T1,T2] =>
            REWRITE_TAC [GSYM T2, REWRITE_RULE [GSYM NOT_LESS] T1])
     ]
);

val MAX_REFL = store_thm
    ("MAX_REFL",
     (--`!n. MAX n n = n`--),
     REWRITE_TAC [MAX_DEF, LESS_OR_EQ]
);

val MAX_SUC = store_thm
    ("MAX_SUC",
     (--`!n. MAX n (SUC n) = SUC n`--),
     REWRITE_TAC [MAX_DEF, LESS_EQ_SUC_REFL]
);

val SUC_MAX = store_thm
    ("SUC_MAX",
     (--`!n p. MAX (SUC n) (SUC p) = SUC (MAX n p)`--),
     REPEAT GEN_TAC THEN
     REWRITE_TAC [MAX_DEF, LESS_EQ_MONO] THEN
     COND_CASES_TAC THEN
     ASM_REWRITE_TAC[]
);

val MIN_DEF = new_definition
    ("MIN_DEF",
     (--`MIN n p = ((n <= p) => n | p)`--)
);

val MIN_0 = store_thm
    ("MIN_0",
     (--`!n. MIN 0 n = 0`--),
     REWRITE_TAC [MIN_DEF, ZERO_LESS_EQ]
);

val MIN_SYM = store_thm
    ("MIN_SYM",
     (--`!n p. MIN n p = MIN p n`--),
     REPEAT GEN_TAC THEN
     ASM_CASES_TAC (--`n:num=p`--) THENL
     [ (* n = p *)
         ASM_REWRITE_TAC []
     , (* ~ n = p *)
         REWRITE_TAC [MIN_DEF] THEN
         ASM_CASES_TAC (--`n <= p`--) THEN
         ASM_REWRITE_TAC [LESS_OR_EQ] THEN
         POP_ASSUM_LIST (fn [T1,T2] =>
            REWRITE_TAC [GSYM T2, REWRITE_RULE [GSYM NOT_LESS] T1])
     ]
);

val MIN_REFL = store_thm
    ("MIN_REFL",
     (--`!n. MIN n n = n`--),
     REWRITE_TAC [MIN_DEF, LESS_OR_EQ]
);

val MIN_SUC = store_thm
    ("MIN_SUC",
     (--`!n. MIN n (SUC n) = n`--),
     REWRITE_TAC [MIN_DEF, LESS_EQ_SUC_REFL]
);


val SUC_MIN = store_thm
    ("SUC_MIN",
     (--`!n p. MIN (SUC n) (SUC p) = SUC (MIN n p)`--),
     REPEAT GEN_TAC THEN
     REWRITE_TAC [MIN_DEF, LESS_EQ_MONO] THEN
     COND_CASES_TAC THEN
     ASM_REWRITE_TAC[]
);


export_theory();
close_theory();
