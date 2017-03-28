new_theory"exorgroup";
load_library{lib = abs_theory_lib, theory = "-"};

open Abs_theory;
open Psyntax;
    
new_parent"groups";

add_obligs "groups";

abs_add_theory_to_sml "groups";

val exclusive_or = new_infix_definition
("exclusive_or",
  --`! (x:bool) y. $>< x y = ~(x=y)`--, 20);

val exorgroup =
  prove((--`group_oblig(group I F ($><))`--),
        EXPAND_THOBS_TAC
        THEN REWRITE_TAC[exclusive_or,theorem"combin""I_THM"]
        THEN (REPEAT GEN_TAC
              THEN MAP_EVERY BOOL_CASES_TAC [--`x:bool`--,
                                             --`y:bool`--,
                                             --`z:bool`--]
              THEN REWRITE_TAC[]));

val EXOR_IDENTITY_UNIQUE =
    instantiate_abs_thm [{abs_term=(--`g:('a)group`--),
                          rep_term=(--`group I F ($><)`--),
                          validation=exorgroup}]
                        IDENTITY_UNIQUE;

val EXOR_GROUP_ID =       
    instantiate_abs_thm [{abs_term=(--`g2:('a)group`--),
                          rep_term=(--`group I F ($><)`--),
                          validation=exorgroup}]
                        OP_DETERMINES_IDENTITY;

val EXOR_LEFT_CANCELLATION =
    instantiate_abs_thm [{abs_term=(--`g:('a)group`--),
                          rep_term=(--`group I F ($><)`--),
                          validation=exorgroup}]
                        LEFT_CANCELLATION;
    
val EXOR_INVERSE_INVERSE_LEMMA =
    instantiate_abs_thm [{abs_term=(--`g:('a)group`--),
                          rep_term=(--`group I F ($><)`--),
                          validation=exorgroup}]
                        INVERSE_INVERSE_LEMMA;
    
