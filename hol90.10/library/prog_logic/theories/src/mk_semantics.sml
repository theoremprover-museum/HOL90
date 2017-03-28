(* ************************************************************************* *)
(*                                                                           *)
(* FILE          : mk_semantics.sml                                          *)
(* DESCRIPTION   : Defines the semantics of a simple while language in HOL   *)
(*                                                                           *)
(* AUTHOR        : Mike Gordon, University of Cambridge                      *)
(* DATE          : March 1988                                                *)
(*                                                                           *)
(* TRANSLATOR    : Matthew Morley, University of Edinburgh                   *)
(* DATE          : Feb 1993                                                  *)
(*                                                                           *)
(* ************************************************************************* *)

new_theory "semantics";

load_library{lib=string_lib, theory = "semantics"};

val num_Axiom  = theorem "prim_rec" "num_Axiom";
val list_Axiom = theorem "list" "list_Axiom";
val NULL       = theorem "list" "NULL";
val CONS       = theorem "list" "CONS";
val HD         = definition "list" "HD";
val TL         = definition "list" "TL";
val UNCURRY_DEF = definition "pair" "UNCURRY_DEF";


(*
    new_type_abbrev("state", ":string -> num");
    new_type_abbrev("command", ":state * state -> bool");
*)

val state = ty_antiq(==`:string -> num`==)
val command = ty_antiq(==`:^state#^state -> bool`==);

val MK_SKIP = new_definition
    ("MK_SKIP",
     (--`MK_SKIP (s:^state,s') = (s = s')`--));

val MK_ABORT = new_definition
    ("MK_ABORT",
     (--`MK_ABORT (s:^state, (s':^state)) = F`--));

val MK_IF1 = new_definition
    ("MK_IF1",
     (--`MK_IF1(p,c) (s:^state,s') = (p s => c(s,s') | (s = s'))`--));

val MK_IF2 = new_definition
    ("MK_IF2",
     (--`MK_IF2(p,c,c') (s:^state,(s':^state)) :bool 
      = (p s => c(s,s') | c'(s,s'))`--));

val MK_SEQ = new_definition
    ("MK_SEQ",
     (--`MK_SEQ(c,c') (s:^state,(s':^state)) 
      = ?s'':^state. c(s,s'') /\ c'(s'',s')`--));

val MK_SEQL = new_recursive_definition
      {name="MK_SEQL",
       def = --`(MK_SEQL NIL          =  \(s,s').(s=s')) /\
                (MK_SEQL (CONS c cl)  =  MK_SEQ(c, MK_SEQL cl))`--,
       rec_axiom = list_Axiom,
       fixity = Prefix};

val MK_FINITE_WHILE = new_recursive_definition{
    def=(--`(MK_FINITE_WHILE 0 = \(p,c) (s,s'). F) /\
            (MK_FINITE_WHILE (SUC n) = \(p,c). 
               MK_IF1(p, MK_SEQ(c, MK_FINITE_WHILE n (p,c))))`--),
    fixity=Prefix,
    name="MK_FINITE_WHILE",
    rec_axiom=num_Axiom};

val MK_WHILE = new_definition
    ("MK_WHILE",
     (--`MK_WHILE (p,c) (s,s') = ?n. MK_FINITE_WHILE n (p,c) (s,s')`--));
 
(* 
   {p} c {q} is represented by MK_SPEC(p,c,q)
*)

val MK_SPEC = new_definition
 ("MK_SPEC",
  (--`MK_SPEC(p,c,q) = !(s:^state) (s':^state). 
                         p s /\ c(s,s') ==> q s'`--));

val MK_ASSERT = new_definition
    ("MK_ASSERT",
     (--`MK_ASSERT (p:^state->bool) (s,s') = p s /\ (s = s')`--));
 
val MK_INVARIANT = new_definition
    ("MK_INVARIANT",
     (--`MK_INVARIANT (p:^state->bool) (s,s') = p s /\ (s = s')`--));
 
val MK_VARIANT = new_definition
  ("MK_VARIANT",
   (--`MK_VARIANT(p:^state->num) (s,s') = (p s > p s') /\ (s = s')`--));

(* ========================================================================= *)
(*  BND : string -> num -> (string -> num) -> (string -> num)                *)
(* ========================================================================= *)

val BND = new_definition
    ("BND",
     (--`BND x n (s:^state)  =  \z. ((z=x) => n | s z)`--));

val MK_ASSIGN = new_definition
    ("MK_ASSIGN",
     (--`MK_ASSIGN (x,e) (s:^state,s') = (s' = BND x (e s) s)`--));

val BND_THM1 = save_thm("BND_THM1",
 prove
  ((--`!n x s. BND x n s x = n`--),
   REWRITE_TAC[BND]
    THEN BETA_TAC
    THEN REWRITE_TAC[]));

val BND_THM2 = save_thm("BND_THM2",
 prove
  ((--`!n x s y. ~(y = x) ==> (BND x n s y = (s y))`--),
   REWRITE_TAC[BND]
    THEN BETA_TAC
    THEN REPEAT STRIP_TAC
    THEN ASM_REWRITE_TAC[]));

val MK_FINITE_WHILE_CLAUSES = save_thm("MK_FINITE_WHILE_CLAUSES",
 prove
  ((--`(MK_FINITE_WHILE 0       (p,c) (s,s')  =  F) /\
       (MK_FINITE_WHILE (SUC n) (p,c) (s,s')  =  
          MK_IF1(p, MK_SEQ(c, MK_FINITE_WHILE n (p,c))) (s,s'))`--),
   PURE_REWRITE_TAC[MK_FINITE_WHILE]
    THEN BETA_TAC
    THEN PURE_REWRITE_TAC[UNCURRY_DEF]
    THEN BETA_TAC
    THEN PURE_REWRITE_TAC[UNCURRY_DEF]
    THEN BETA_TAC
    THEN REWRITE_TAC[]));

close_theory();

export_theory();
