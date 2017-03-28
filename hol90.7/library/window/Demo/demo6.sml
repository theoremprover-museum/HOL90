(* (|- !t x. (t => x | x) = x)                                               *)
val COND_EQ =
    prove ((--`!t (x:'a). (t => x | x) = x`--),
	(REPEAT GEN_TAC) THEN
	(BOOL_CASES_TAC (--`t:bool`--)) THEN
	(REWRITE_TAC []));

(* (|- (P => T | F) = P)                                                     *)
val COND_T_F =
    GEN_ALL (prove ((--`(P => T | F) = P`--),
            (BOOL_CASES_TAC (--`P:bool`--)) THEN
            (REWRITE_TAC [])));

(* (|- (P => F | T) = ~P)                                                    *)
val COND_F_T =
    GEN_ALL (prove ((--`(P => F | T) = ~P`--),
            (BOOL_CASES_TAC (--`P:bool`--)) THEN
            (REWRITE_TAC [])));

(* (|- (f (a => b | c)) = (a => (f b) | (f c)))                              *)
val COND_AP =
    GEN_ALL
      (prove ((--`((f:'a->'b) (a => (b:'a) | c)) = (a => (f b) | (f c))`--),
		(BOOL_CASES_TAC (--`a:bool`--)) THEN
		(REWRITE_TAC [])));

(* EQ_EXT_EQ (|- !f g. (!x. f x = g x) = (f = g))                            *)

val EQ_EXT_EQ =
    let val th1 = SPEC_ALL EQ_EXT
        val th2 = DISCH_ALL (GEN (--`x:'a`--)
		      (AP_THM (ASSUME (--`(f:'a -> 'b) = g`--)) (--`x:'a`--)))
	in
		GEN_ALL (IMP_ANTISYM_RULE th1 th2)
	end;

val NOT_CLAUSE1 = GEN_ALL (hd (CONJUNCTS (SPEC_ALL NOT_CLAUSES)))
and AND_CLAUSE1 = GEN_ALL (hd (CONJUNCTS (SPEC_ALL AND_CLAUSES)))
and EQ_CLAUSE1 = GEN_ALL (hd (CONJUNCTS (SPEC_ALL EQ_CLAUSES)));

new_theory "PARITY";

val PARITY_DEF =
    new_recursive_definition
        {name = "PARITY_DEF",
	 fixity = Prefix,
	 rec_axiom = theorem "prim_rec" "num_Axiom",
	 def = (--`(PARITY inp 0 = T) /\
		   (PARITY inp (SUC n) =
                       (inp (SUC n) => ~(PARITY inp n) | (PARITY inp n)))`--)
        };

val MUX_DEF = new_definition
    (
        "MUX_DEF",
        (--`MUX a (b:num->bool) c t = ((a t) => (b t) | (c t))`--)
    );

val REG_DEF = new_definition ("REG_DEF",
    (--`REG inp t = ((t=0) => F | (inp (t - 1)))`--));

val ONE_DEF = new_definition ("ONE_DEF", (--`ONE (t : num) = T`--));

val NOT_DEF = new_definition ("NOT_DEF", (--`NOT inp (t : num) = ~(inp t)`--));

BEGIN_STACK "demo6" (--`($<==) (!t.out t = PARITY inp t)`--) [] [];

DO (OPEN_WIN [RAND,BODY,RAND]);
   DO (ONCE_REWRITE_WIN
	[SYM (SPEC_ALL (ISPECL [(--`t = 0`--),
				(--`PARITY inp t`--)] COND_EQ))]);
   DO (OPEN_WIN [RATOR,RAND]);
       DO (REWRITE_WIN [ASSUME (--`t = 0`--), PARITY_DEF]);
       DO (TRANSFORM_WIN (SYM (SPEC (--`t:num`--) ONE_DEF)));
       DO CLOSE_WIN;
   DO (OPEN_WIN [RAND]);
      DO (PURE_ONCE_REWRITE_WIN [GEN_ALL (SYM (SPEC_ALL AND_CLAUSE1))]);
      DO (ADD_THEOREM (REWRITE_RULE [ASSUME (--`~(t = 0)`--)]
                          (SPEC (--`t:num`--)
                                (theorem "arithmetic" "num_CASES"))));
      DO (PURE_ONCE_REWRITE_WIN
            [EQ_MP (SYM (SPEC (--`?n. t = SUC n`--) EQ_CLAUSE1))
                   (ASSUME (--`(?n. t = SUC n)`--))]);
      DO (CONVERT_WIN LEFT_AND_EXISTS_CONV);
      DO (OPEN_WIN [RAND,BODY,RAND]);
         DO (REWRITE_WIN [ASSUME (--`t = SUC n`--), PARITY_DEF]);
         DO (OPEN_CONTEXT((--`t = SUC n`--),[]));
         DO (RULE_WIN (AP_TERM (--`PRE`--)));
         DO (REWRITE_WIN [theorem "prim_rec" "PRE"]);
         DO (REWRITE_WIN [theorem "arithmetic" "PRE_SUB1"]);
         DO (RULE_WIN SYM);
         DO CLOSE_WIN;
      DO (REWRITE_WIN[SYM (ASSUME (--`t = SUC n`--)),
                      ASSUME (--`n = t - 1`--)]);
      DO (REWRITE_WIN[SYM (REWRITE_RULE[ASSUME (--`~(t = 0)`--)]
                          (SPECL[(--`PARITY inp`--),(--`t:num`--)] REG_DEF))]);
      DO (REWRITE_WIN [GEN_ALL (SYM (SPEC_ALL NOT_DEF))]);
      DO (REWRITE_WIN [GEN_ALL (SYM (SPEC_ALL MUX_DEF))]);
      DO CLOSE_WIN;
   DO (CONVERT_WIN EXISTS_AND_CONV);
   DO (REWRITE_WIN [ASSUME (--`?n. t = SUC n`--)]);
   DO CLOSE_WIN;

DO (OPEN_WIN [RATOR,RATOR,RAND]);
   DO (PURE_ONCE_REWRITE_WIN [SYM (SPEC ((--`t = 0`--)) COND_T_F)]);
   DO (PURE_ONCE_REWRITE_WIN [GEN_ALL (SYM (SPEC_ALL NOT_CLAUSE1))]);
   DO (PURE_ONCE_REWRITE_WIN [COND_AP]);
   DO (PURE_ONCE_REWRITE_WIN [NOT_CLAUSES]);
   DO (OPEN_WIN [RAND,RAND]);
      DO (TRANSFORM_WIN (SYM (SPEC (--`t - 1`--) ONE_DEF)));
      DO CLOSE_WIN;
   DO (PURE_ONCE_REWRITE_WIN [GEN_ALL (SYM (SPEC_ALL REG_DEF))]);
   DO (PURE_ONCE_REWRITE_WIN [GEN_ALL (SYM (SPEC_ALL NOT_DEF))]);
   DO CLOSE_WIN;

DO (REWRITE_WIN [GEN_ALL (SYM (SPEC_ALL MUX_DEF))]);
DO CLOSE_WIN;
DO (REWRITE_WIN [EQ_EXT_EQ]);

WIN_THM ();

END_STACK "demo6";
