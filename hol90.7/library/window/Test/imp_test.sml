BEGIN_STACK "test" (--`($==>) (A /\ B)`--) [] [];
DO (OPEN_WIN [RATOR,RAND]);
DO (TRANSFORM_WIN (mk_thm([(--`B:bool`--)],(--`A ==> C`--))));
DO CLOSE_WIN;
WIN_THM ();
END_STACK "test";

BEGIN_STACK "test" (--`($==>) (A /\ B)`--) [] [];
DO (OPEN_WIN [RAND]);
DO (TRANSFORM_WIN (mk_thm([(--`A:bool`--)],(--`B ==> C`--))));
DO CLOSE_WIN;
WIN_THM ();
END_STACK "test";

BEGIN_STACK "test" (--`($==>) (A ==> B)`--) [] [];
DO (OPEN_WIN [RATOR,RAND]);
DO (TRANSFORM_WIN (mk_thm([(--`~B`--)],(--`A <== C`--))));
DO CLOSE_WIN;
WIN_THM ();
END_STACK "test";

BEGIN_STACK "test" (--`($==>) (A ==> B)`--) [] [];
DO (OPEN_WIN [RAND]);
DO (TRANSFORM_WIN (mk_thm([(--`A:bool`--)],(--`B ==> C`--))));
DO CLOSE_WIN;
WIN_THM ();
END_STACK "test";

BEGIN_STACK "test" (--`($==>) (A <== B)`--) [] [];
DO (OPEN_WIN [RATOR,RAND]);
DO (TRANSFORM_WIN (mk_thm([(--`B:bool`--)],(--`A ==> C`--))));
DO CLOSE_WIN;
WIN_THM ();
END_STACK "test";

BEGIN_STACK "test" (--`($==>) (A <== B)`--) [] [];
DO (OPEN_WIN [RAND]);
DO (TRANSFORM_WIN (mk_thm([(--`~A`--)],(--`B <== C`--))));
DO CLOSE_WIN;
WIN_THM ();
END_STACK "test";

BEGIN_STACK "test" (--`($==>) (A \/ B)`--) [] [];
DO (OPEN_WIN [RATOR,RAND]);
DO (TRANSFORM_WIN (mk_thm([(--`~B`--)],(--`A ==> C`--))));
DO CLOSE_WIN;
WIN_THM ();
END_STACK "test";

BEGIN_STACK "test" (--`($==>) (A \/ B)`--) [] [];
DO (OPEN_WIN [RAND]);
DO (TRANSFORM_WIN (mk_thm([(--`~A`--)],(--`B ==> C`--))));
DO CLOSE_WIN;
WIN_THM ();
END_STACK "test";

BEGIN_STACK "test" (--`($==>) (~A)`--) [] [];
DO (OPEN_WIN [RAND]);
DO (TRANSFORM_WIN (mk_thm([],(--`A <== B`--))));
DO CLOSE_WIN;
WIN_THM ();
END_STACK "test";

BEGIN_STACK "test" (--`($==>) (!v:'a.A v)`--) [] [];
DO (OPEN_WIN [RAND,BODY]);
DO (TRANSFORM_WIN (mk_thm([],(--`(A (v:'a)) ==> B v`--))));
DO CLOSE_WIN;
WIN_THM ();
END_STACK "test";

BEGIN_STACK "test" (--`($==>) (?v:'a.A v)`--) [] [];
DO (OPEN_WIN [RAND,BODY]);
DO (TRANSFORM_WIN (mk_thm([],(--`(A (v:'a)) ==> B v`--))));
DO CLOSE_WIN;
WIN_THM ();
END_STACK "test";

BEGIN_STACK "test" (--`($<==) (A /\ B)`--) [] [];
DO (OPEN_WIN [RATOR,RAND]);
DO (TRANSFORM_WIN (mk_thm([(--`B:bool`--)],(--`A <== C`--))));
DO CLOSE_WIN;
WIN_THM ();
END_STACK "test";

BEGIN_STACK "test" (--`($<==) (A /\ B)`--) [] [];
DO (OPEN_WIN [RAND]);
DO (TRANSFORM_WIN (mk_thm([(--`A:bool`--)],(--`B <== C`--))));
DO CLOSE_WIN;
WIN_THM ();
END_STACK "test";

BEGIN_STACK "test" (--`($<==) (A ==> B)`--) [] [];
DO (OPEN_WIN [RATOR,RAND]);
DO (TRANSFORM_WIN (mk_thm([(--`~B`--)],(--`A ==> C`--))));
DO CLOSE_WIN;
WIN_THM ();
END_STACK "test";

BEGIN_STACK "test" (--`($<==) (A ==> B)`--) [] [];
DO (OPEN_WIN [RAND]);
DO (TRANSFORM_WIN (mk_thm([(--`A:bool`--)],(--`B <== C`--))));
DO CLOSE_WIN;
WIN_THM ();
END_STACK "test";

BEGIN_STACK "test" (--`($<==) (A <== B)`--) [] [];
DO (OPEN_WIN [RATOR,RAND]);
DO (TRANSFORM_WIN (mk_thm([(--`B:bool`--)],(--`A <== C`--))));
DO CLOSE_WIN;
WIN_THM ();
END_STACK "test";

BEGIN_STACK "test" (--`($<==) (A <== B)`--) [] [];
DO (OPEN_WIN [RAND]);
DO (TRANSFORM_WIN (mk_thm([(--`~A`--)],(--`B ==> C`--))));
DO CLOSE_WIN;
WIN_THM ();
END_STACK "test";

BEGIN_STACK "test" (--`($<==) (A \/ B)`--) [] [];
DO (OPEN_WIN [RATOR,RAND]);
DO (TRANSFORM_WIN (mk_thm([(--`~B`--)],(--`A <== C`--))));
DO CLOSE_WIN;
WIN_THM ();
END_STACK "test";

BEGIN_STACK "test" (--`($<==) (A \/ B)`--) [] [];
DO (OPEN_WIN [RAND]);
DO (TRANSFORM_WIN (mk_thm([(--`~A`--)],(--`B <== C`--))));
DO CLOSE_WIN;
WIN_THM ();
END_STACK "test";

BEGIN_STACK "test" (--`($<==) (~A)`--) [] [];
DO (OPEN_WIN [RAND]);
DO (TRANSFORM_WIN (mk_thm([],(--`A ==> B`--))));
DO CLOSE_WIN;
WIN_THM ();
END_STACK "test";

BEGIN_STACK "test" (--`($<==) (!v:'a.A v)`--) [] [];
DO (OPEN_WIN [RAND,BODY]);
DO (TRANSFORM_WIN (mk_thm([],(--`(A (v:'a)) <== B v`--))));
DO CLOSE_WIN;
WIN_THM ();
END_STACK "test";

BEGIN_STACK "test" (--`($<==) (?v:'a.A v)`--) [] [];
DO (OPEN_WIN [RAND,BODY]);
DO (TRANSFORM_WIN (mk_thm([],(--`(A (v:'a)) <== B v`--))));
DO CLOSE_WIN;
WIN_THM ();
END_STACK "test";
