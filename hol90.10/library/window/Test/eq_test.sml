BEGIN_STACK "test" (--`($=) (A /\ B)`--) [] [];
DO (OPEN_WIN [RATOR,RAND]);
DO (TRANSFORM_WIN (mk_thm([(--`B:bool`--)],(--`(A:bool) = C`--))));
DO CLOSE_WIN;
WIN_THM ();
END_STACK "test";

BEGIN_STACK "test" (--`($=) (A /\ B)`--) [] [];
DO (OPEN_WIN [RAND]);
DO (TRANSFORM_WIN (mk_thm([(--`A:bool`--)],(--`(B:bool) = C`--))));
DO CLOSE_WIN;
WIN_THM ();
END_STACK "test";

BEGIN_STACK "test" (--`($=) (A ==> B)`--) [] [];
DO (OPEN_WIN [RATOR,RAND]);
DO (TRANSFORM_WIN (mk_thm([(--`~B`--)],(--`(A:bool) = C`--))));
DO CLOSE_WIN;
WIN_THM ();
END_STACK "test";

BEGIN_STACK "test" (--`($=) (A ==> B)`--) [] [];
DO (OPEN_WIN [RAND]);
DO (TRANSFORM_WIN (mk_thm([(--`A:bool`--)],(--`(B:bool) = C`--))));
DO CLOSE_WIN;
WIN_THM ();
END_STACK "test";

BEGIN_STACK "test" (--`($=) (A <== B)`--) [] [];
DO (OPEN_WIN [RATOR,RAND]);
DO (TRANSFORM_WIN (mk_thm([(--`B:bool`--)],(--`(A:bool) = C`--))));
DO CLOSE_WIN;
WIN_THM ();
END_STACK "test";

BEGIN_STACK "test" (--`($=) (A <== B)`--) [] [];
DO (OPEN_WIN [RAND]);
DO (TRANSFORM_WIN (mk_thm([(--`~A`--)],(--`(B:bool) = C`--))));
DO CLOSE_WIN;
WIN_THM ();
END_STACK "test";

BEGIN_STACK "test" (--`($=) (A \/ B)`--) [] [];
DO (OPEN_WIN [RATOR,RAND]);
DO (TRANSFORM_WIN (mk_thm([(--`~B`--)],(--`(A:bool) = C`--))));
DO CLOSE_WIN;
WIN_THM ();
END_STACK "test";

BEGIN_STACK "test" (--`($=) (A \/ B)`--) [] [];
DO (OPEN_WIN [RAND]);
DO (TRANSFORM_WIN (mk_thm([(--`~A`--)],(--`(B:bool) = C`--))));
DO CLOSE_WIN;
WIN_THM ();
END_STACK "test";

