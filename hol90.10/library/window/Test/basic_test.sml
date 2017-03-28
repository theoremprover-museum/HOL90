BEGIN_STACK "test" (--`($=) ((f:'a->'b) x)`--) [] [];
DO (OPEN_WIN [RATOR]);
DO (TRANSFORM_WIN (mk_thm([],(--`(f:'a->'b) = g`--))));
DO CLOSE_WIN;
WIN_THM ();
END_STACK "test";

BEGIN_STACK "test" (--`($=) ((f:'a->'b) x)`--) [] [];
DO (OPEN_WIN [RAND]);
DO (TRANSFORM_WIN (mk_thm([],(--`(x:'a) = y`--))));
DO CLOSE_WIN;
WIN_THM ();
END_STACK "test";

BEGIN_STACK "test" (--`($==>) (A => B | C)`--) [] [];
DO (OPEN_WIN [RATOR,RAND]);
DO (TRANSFORM_WIN (mk_thm([(--`A:bool`--)],(--`(B:bool) = D`--))));
DO CLOSE_WIN;
WIN_THM ();
END_STACK "test";

BEGIN_STACK "test" (--`($==>) (A => B | C)`--) [] [];
DO (OPEN_WIN [RAND]);
DO (TRANSFORM_WIN (mk_thm([(--`~A`--)],(--`(C:bool) = D`--))));
DO CLOSE_WIN;
WIN_THM ();
END_STACK "test";

BEGIN_STACK "test" (--`($==>) ((\v:'a. f v) c)`--) [] [];
DO (OPEN_WIN [RATOR,BODY]);
DO(TRANSFORM_WIN(mk_thm([(--`(v:'a)=c`--)],(--`((f:'a ->bool) v)==>(g v)`--))));
DO CLOSE_WIN;
WIN_THM ();
END_STACK "test";

BEGIN_STACK "test" (--`($==>) (let (v:'a) = c in f v)`--) [] [];
DO (OPEN_WIN [RATOR,RAND,BODY]);
DO(TRANSFORM_WIN(mk_thm([(--`(v:'a)=c`--)],(--`((f:'a ->bool) v)==>(g v)`--))));
DO CLOSE_WIN;
WIN_THM ();
END_STACK "test";

