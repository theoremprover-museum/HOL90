BEGIN_STACK "demo2" (--`($=) (((x = 1) /\ (y = 2)) /\ ((x + 1) = y))`--) [] [];

DO (OPEN_WIN [RAND]);
    DO (REWRITE_WIN [ASSUME (--`x = 1`--), ASSUME (--`y = 2`--)]);
DO CLOSE_WIN;

WIN_THM ();

END_STACK "demo2";
