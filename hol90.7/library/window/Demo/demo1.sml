BEGIN_STACK "demo1" (--`($=) ((x = 1) /\ ((x + 1) = 2))`--) [] [];

DO (OPEN_WIN [RAND]);
    DO (REWRITE_WIN [ASSUME (--`x = 1`--)]);
DO CLOSE_WIN;

WIN_THM ();

END_STACK "demo1";
