BEGIN_STACK "demo3"
	(--`($==>) (((x = 1) /\ (y = 2)) /\ !x.((x + 1) = y))`--) [] [];

DO (OPEN_WIN [RAND, RAND, BODY]);
DO (REWRITE_WIN [ASSUME (--`y = 2`--)]);
DO CLOSE_WIN;

WIN_THM ();

END_STACK "demo3";
