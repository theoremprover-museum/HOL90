(* Do Case analysis about a term.                                            *)
local
val CASES_THM = prove(
   (--`!a b. (a \/ b) ==> (!p. p = ((a ==> p) /\ (b ==> p)))`--)
   ,
   (REPEAT GEN_TAC) THEN
   (BOOL_CASES_TAC (--`a:bool`--)) THEN
   (BOOL_CASES_TAC (--`b:bool`--)) THEN
   (REWRITE_TAC [])
   )
in
	fun CASES_CONV th tm = SPEC tm (MATCH_MP CASES_THM th)
end;

BEGIN_STACK "demo4"
    (--`($<==)
        (!a b c d.(~a ==> b) ==> ~(c ==> a) \/ ~a ==> (~a ==> b ==> d) ==>d)
    `--)
    []
    [];

DO (OPEN_WIN [RAND,BODY,RAND,BODY,RAND,BODY,RAND,BODY,RAND,RAND,RAND]);
    DO (CONJECTURE (--`~a`--));
    DO (OPEN_CONTEXT ((--`~a ==> b`--),[]));
        DO (REWRITE_WIN [ASSUME (--`~a`--)]);
    DO CLOSE_WIN;
    DO (OPEN_CONTEXT ((--`~a ==> b ==> d`--),[]));
        DO (REWRITE_WIN [ASSUME (--`~a`--), ASSUME (--`b:bool`--)]);
    DO CLOSE_WIN;
    DO (REWRITE_WIN [ASSUME (--`d:bool`--)]);
    DO (ESTABLISH (--`~a`--));
        DO (CONVERT_WIN (CASES_CONV (ASSUME (--`~(c ==> a) \/ ~a`--))));
        DO (OPEN_WIN [RATOR, RAND, RAND]);
            DO (REWRITE_WIN [ASSUME (--`~a`--)]);
        DO CLOSE_WIN;
        DO (REWRITE_WIN []);
    DO CLOSE_WIN;
DO CLOSE_WIN;
DO (REWRITE_WIN []);

WIN_THM();

END_STACK "demo4";
