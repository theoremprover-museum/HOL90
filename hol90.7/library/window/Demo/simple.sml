(* Just go through the examples in this file *)

(* Load the window library *)
load_library{lib = window_lib, theory = "foo"};

(* If you don't have a lot of time or memory, use this:
 *
 *    prim_load_library Lib.compile {lib = window_lib, theory = "foo"};
 *
 **********************************************************************)



(* The first example *)
BEGIN_STACK "demo1" (--`($=) ((x = 1) /\ ((x + 1) = 2))`--) [] [];

DO (OPEN_WIN [RAND]);
    DO (REWRITE_WIN [ASSUME (--`x = 1`--)]);
DO CLOSE_WIN;

WIN_THM ();

END_STACK "demo1";


(* The second example  *)
BEGIN_STACK "demo2" (--`($=) (((x = 1) /\ (y = 2)) /\ ((x + 1) = y))`--) [] [];

DO (OPEN_WIN [RAND]);
    DO (REWRITE_WIN [ASSUME (--`x = 1`--), ASSUME (--`y = 2`--)]);
DO CLOSE_WIN;

WIN_THM ();

END_STACK "demo2";



(* The third example   *)
BEGIN_STACK "demo3"
	(--`($==>) (((x = 1) /\ (y = 2)) /\ !x.((x + 1) = y))`--) [] [];

DO (OPEN_WIN [RAND, RAND, BODY]);
DO (REWRITE_WIN [ASSUME (--`y = 2`--)]);
DO CLOSE_WIN;

WIN_THM ();

END_STACK "demo3";


(* The fourth example. Needs the following rule for doing case analysis
 * about a term.
 ************************************************************************)
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


(* A logic puzzle.    *)

BEGIN_STACK
	"demo5"
(--`
   ($<==)
   (!jar:bool.
    !sterile:bool->bool.
    !heated:bool->bool.
    !bug:bool->bool .
    !animal:bool->bool .
    !isin:bool->bool->bool.
    !dead:bool->bool.
	(((heated jar) /\ (!x. ((bug x) ==> (animal x))) /\
        (!x.(!y. (((heated y) /\ (isin x y) /\ (animal x)) ==> (dead x)))) /\
	(!y. (!x. ((isin x y) /\ (bug x)) ==> (dead x)) ==> (sterile y)))
	==> (sterile jar)))
                                    `--)
	[] [];

DO (OPEN_WIN [RAND,BODY,RAND,BODY,RAND,BODY,RAND,BODY,RAND,BODY,RAND,BODY,
				RAND,BODY,RAND]);
DO (TRANSFORM_WIN (IMP_PMI (SPEC (--`jar:bool`--) (ASSUME 
    (--`!y:bool. (!x:bool. isin x y /\ bug x ==> dead x) ==> sterile y`--)))));
DO (OPEN_WIN [RAND,BODY,RAND]);
DO (TRANSFORM_WIN (IMP_PMI (SPECL [(--`x:bool`--),(--`jar:bool`--)] (ASSUME
   (--`!(x:bool) (y:bool). heated y /\ isin x y /\ animal x ==> dead x`--)))));
DO (ASM_REWRITE_WIN []);
DO (TRANSFORM_WIN (IMP_PMI (SPEC (--`x:bool`--)
	(ASSUME (--`!x:bool. bug x ==> animal x`--)))));
DO (ASM_REWRITE_WIN []);
DO CLOSE_WIN;
DO (REWRITE_WIN []);
DO CLOSE_WIN;
DO (REWRITE_WIN []);

WIN_THM ();

END_STACK "demo5";

