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

