(* Syntactic type for processes with denotational semantics.		*)
(* 									*)
(* FILE		  : csp_syntax.ml 					*)
(* 									*)
(* READS FILES	  : process.th			          		*)
(* LOADS LIBRARIES : sets, string		          		*)
(* WRITES FILES    : csp_syntax.th					*)
(*									*)
(* AUTHOR	  : Albert J Camilleri					*)
(* AFFILIATION     : Hewlett-Packard Laboratories, Bristol		*)
(* DATE		  : 89.03.15						*)
(* REVISED	  : 91.10.01						*)
(*                : 21.06.93 - BtG - ported to hol90                    *)

new_theory "csp_syntax";               
(*
load_library "sets";
load_library "string";
*)
new_parent "process";

val event    = ty_antiq(==`:string`==);
val trace    = ty_antiq(==`:^event list`==);
val alphabet = ty_antiq(==`:^event set`==);

val environment = ty_antiq(==`:string -> (^event + process)`==);

val Event = define_type {name="Event",
			 type_spec=`Event = econst of string | evar of string`,
			 fixities=[Prefix,Prefix]};

val Event_INDUCT  = prove_induction_thm Event;
val Event_ONE_ONE = prove_constructors_one_one Event;
val Event_DISTINCT = prove_constructors_distinct Event;

val ES =
    new_recursive_definition
      {fixity=Prefix,
       rec_axiom=Event,
       name="ES",
       def=(--`((ES (econst s) (E:^environment)) = s) /\
        ((ES (evar s) E) = OUTL (E s))`--)};

val CSP =
    define_type
    {name="CSP",
     fixities=[Prefix,Prefix,Prefix,Prefix,Prefix,Prefix,Prefix,Prefix,Prefix],
     type_spec = `CSP = stop of ^alphabet |
                        run of ^alphabet |
			var of string |
			pref of Event => CSP |
		        Choice of string => ^alphabet => CSP |
			par of CSP => CSP |
		        after of CSP => ^trace |
			mu of string => ^alphabet => CSP |
			cond of Event => Event => CSP => CSP`};

val Bnd =
    new_definition
       ("Bnd",
        (--`Bnd s exp (env: ^environment) = \s'. (s' = s) => exp | (env s)`--));

val TS =
    new_recursive_definition
      {fixity=Prefix,
       rec_axiom=CSP,
       name="TS",
       def=(--`((TS (stop A) E) = STOP A) /\
	       ((TS (run A) E) = RUN A) /\
	       ((TS (var s) E) = OUTR (E s)) /\
	       ((TS (pref a P) E) = ((ES a E) --> (TS P E))) /\
	       ((TS (Choice s A P) E) =
		(choice A (\x:^event. TS P (Bnd s (INL x) E)))) /\
	       ((TS (par P Q) E) = (TS P E) PAR (TS Q E)) /\
	       ((TS (after P tr) E) = (TS P E) / tr) /\
	       ((TS (mu s A P) E) =
		(MU A (\x:process. TS P (Bnd s (INR x) E)))) /\
	       ((TS (cond e1 e2 P Q) E) =
		((ES e1 E = ES e2 E) => TS P E | TS Q E))`--)};

val CSP_INDUCT = prove_induction_thm CSP;

export_theory ();
