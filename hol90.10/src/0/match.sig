(* ===================================================================== *)
(* FILE          : match.sig                                             *)
(* DESCRIPTION   : Signature for functions implementing type and term    *)
(*                 matching.                                             *)
(*                                                                       *)
(* AUTHOR        : Konrad Slind, University of Calgary                   *)
(* DATE          : August 26, 1991                                       *)
(* ===================================================================== *)


signature Match_sig =
sig
structure Term : Public_term_sig
val match_type : Term.Type.hol_type -> Term.Type.hol_type -> 
                 Term.Type.hol_type Lib.subst
val match_term : Term.term -> Term.term -> 
                 (Term.term Lib.subst * Term.Type.hol_type Lib.subst)
end;
