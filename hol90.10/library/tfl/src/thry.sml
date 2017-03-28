structure Thry : Thry_sig = 
struct

structure USyntax  = USyntax;
structure Utils = USyntax.Utils;
open Mask
infix 3 |->;

type Type = USyntax.Type
type Preterm = USyntax.Preterm
type Term = USyntax.Term
type Thm = Thms.Thm
type Thry = String.string;


local fun mk_bind {redex,residue} = (redex |-> residue)
in fun mk_tfp_subst x = map mk_bind x
end;

fun match_term thry tm1 tm2 = 
   let val (th1,th2) = CoreHol.Match.match_term tm1 tm2
   in (mk_tfp_subst th1, mk_tfp_subst th2)
   end;

fun match_type thry ty1 ty2 = mk_tfp_subst(CoreHol.Match.match_type ty1 ty2);

fun typecheck thry = Lib.I

fun make_definition thry s tm = (CoreHol.Const_def.new_definition(s,tm), thry)

(*---------------------------------------------------------------------------
 * Accessing different parts of the underlying information for a datatype.
 *---------------------------------------------------------------------------*)
local open Utils
in
fun match_info thy s = 
(case (Utils.assoc1 (op=) s (Hol_datatype.current()))
 of SOME(_,{case_const,constructors,...}) => SOME{case_const=case_const,
                                                  constructors = constructors}
  | NONE => NONE)

fun induct_info thy s = 
(case (Utils.assoc1 (op=) s (Hol_datatype.current()))
 of SOME(_,{nchotomy, constructors,...}) => SOME{nchotomy=nchotomy,
                                                 constructors = constructors}
  | NONE => NONE)

fun extract_info thy = 
 let val (rws,congs) = Utils.itlist 
      (fn (_,{case_def, case_cong,...}) => 
       fn (R,C) => (case_def::R, case_cong::C))
       (Hol_datatype.current()) ([],[])
 in
 {case_congs = congs, case_rewrites = rws}
 end
end;


end; (* Thry *)
