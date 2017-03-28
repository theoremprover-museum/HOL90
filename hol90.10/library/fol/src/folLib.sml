signature folLib_sig =
sig
   structure FOL : FOL_sig
   structure FOL_HOL : FOL_HOL_sig
end;

structure folLib : folLib_sig =
struct
   structure FOL = FOL
   structure FOL_HOL = FOL_HOL
end;
