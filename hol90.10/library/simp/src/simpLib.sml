signature simpLib_sig =
sig
  structure Simplifier : Simplifier_sig
  structure Simpsets : Simpsets_sig
  structure arith_ss : arith_ss_sig
end;

structure simpLib :simpLib_sig =
struct
  structure Simplifier = Simplifier
  structure Simpsets = Simpsets
  structure arith_ss = arith_ss
end;
