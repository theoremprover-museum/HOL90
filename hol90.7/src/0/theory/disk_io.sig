signature Disk_io_sig =
sig
structure Regime : Regime_sig
val read_hol_sig : instream -> Regime.hol_sig
val write_hol_sig : (outstream * Regime.hol_sig) -> unit
val read_hol_thms : instream -> Regime.hol_thms
val write_hol_thms : (outstream * Regime.hol_thms) -> unit
end;
