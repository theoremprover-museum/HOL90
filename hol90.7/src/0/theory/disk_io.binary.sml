functor DISK_IO_BINARY(Regime : Regime_sig):Disk_io_sig =
struct
structure Regime = Regime;



type hol_sig = Regime.hol_sig
type hol_thms = Regime.hol_thms

(* V 88 and higher *)
fun read_hol_sig i:hol_sig = System.Unsafe.blast_read(i, can_input i);
fun read_hol_thms i:hol_thms = System.Unsafe.blast_read(i, can_input i);
fun write_hol_sig(ostm,hsig) = (System.Unsafe.blast_write(ostm,(hsig:hol_sig));
                                ());
fun write_hol_thms(ostm,ths) = (System.Unsafe.blast_write(ostm,(ths:hol_thms));
                                ());

(* V87 and lower *)
(*
**fun read_hol_sig i:hol_sig = System.Unsafe.blast_read i;
**fun read_hol_thms i:hol_thms = System.Unsafe.blast_read i;
**fun write_hol_sig(ostm,hsig) = System.Unsafe.blast_write(ostm,(hsig:hol_sig));
**fun write_hol_thms(ostm,ths) = System.Unsafe.blast_write(ostm,(ths:hol_thms));
*)
end; (* DISK_IO *)


