(* Reading and writing theories from and to disk. Replace only this module,
   Disk_io, and Regime if you want a different arrangement of theories on 
   disk. In the current design, a theory X is represented by 2 binary 
   files: X.holsig and X.thms. If you only want to change the representation 
   of a theory component, e.g., from binary to ascii, all you have to do 
   is change Disk_io.
*)
functor THEORY_IO(structure Disk_io : Disk_io_sig
                  structure File : File_sig) : Theory_io_sig =
struct
structure Theory_data = Disk_io.Regime.Theory_data;

fun THEORY_IO_ERR{function,message} =
      HOL_ERR{origin_structure = "Theory_io",
	      origin_function = function,
	      message = message}

type hol_sig = Disk_io.Regime.hol_sig;
type hol_thms = Disk_io.Regime.hol_thms;

val hol_sig_suffix = ".holsig";
val thms_suffix = ".thms";

val theory_to_hol_sig = Disk_io.Regime.theory_to_hol_sig
val dest_hol_sig = Disk_io.Regime.dest_hol_sig;
val mk_theory = Disk_io.Regime.mk_theory_from_parts


val get_hol_sig_by_name = File.get_file_by_name{reader = Disk_io.read_hol_sig,
                                                suffix = hol_sig_suffix};

val get_hol_sig_by_uid = File.get_file_by_key
                               {reader = Disk_io.read_hol_sig,
                                suffix = hol_sig_suffix,
                                eq = Theory_data.theory_id_eq,
                                key_of = #thid o Disk_io.Regime.dest_hol_sig,
                                name_of = Theory_data.theory_id_name};

(* When one calls this, one needs to have the constants of the theory already 
   in the symbol table, since a mild form of parsing is done.
*)
val get_thms = File.get_file_by_key
                     {reader = Disk_io.read_hol_thms,
                      suffix = thms_suffix,
                      eq = Theory_data.theory_id_eq,
                      key_of = #thid o Disk_io.Regime.dest_hol_thms,
                      name_of = Theory_data.theory_id_name};


local
fun open_theory_outstreams path name = 
   let val out1 = open_out (path^name^hol_sig_suffix)
   in
       let val out2 = open_out (path^name^thms_suffix)
       in
       (out1,out2)
       end
       handle (Io s) => (close_out out1;
                         raise THEORY_IO_ERR{function="open_theory_outstreams",
                                             message = s})
   end
   handle (Io s) => raise THEORY_IO_ERR{function = "open_theory_outstreams",
                                        message = s}
in
fun put_theory_to_disk thry =
   let val name = (Theory_data.theory_id_name o Theory_data.theory_id) thry
       val outfile_prefix = hd(!Globals.theory_path)
       val (outstrm1,outstrm2) = open_theory_outstreams outfile_prefix name
       val (hsig,thms) = Disk_io.Regime.split_theory thry
   in
     Disk_io.write_hol_sig (outstrm1, hsig);
     Disk_io.write_hol_thms(outstrm2, thms);
     close_out outstrm1;
     close_out outstrm2
   end
   handle _ => raise THEORY_IO_ERR{function = "put_theory_to_disk",
			          message ="error when writing theory to disk"}
end;


(*
** fun theory_exists path s = 
**   (get_thms path (#thid(dest_hol_sig(get_hol_sig_by_name path s)));
**    true)
**   handle e => false;
*)

end; (* THEORY_IO *)
