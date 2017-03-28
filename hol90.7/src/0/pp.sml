(* *************************************************************************
 * Adapted from utilities in the SML/NJ compiler, which were written by 
 * Konrad Slind and Dave MacQueen.
 *
 ***************************************************************************)

structure PP : PP_sig =
struct

(* sml/nj 93 open System.PrettyPrint; *)
(* sml/nj 102 open Compiler.PrettyPrint; open Compiler.PPTable; *)
open System.PrettyPrint;

val mk_consumer = Lib.I;

(* sml/nj 93
 * fun defaultConsumer () =
 *       {consumer = System.Print.say,
 *        linewidth = !System.Print.linewidth,
 *        flush = System.Print.flush};
 **********************************************************)
(* sml/nj 102
 * fun defaultConsumer () =
 *         {consumer = Lib.say,
 *          linewidth = !Globals.linewidth,
 *          flush = Compiler.Control.Print.flush};
 ***********************************************************)

fun defaultConsumer () =
       {consumer = System.Print.say,
        linewidth = !System.Print.linewidth,
        flush = System.Print.flush};

fun with_ppstream ppstrm = 
   {add_string = add_string ppstrm, 
    add_break = add_break ppstrm, 
    begin_block = begin_block ppstrm, 
    end_block=fn () => end_block ppstrm, 
    add_newline=fn () => add_newline ppstrm, 
    clear_ppstream=fn () => clear_ppstream ppstrm, 
    flush_ppstream=fn () => flush_ppstream ppstrm};



(* Simple and heavily used.
 * pfun = item printing function
 * dfun = delimiter printing function
 * bfun = break printer function
 *******************************************)
fun pr_list pfun dfun bfun =
   let fun pr [] = ()
         | pr [i] = pfun i
         | pr (i::rst) = ( pfun i; dfun() ; bfun() ; pr rst )
   in  pr 
   end;

(****************************************************************************
 * 
 *  fun pp_seq0 ppstream (sep:ppstream->unit,pr) =
 *     let val prstrm = pr ppstream
 *         fun prElems [el] = prstrm el
 *           | prElems (el::rest) = (prstrm el; sep ppstream; prElems rest)
 *           | prElems [] = ()
 *     in prElems 
 *     end
 * 
 * fun pp_seq ppstream {sep:ppstream->unit, 
 *                      pr:ppstream->'a->unit, 
 *                      indent:int, style:break_style} alist =
 *     (begin_block ppstream style indent;
 *      pp_seq0 ppstream (sep,pr) alist;
 *      end_block ppstream)
 *
 * fun pp_seqC ppstream {sep,pr,indent} = 
 *         pp_seq ppstream {sep = sep, pr = pr, indent = indent,
 *                          style = CONSISTENT};
 *
 * fun pp_seqI ppstream {sep,pr,indent} = 
 *         pp_seq ppstream {sep = sep, pr = pr, indent = indent,
 *                          style = INCONSISTENT};
 *
 * fun pp_vseq ppstrm {indent, sep:string, pr} =
 *    pp_seqC ppstrm {sep = fn ppstrm =>(add_string ppstrm sep; 
 *                                       add_newline ppstrm), 
 *                    pr = pr, indent = indent};
 *
 * fun pp_delimited_seq ppstream
 *          {front:ppstream->unit,
 *           back:ppstream->unit,
 *           pr:ppstream->'a list->unit} (elems:'a list) =
 *     (begin_block ppstream CONSISTENT 0;
 *      front ppstream;
 *      pr ppstream elems; 
 *      back ppstream;
 *      end_block ppstream)
 ***************************************************************************)

end; (* PPutil *)
