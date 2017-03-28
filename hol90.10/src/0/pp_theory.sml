(*---------------------------------------------------------------------------
 * HOL theories interpreted by SML structures.
 *
 *  
     fun stdOut_consumer() = 
       let val {say,flush} = !Compiler.Control.Print.out
       in {consumer=say, flush=flush, 
           linewidth = !Compiler.Control.Print.linewidth}
       end
     val stdOut_ppstrm = mk_ppstream(stdOut_consumer());
 *
 *---------------------------------------------------------------------------*)

functor PP_THEORY(structure Thm : Thm_sig
              structure Term : Term_sig
              structure Hol_pp : Hol_pp_sig
              sharing Thm.Term = Hol_pp.Term = Term) : NewIO_sig =
struct

structure Thm = Thm;
open Exception Lib;
open Thm Term Type;
open PP;

fun PP_THEORY_ERR f m = 
       HOL_ERR{origin_structure = "IO",
               origin_function = f, message = m};

val concat = Portable.String.concat;
val sort = Lib.sort (fn s1:string => fn s2 => s1<=s2);
val psort = Lib.sort (fn (s1:string,_:Thm.thm) => fn (s2,_:Thm.thm) => s1<=s2);
fun thm_terms th = concl th::hyp th;


fun Thry s = s^"Theory";
fun ThrySig s = s^"TheorySig";

local structure String = Portable.String
in
fun pp_theory_sig ppstrm {name,parents,axioms,definitions,theorems,
                          types,constants} =
 let val {add_string,add_break,begin_block,end_block,
          add_newline,flush_ppstream,...} = PP.with_ppstream ppstrm
     fun vblock(header, ob_pr, obs) =
             ( begin_block CONSISTENT 2;
               add_string ("(*  "^header^ "  *)");
               add_newline();
               PP.pr_list ob_pr (fn () => ()) add_newline obs;
               end_block())
     fun pparent s = String.concat ["structure ",Thry s," : ",ThrySig s]
     fun pr_thm (heading, ths) = vblock(heading, 
          (fn (s,th) => (begin_block CONSISTENT 0;
(*                         add_string(concat["val ",s, " : unit -> thm"]); *)
                           add_string(concat["val ",s, " : thm"]);
                         end_block())),  ths)
   in begin_block CONSISTENT 0;
      add_string ("signature "^ThrySig name^" ="); add_newline();
      begin_block CONSISTENT 2;
      add_string "sig"; add_newline();
      begin_block CONSISTENT 0;
      add_string"type thm"; add_newline(); add_newline();
      vblock ("Parents", add_string o pparent, sort parents); 
      if null axioms then () 
      else (add_newline(); add_newline(); pr_thm ("Axioms", psort axioms));
      if null definitions then () 
      else (add_newline(); add_newline();
            pr_thm("Definitions", psort definitions));
      if null theorems then () 
       else (add_newline(); add_newline(); pr_thm ("Theorems",psort theorems));
      end_block();
      end_block();
      add_newline(); add_string"end"; add_newline();
      end_block();
      flush_ppstream()
   end;
end;


val table_size = 311
val share_table = Array.array(table_size, [] :(Thm.Term.term * int)list);
val taken = ref 0;

fun reset_share_table () =
  (taken := 0;
   Lib.for_se 0 (table_size-1) (fn i => Array.update(share_table,i,[])));

  
(*---------------------------------------------------------------------------
 * Miscellaneous hash function taken from implementation of HOL signatures.
 *---------------------------------------------------------------------------*)

fun hash s = 
  let fun h(i,A) = h (i+1, (A*4 + Portable.String.ordof(s,i)) mod table_size)
                   handle Subscript => A
  in h end;


fun hash_type ty n = hash(Type.dest_vartype ty) (0,n)
  handle _ => let val {Tyop,Args} = Type.dest_type ty
              in itlist hash_type Args (hash Tyop (0,n))
              end;


fun dest_atom (Const r) = r
  | dest_atom (Fv r) = r
  | dest_atom _ = raise PP_THEORY_ERR"dest_atom" "not an atom";

fun hash_atom tm n = 
    let val {Name,Ty} = dest_atom tm
    in hash_type Ty (hash Name (0,n))
    end;


(*---------------------------------------------------------------------------
 * Add an atom to the atom hash table, checking to see if it is already there 
 * first. 
 *---------------------------------------------------------------------------*)
fun add tm = 
  let val i = hash_atom tm 0
      val els = Array.sub(share_table, i)
      fun loop [] = 
               (Array.update(share_table, i, (tm,!taken)::els);
                taken := !taken + 1)
        | loop ((x,index)::rst) = if (x=tm) then () else loop rst
  in 
    loop els
  end;


(*---------------------------------------------------------------------------
 * Get the vector index of an atom.
 *---------------------------------------------------------------------------*)
  
fun index tm = 
  let val i = hash_atom tm 0
      val els = Array.sub(share_table, i)
      fun loop [] = raise PP_THEORY_ERR"index" "not found in table"
        | loop ((x,index)::rst) = if (x=tm) then index else loop rst
  in 
    loop els
  end;


(*---------------------------------------------------------------------------
 * Traverse a term, performing a given (side-effecting) operation at the 
 * leaves. For our purposes, bound variables can be ignored.
 *---------------------------------------------------------------------------*)

fun trav f =
  let fun trv (a as Fv _) = f a
        | trv (a as Const _) = f a
        | trv (Comb{Rator, Rand}) = (trv Rator; trv Rand)
        | trv (Abs{Bvar, Body})  = (trv Bvar; trv Body)
        | trv _ = () 
  in trv end;


local val output = Portable.output
      val std_out = Portable.std_out
      val flush_out = Portable.flush_out
in
fun check V thml = 
  let val _ = Lib.mesg true "Checking consistency of sharing scheme"
      fun chk tm = 
         if (Vector.sub(V, index tm) = tm) 
          then ()
           else (Lib.mesg true "FAILURE in sharing scheme!"; 
                 raise PP_THEORY_ERR"check" "failure in sharing scheme")
  in Portable.List.app (app (trav chk) o thm_terms o snd) thml;
     Lib.mesg true "Completed successfully"
  end
end;


fun share_thy check_share thms =
  let val _ = reset_share_table()
      val _ = Portable.List.app (app (trav add) o thm_terms o snd) thms
      val L0 = Array.foldr (op @) [] share_table
      val L1 = Lib.sort (fn (_,i0) => fn (_,i1) => i0<=i1) L0
      val slist = map fst L1
      val _ = if check_share then check (Vector.fromList slist) thms else ()
  in
    slist
  end;


val space = " "
val comma = ","
val dot = "."
val dollar  = "$";
val percent = "%";

val CONSISTENT = PP.CONSISTENT
val INCONSISTENT = PP.INCONSISTENT;

(*---------------------------------------------------------------------------
 *  Raw syntax prettyprinter for terms. 
 *---------------------------------------------------------------------------*)

fun pp_raw_term pps tm = 
let val {add_string,add_break,begin_block,end_block,...} = PP.with_ppstream pps
    fun pr_term (Abs{Bvar,Body}) = 
            ( add_string "(\\"; pr_term Bvar; add_string dot;
                              add_break(1,0);  pr_term Body;
              add_string ")"
            )
      | pr_term (Comb{Rator, Rand}) =
           ( add_string "("; pr_term Rator; add_break(1,0); pr_term Rand;
             add_string ")"
           )
      | pr_term (ty_antiq _) = raise PP_THEORY_ERR"pr_term" "term construction"
      | pr_term (Bv i) = add_string (dollar^Lib.int_to_string i)
      | pr_term a = add_string(percent^Lib.int_to_string (index a))
in
  begin_block INCONSISTENT 0;
  add_string"`"; pr_term tm; add_string"`"; end_block()
end;

(*---------------------------------------------------------------------------
 * One needs to replace a backslash by two backslashes because one of them
 * disappears when sent through "output". Also need to add string quotes
 * at each end of the string.
 *---------------------------------------------------------------------------*)
local fun has_backslash s =
         let fun loop i = String.sub(s,i) = #"\\" orelse loop (i+1)
                          handle Subscript => false
         in loop 0 end
      fun add_backslashes s =
        let fun add i A = add (i+1) 
              (let val c = String.sub(s,i)
               in if (c = #"\\") then  (#"\\" :: #"\\" ::A) else c::A
               end) handle Subscript => String.implode(rev A)
        in add 0 []
        end
in
fun stringify s = Lib.quote
 (if (Lexis.ok_identifier s orelse not(has_backslash s)) then s
 else add_backslashes s);
end;
  

(*---------------------------------------------------------------------------
 *  Print a theory as a module.
 *---------------------------------------------------------------------------*)

fun pp_theory_struct ppstrm {name,parents,axioms,definitions,theorems,
                             types,constants} =
 let val {add_string,add_break,begin_block,end_block,
          add_newline,flush_ppstream,...} = PP.with_ppstream ppstrm
     val pp_tm = pp_raw_term ppstrm
     val pp_ty = Hol_pp.pp_type ppstrm
     fun vblock(header, ob_pr, obs) =
            ( begin_block CONSISTENT 2;
              add_string ("(*  "^header^ "  *)"); add_newline();
              PP.pr_list ob_pr (fn () => ()) add_newline obs; end_block())
     fun pparent s = String.concat ["structure ",Thry s," = ",Thry s]
     fun pr_fields{Name,Ty} = 
         (begin_block CONSISTENT 0;
          add_string"{";
          begin_block CONSISTENT 0;
          add_string"Name"; add_break(1,0); add_string "="; add_break (1,0);
          add_string(stringify Name);
          end_block();
          add_string","; add_break(1,0);
          begin_block CONSISTENT 0;
          add_string"Ty"; add_break (1,0); add_string "="; add_break(1,0);
          add_string"pty"; add_break(0,0); add_string"`:";
          pp_ty Ty; add_string"`";
          end_block();
          add_string"}"; end_block())
     fun pr_atom (Fv r) = (
            begin_block INCONSISTENT 2;
            add_string"mk_var"; add_break(0,0); pr_fields r; end_block())
       | pr_atom (Const r) = 
            (begin_block INCONSISTENT 2;
             add_string"mk_const"; add_break(0,0); pr_fields r; end_block())
       | pr_atom _ = raise PP_THEORY_ERR"pp_theory_struct.pr_atom" "not atomic"
     fun pr_bind (s,th) = 
      let val (asl,w) = Thm.dest_thm th
      in
         begin_block INCONSISTENT 0;
         add_string"val"; add_break(1,0);
         add_string s; add_break (1,0);
         add_string "="; add_break (1,0);
         add_string"DT"; add_break (0,0); add_string"(";
          begin_block CONSISTENT 0;
           add_string"[";
           begin_block INCONSISTENT 0;
           pr_list pp_tm (fn() => add_string",") (fn() => add_break(1,0)) asl;
           add_string "]";
           add_string","; add_break(1,0);
           pp_tm w;
          end_block();
         add_string")";
         end_block();
         end_block()
      end
     val thml = axioms@definitions@theorems
     val slist = share_thy false thml
     fun bind_theorems () = (
      begin_block CONSISTENT 0;
      add_string "local"; add_break(1,0);
      begin_block CONSISTENT 0;
      add_string "val pty = Parse.type_parser"; add_newline();
      add_string "val share_table = Vector.fromList";add_newline();
      add_string "[";
      begin_block CONSISTENT 0;
      pr_list pr_atom (fn () => add_string",") (fn () => add_break(1,0)) slist;
      end_block();
      add_string "]"; add_newline();
      add_string"fun rtp q = CoreHol.Theory.raw_term_parser share_table q";
      add_newline();
(*add_string"fun DT(asl,w) () = CoreHol.Thm.mk_disk_thm(map rtp asl, rtp w)";*)
   add_string"fun DT(asl,w) = CoreHol.Thm.mk_disk_thm(map rtp asl, rtp w)";
      end_block();
      add_newline();
      add_string"in"; add_newline();
      begin_block CONSISTENT 0;
      pr_list pr_bind (fn () => ()) add_newline thml;
      end_block();
      add_newline();
      add_string"end";
      end_block())
   in 
      begin_block CONSISTENT 0;
(*  add_string (concat ["structure ",Thry name," : ", ThrySig name," ="]);  *)
      add_string (concat ["functor ",Thry name,"() : ", ThrySig name," ="]);
      add_newline();
      begin_block CONSISTENT 2;
      add_string "struct"; add_newline();
      begin_block CONSISTENT 0;
      add_string"type thm = CoreHol.Thm.thm"; add_newline(); 
      add_string"val mk_const = CoreHol.Dsyntax.mk_const"; add_newline();
      add_string"val mk_var = CoreHol.Term.mk_var"; add_newline();
      add_newline();
      vblock ("Parents", add_string o pparent, sort parents); 
      add_newline(); 
      (* theory graph operations still to come *)
      bind_theorems (); add_newline();
      end_block();
      end_block();
      add_break(0,0); add_string"end"; add_newline();
      end_block();
      flush_ppstream()
   end;

end;
