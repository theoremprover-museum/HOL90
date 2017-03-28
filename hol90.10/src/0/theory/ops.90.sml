(*---------------------------------------------------------------------------
 * Implements the coordination between cache and disk. Also provides
 * routines that add to the theory graph, possibly with side-effects
 * (like adding constants to the symbol table).
 *---------------------------------------------------------------------------*)

functor THEORY_OPS(structure Globals : Globals_sig
                   structure Theory_data : Theory_data_sig
                   structure Theory_io : Theory_io_sig
                   structure Theory_cache : Theory_cache_sig
                   structure Theory_graph : Theory_graph_sig
                   structure Term : Term_sig
                   sharing Theory_io.Theory_data = Theory_data
                   sharing Theory_data.Thm.Term = Term
                   sharing type
                     Theory_data.theory = Theory_cache.object
                   sharing type
                     Theory_data.theory_id = Theory_graph.node_id
                   sharing type
                     Theory_cache.key = string)
                 : Theory_ops_sig =
struct
structure Theory_data = Theory_data;
structure Theory_io = Theory_io;
structure Theory_cache = Theory_cache;
structure Theory_graph = Theory_graph;

structure Term = Term;
open Theory_data;

fun THEORY_OPS_ERR{function,message} =
    Exception.HOL_ERR{origin_structure = "Theory_ops",
		      origin_function = function,
		      message = message}

val current_theory_name = theory_id_name o theory_id o the_current_theory;


(*****************************************************************************
 * There's a hack here for strings. If I load the theory of strings in,
 * I want string literals to be constants. But I can't interpret string
 * literals as string constants until that time. The call to 
 * Globals.assert_strings_defined does the job. It basically informs
 * Parse_support.make_string when it can make consts instead of variables.
 *****************************************************************************)
local
fun TY_CLASH{common_name, theory1, theory2} =
     THEORY_OPS_ERR{function =" install_hol_sig.add_type_const",
		    message = "\nType constant clash: "^Lib.quote common_name^
			      " appears in both "^Lib.quote theory1^" and "^
			      Lib.quote theory2^"\n"}
fun TM_CLASH {common_name,theory1,theory2} =
    THEORY_OPS_ERR{function = "install_hol_sig.add_term_const",
		   message = "\nTerm constant clash: "^Lib.quote common_name^
			      " appears in both "^Lib.quote theory1^" and "^
			      Lib.quote theory2^"\n"}
in
fun install_hol_sig hol_sig =
   let val {thid,type_constants,term_constants,...} = 
                                Theory_io.dest_hol_sig hol_sig
       val _ = if (Theory_data.theory_id_name thid = "string")
               then Globals.assert_strings_defined()
               else()
   in
   ( map Term.Type.add_type_const type_constants
     handle Term.Type.TYPE_SYMTAB_CLASH strs => raise (TY_CLASH strs);

     map (Term.add_term_const Term.Loading) term_constants
     handle Term.TERM_SYMTAB_CLASH strs => raise (TM_CLASH strs)
   )
   end
end;


val slash = "/";
(*****************************************************************************
 * The path is s1^s2, the normalized path is the path less the last component,
 * where components are separated by a slash.
 *****************************************************************************)
fun normalize_path (s1,s2) =
   let val p = s1^s2
       val is_absolute = (Portable.String.ordof(p,0) 
                          = Portable.String.ordof(slash,0))
   in
   case (Lib.words2 slash p)
     of [] => raise THEORY_OPS_ERR{function = "normalize_path",
                    message = "empty string can not be interpreted as a path"}
      | [s] => ""
      | slist => ((if is_absolute then slash else "")
                  ^Lib.itlist (fn s => fn S => (s^slash^S)) 
                            (Lib.fst(Lib.front_last slist)) "")
   end;

         
(*****************************************************************************
 * Takes a path name and returns the theory found there. Some redundancy in
 * consistency checking in Theory_io, but that's modularity for you. The
 * uses to which "get_theory_from_disk" is put (from the uses of
 * grab_ances_theory) don't seem to be speed-critical. It seems stupid to 
 * re-get the holsig, since we know that all the constants from it are already
 * in the symtab. We have to re-get it because the symtab is unstructured
 * wrt theories: it would take a sweep of the symbol table to get all the
 * info for a theory. <Later comment: maybe that's OK - it's apt to be faster
 * than going to disk.
 *
 *****************************************************************************)
fun get_theory_from_disk str : Theory_data.theory =
   let val path = !Globals.theory_path
       val {data=hsig,path=thms_path} = Theory_io.get_hol_sig_by_name path str
       val thms_path' = normalize_path (thms_path,str)
       val thyid = #thid (Theory_io.dest_hol_sig hsig)
       val {data=thms, ...} = Theory_io.get_thms [thms_path'] thyid
   in Theory_io.mk_theory hsig thms
   end handle (e as Exception.HOL_ERR _) => raise e
            | _ => raise THEORY_OPS_ERR{function = "get_theory_from_disk",
                                  message = "unable to read theory from disk"};


(****************************************************************************
 * Gets the named theory. Looks first to see if it is the current theory. 
 * If not, it checks the cache for it. If it's not there, it attempts to 
 * get it from disk. If it's on disk, it gets put in the cache, before being 
 * returned as a value. The heuristic used (in theory.sml) is that, if any 
 * part of a theory is requested, then the whole theory is brought in.
 ****************************************************************************)
fun grab_ances_theory "" = raise THEORY_OPS_ERR{function = "grab_ances_theory",
			         message = "theory name can't be null string"}
  | grab_ances_theory thry_str =
      if ((thry_str = current_theory_name()) orelse (thry_str = "-"))
      then Theory_data.the_current_theory()
      else if (Theory_graph.is_ancestor thry_str)
           then Theory_cache.get_object_from_cache thry_str
                handle (Exception.HOL_ERR _) => 
                  let val thry = get_theory_from_disk thry_str
                      val _ = Theory_cache.add_object_to_cache thry
                  in thry 
                  end
           else raise THEORY_OPS_ERR{function = "grab_ances_theory",
                    message = Lib.quote thry_str^" is not an ancestor theory"};

(* Not for casual use, as can wreck soundness. *)
fun perform_atomic_theory_op (f:unit -> 'a) =
   let val g = Theory_graph.graph_copy()
       val ty_st = Term.Type.symtab_copy()
       val tm_st = Term.symtab_copy()
       val ct = Theory_data.the_current_theory()
   in
   f() handle e => ( Theory_graph.replace_graph g;
                     Term.Type.replace_symtab ty_st;
                     Term.replace_symtab tm_st;
                     Theory_data.make_current ct;
                     raise e )
   end;
   

(****************************************************************************
 * When one does a "load_theory" or "extend_theory", the target theory's 
 * signature is loaded into the symtab, and loading recurses on its parents
 * until the theory being loaded is equal to one that has already been loaded 
 * or is the the current theory at the time of the call to 
 * {load,extend}_theory. The reference "found_terminus" is set whenever the 
 * original theory is encountered in the recursion. It's an error if the
 * original theory is never encountered. 
 *
 * When one does a "new_parent", the new_parent and, recursively, its 
 * ancestors are loaded into the symtab. This case differs from that of
 * {load,extend}_theory in that there is no terminus that must be found.
 * Instead, the recursion terminates when the frontier of the existing
 * theory graph is encountered (and is found to be consistent with the
 * newly-built sub-graph!).
 *
 * Note: in the test
 *
 *   if (theory_id_eq (thid,p) andalso check p)
 *
 * the first test seems to be always "true" because of unique ids. A re-think
 * is probably needed, if this is true.
 ****************************************************************************)

fun install_parents {done_test,check} = 
let fun install plist =
      (Lib.rev_itlist 
         (fn p => fn _ =>
           if (Theory_graph.node_in_graph p)
           then done_test p
           else let val {data=psig,...} = Theory_io.get_hol_sig_by_uid 
                                                  (!Globals.theory_path) p
                    val {thid,parents,...} = Theory_io.dest_hol_sig psig
                in if (theory_id_eq (thid,p) andalso check p)
                   then ( install_hol_sig psig;
                          Theory_graph.add_node thid parents;
                          install parents;
                        ())
                   else raise THEORY_OPS_ERR{function = "install_parents",
                    message = "attempt to construct inconsistent theory graph"}
                end) plist ()
         ;
         plist)
in
  install
end;




(**************************************************************************
 * Checks, done by {load,extend}_theory on the hol_sig of the theory
 * to be loaded/extended.
 * 
 *     1. Check that theory not in graph
 *     2. Load constants into symtab
 *     3. Add theory to graph. The parents of the theory are associated
 *        with it in the graph.
 *     4. Return parents for the call to install.
 *************************************************************************)
fun goto_theory str terminus_id =
   let val path = !Globals.theory_path
       val {data=hsig,path=hsig_path} = Theory_io.get_hol_sig_by_name path str
       val hsig_path' = normalize_path (hsig_path,str)
       val {thid,parents,...} = Theory_io.dest_hol_sig hsig
       val _ = if (Theory_graph.node_in_graph thid)
               then raise THEORY_OPS_ERR{function = "goto_theory",
                  message = "attempt to install node already in theory graph."}
               else ()
       val _ = install_hol_sig hsig
       val _ = Theory_graph.add_node thid parents
       val found_terminus = ref false
       fun done_test p = if (theory_id_eq (p,terminus_id))
                         then found_terminus := true
                         else ()
   in
     (case (install_parents {done_test=done_test,check = fn _ => true} parents)
        of [] => ()
         | _ => if (!found_terminus)
                then ()
                else raise THEORY_OPS_ERR{function = "goto_theory",
                                    message="cannot load/extend given theory"})
     ;
     Theory_io.mk_theory hsig (#data(Theory_io.get_thms [hsig_path'] thid))
   end;



(****************************************************************************
 * Checks, done by new_parent on the holsig corresponding to the new 
 * parent.
 * 
 *     0. If proposed parent is already in graph, you are done. Signal this
 *        by returning empty list. "install_parents" will take this 
 *        argument and not do anything.
 * Otherwise,       
 *     1. Load signature into symtab
 *     2. Add theory_id to graph. The parents of the theory_id are associated
 *        with it in the graph.
 *     3. Return parents (for call to install_parents).
 *     4. Call install_parents. We must check that the name of the current
 *        theory is not the name of any of the new parents being brought
 *        in, hence the "check" function.
 ****************************************************************************)
fun install_new_parent (ct,hsig) =
   let val {thid,parents,...} = Theory_io.dest_hol_sig hsig
       val pnts = if (Theory_graph.node_in_graph thid)
                  then []
                  else ( install_hol_sig hsig;
                         Theory_graph.add_node thid parents;
                         parents )
       fun check p = (ct <> Theory_data.theory_id_name p)
   in perform_atomic_theory_op 
       (fn () => install_parents{done_test = fn _ => (),check = check} pnts)
      ;
      ()
   end;


(**************************************************************************
 * Needs to be called to write the contents of a theory to disk. Does not
 * change any contents of the theory. The "draft_mode" is not altered. 
 * Consistent_with_disk is initially false, and only becomes true when
 * export_theory is called, or after a {load,extend}_theory.
 **************************************************************************)
fun export_theory() = 
   if (Theory_data.theory_consistent_with_disk(the_current_theory()))
   then Lib.say ("\nTheory "^Lib.quote(current_theory_name())^" already \
                    \consistent with disk, hence not exported.\n")
   else ( Theory_io.put_theory_to_disk (Theory_data.the_current_theory());
          Theory_data.make_current
           (Theory_data.set_consistency_with_disk true (the_current_theory()));
          Lib.say ("\nTheory "^Lib.quote(current_theory_name())^" exported.\n"));


(*************************************************************************
 * It can happen that a "system" theory gets read in, a theorem gets
 * saved in it, and then "export_theory" or "close" is called. The theory
 * will get dumped to the file prefixed by the first path name in the
 * theory_path, if the file is writable. This gives a scheme for users to
 * get private copies of system theories, which is OK, but can be
 * confusing. The moral: always consider the theory_path in matters of
 * theory i/o.
 *************************************************************************)

(* From Elsa Gunter. *)
fun close () = ( export_theory(); Portable.exit () );


end; (* THEORY_OPS *)
