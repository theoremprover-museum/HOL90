(* ===================================================================== *)
(* FILE          : library.sml                                           *)
(* DESCRIPTION   : Provides functionality for HOL libraries.             *)
(*                                                                       *)
(* AUTHOR        : Konrad Slind, University of Calgary                   *)
(*                                                                       *)
(* DATE          : December 9, 1991                                      *)
(*                                                                       *)
(* Modified      : Dec 25, 1992 (kls)                                    *)
(*                 Builds on modifications made by Elsa Gunter.          *)
(*                 New library scheme: library info held in data         *)
(*                 structure instead of on a disk file. Can then write a *)
(*                 load_library function that works uniformly on the     *)
(*                 data structure.                                       *)
(*                                                                       *)
(*                 Jan 12, 1993 (kls)                                    *)
(*                 Changed to be more like theories: libraries are       *)
(*                 represented on disk, are accessible once more via a   *)
(*                 path, which is OK, since the evil of paths has been   *)
(*                 circumvented.                                         *)
(*                                                                       *)
(*                 March 23, 1993 (kls)                                  *)
(*                 Bugfix to load_library - it needs to find the theories*)
(*                 of a library wrt the "path" field of the library, not *)
(*                 the theory_path.                                      *)
(*                                                                       *)
(*                 October, 1994 (kls)                                   *)
(*                 Changed semantics of "load_library" so that given a   *)
(*                 theory name not equal to the current theory, it will  *)
(*                 always declare that theory.                           *)
(* ===================================================================== *)


(* In the following, there is a general confusion between "the" library and 
   a library. The library contains all the libraries. Unfortunately.
*)
functor LIBRARY (structure Theory : Theory_sig
                 structure Lib_io : Lib_io_sig): Library_sig = 
struct
structure Theory = Theory;
structure Lib_data = Lib_io.Lib_data


fun LIBRARY_ERR{function,message} =
        HOL_ERR{origin_structure = "Library", origin_function = function,
	        message = message}

val slash = "/";

abstype lib = Lib of {lib_id : Lib_data.lib_id,
                      doc : string,
                      path : string ref,
                      parents : lib list,
                      theories : string list,
                      code : string list,
                      help : string list,
                      loaded : string}
with

val the_current_library = ref {the_known_libs  = []:lib list,
                               the_loaded_libs = []:lib list};


fun known_libraries() = #the_known_libs(!the_current_library)
fun loaded_libraries() = #the_loaded_libs(!the_current_library)

fun lib_id (Lib{lib_id,...}) = lib_id;
fun lib_name (Lib{lib_id,...}) = Lib_data.lib_id_name lib_id;

fun lib_eq (Lib{lib_id = lib_id1,...}) (Lib{lib_id = lib_id2,...}) =
          Lib_data.lib_id_eq(lib_id1, lib_id2);

fun lib_id_assoc lid =
   let fun assc [] = NONE
         | assc ((lib as Lib{lib_id,...})::rst) = 
              if (Lib_data.lib_id_eq(lib_id,lid))
              then (SOME lib)
              else assc rst
   in assc
   end;

fun lib_str_assoc str =
   let fun assc [] = NONE
         | assc ((lib as Lib{lib_id,...})::rst) = 
              if (str = Lib_data.lib_id_name lib_id)
              then (SOME lib)
              else assc rst
   in assc
   end;

fun is_loaded (Lib{lib_id,...}) = 
   case (lib_id_assoc lib_id (loaded_libraries()))
     of NONE => false
      | _ => true;


fun known_library_names() = map lib_name (known_libraries())
fun is_known s = mem s (known_library_names());

fun perform_atomic_library_op (f:unit->unit) =
   let val hp = !Globals.help_path
       val thp = !Globals.theory_path
       val clib = !the_current_library
   in Theory.perform_atomic_theory_op f
      handle e => (Globals.help_path := hp; 
                   Globals.theory_path := thp;
                   the_current_library := clib;
                   raise e)
   end;
                  

fun lib_theory_path prefix = prefix^"theories/"^Globals.theory_file_type^slash;


fun dest_library (Lib{lib_id,doc,path,parents,theories,code,help,...}) =
    {name = Lib_data.lib_id_name lib_id,
     doc = doc, path = !path, parents = parents, 
     theories = theories,code=code,help=help}


(*------------------------------------------------------------------------*)
(* So what does new_library do?                                           *)
(*                                                                        *)
(*    0. Appends the theories to the theory path                          *)
(*    1. externalizes the library in a ".hol_lib" file. Written at the    *)
(*       hd of library_path.                                              *)
(*    2. returns the library                                              *)
(*------------------------------------------------------------------------*)
val std_fn = fn () => ()
val loaded_cell = ref std_fn


fun new_library {name,doc,path,parents,theories,code,help,loaded} =
   let val new_lib_id = Lib_data.new_lib_id name
       val extern_lib = Lib_data.mk_lib_data
                          {lib_id = new_lib_id,doc = doc,path = path,
                           parents = map lib_id parents,
                           theories = theories,code = code,
                           help = help,loaded = loaded}
       val _ = Lib_io.write_lib_to_disk(hd(!Globals.library_path), extern_lib)
       val new_lib = Lib {lib_id = new_lib_id,doc = doc,path = ref path,
                          parents = parents,theories = theories,code = code,
                          help = help,loaded = loaded}
       val {the_known_libs, the_loaded_libs} = !the_current_library
   in
    case theories of [] => ()
    | _ => Lib.append_path (lib_theory_path path) Globals.theory_path;
    the_current_library := {the_known_libs = new_lib::the_known_libs,
                            the_loaded_libs = the_loaded_libs};
    Lib.say("\nThe library "^quote name^" has been declared and exported.\n");
    new_lib
   end;


(* If we come to add a new parent and it is not already a parent (or 
 * the current theory) and we are already in draft mode, make it a new 
 * parent; otherwise fail.
 *************************************************************************)
fun add_new_parent ances sprefix s =
     if Lib.mem s ances
     then ()
     else if Theory.draft_mode()
        then Theory.new_parent (sprefix^s)
               handle HOL_ERR{origin_structure,origin_function,message} =>
             raise LIBRARY_ERR{function="load_library.add_new_parent",
                  message = origin_structure^"."^origin_function^": "^message}
        else raise LIBRARY_ERR{function="load_library.add_new_parent",
               message = Lib.quote s^" is not a parent theory, and can not be \
                \ added as a parent theory because we are not in draft mode."}

(* Documentation : see doc/library.html. *)
(*----------------------------------------------------------------------*)
(* So what does load_library do?                                        *)
(*                                                                      *)
(*   1. declares new theory if necessary                                *)
(*   2. loads parent libraries                                          *)
(*   3. does new_parent-ing, if necessary                               *)
(*   4. import code, binary if possible                                 *)
(*   5. adjust help path                                                *)
(*   6. apply loaded                                                    *)
(*   7. updates "loaded_libs"                                           *)
(*   8. If any exceptions raised, clean up as best as possible.         *)
(*----------------------------------------------------------------------*)

fun prim_load_library code_loader 
         {lib as Lib{lib_id,doc,path,parents,theories,code,help,loaded},
          theory} =
   let val name = Lib_data.lib_id_name lib_id
       val quoted_name = "library "^Lib.quote name
   in
   if (is_loaded lib)
   then Lib.say ("\nThe "^quoted_name^" is already loaded.\n")
   else 
let fun f() =
   let val theory = if (theory = "-") then Theory.current_theory() else theory
       val heritage = Theory.current_theory()::(Theory.ancestry"-")
       val lib_code_path = (!path)^"src/"
       val lib_help_path = (!path)^"help/"
       val lib_thy_path = lib_theory_path (!path)
       fun load_parent_libs ([],_) = ()
         | load_parent_libs (P,str) = 
           (map (fn lib => prim_load_library code_loader {lib=lib,theory=str})
                P;
              Lib.say ("\n  The parent libraries of "^quoted_name^
                       " have been loaded.\n"))
    in
    (if (theory = Theory.current_theory())
     then ()
     else Theory.new_theory theory
     ;
     load_parent_libs (parents, theory)
     ;
     case theories of [] => ()
     | L => (map (add_new_parent heritage lib_thy_path) L
             ;
             Lib.say("\n  The theories belonging to "^quoted_name^
                     " have been incorporated.\n"))
     ;
     case code of [] => ()
     | L => (map (fn s => code_loader (lib_code_path^s)) L;
             Lib.say("\n  The code of "^quoted_name^" has been loaded.\n"))
     ;
     (case help of [] => Lib.cons_path lib_help_path Globals.help_path
     | L => rev_itlist(fn p => fn _ => 
                          Lib.cons_path (lib_help_path^p)Globals.help_path)
                       L ())
     ;
     Lib.say("\n  The help path for "^quoted_name^" has been adjusted.\n")
     ;
     (* this is before the call to "loaded" because at the time of
      * dumping the final image of the system, which is done in the
      * "loaded" section of hol_lib in 3/sys_lib, hol_lib needs
      * to be thought of as loaded, otherwise we get 
      * .../library/HOL/theories/ascii put on the theory_path, but that
      * is a bogus path and bound to be confusing.
      *)
     the_current_library := {the_known_libs = known_libraries(),
                             the_loaded_libs = lib::(loaded_libraries())}
     ;
     loaded_cell := std_fn;
     Lib.eval_string("val _ = (Library.loaded_cell := ("^loaded^"))");
     (!loaded_cell) ()
     ;
     Lib.say ("\nThe "^quoted_name^" is loaded.\n"))
     end
in
 Lib.say ("\nLoading the "^quoted_name^".\n");
 perform_atomic_library_op f
end
end;


val load_library = prim_load_library Lib.compile;

(*------------------------------------------------------------------------*)
(* So what does load_library_in_place do? It does exactly the same stuff  *)
(* as load_library, but it refuses to leave its current theory.           *)
(*------------------------------------------------------------------------*)

fun load_library_in_place lib = load_library{lib = lib, theory = "-"};

(* We look for the library in known_libraries; if not there, then on disk.
 * Returns a lib suitable for loading.
 *)
fun find_library_by_id id =
   case (lib_id_assoc id (known_libraries()))
     of (SOME L) => L
      | NONE => 
        let val data = Lib_io.get_lib_by_uid (!Globals.library_path) id
            val {lib_id,doc,path,parents,theories,code,help,loaded} = 
                                Lib_data.dest_lib_data data
            val parent_libs = map find_library_by_id parents
            val _ = if (null theories)
                    then ()
                    else append_path (lib_theory_path path) Globals.theory_path
            val lib = Lib{lib_id = lib_id,doc = doc,path = ref path,
                          parents = parent_libs,theories = theories,
                          code = code,help = help,loaded = loaded}
        in the_current_library := {the_known_libs = lib::(known_libraries()),
                                   the_loaded_libs = loaded_libraries()};
           lib
        end;

fun get_library_from_disk str =
   let val data = Lib_io.get_lib_by_name (!Globals.library_path) str
       val {lib_id,doc,path,parents,theories,code,help,loaded} = 
                                Lib_data.dest_lib_data data
       val parent_libs = map find_library_by_id parents
       val _ = if (null theories)
               then ()
               else append_path (lib_theory_path path) Globals.theory_path
       val lib = Lib{lib_id = lib_id,doc = doc,path = ref path,
                     parents = parent_libs,theories = theories,
                     code = code,help = help,loaded = loaded}
   in the_current_library := {the_known_libs = lib::(known_libraries()),
                              the_loaded_libs = loaded_libraries()};
      lib
   end;

fun find_library str =
   case (lib_str_assoc str (known_libraries()))
     of (SOME L) => L
      | NONE => get_library_from_disk str;


(* Unfortunately, moving a library (maybe I should call it "new_library_path")
 * will not move the paths that were added by the library to the theory_path.
 * Maybe structured paths are the answer:
 *
 *    datatype path = Absolute of {prefix:string, name}
 *                  | ??
 ****************************************************************************)
fun move_library(Lib{path,...},new) = (path := new);

(* Ought to be a Lib.op_remove *)
fun del L =
   let fun d [] = []
         | d (a::rst) = if (lib_eq L a) then rst else a::(d rst)
   in d
   end;
 
fun delete_library L =
   if (op_mem lib_eq L (loaded_libraries()))
   then raise LIBRARY_ERR{function = "delete_library",
                 message="the library is loaded and hence can not be removed."}
   else if (exists (fn (Lib{parents,...}) => op_mem lib_eq L parents) 
                   (known_libraries()))
        then raise LIBRARY_ERR{function = "delete_library",
                 message = "the library is a parent to an existing library and\
                           \ can not be removed."}
        else the_current_library := {the_known_libs=del L (known_libraries()),
                                     the_loaded_libs = loaded_libraries()};


fun lib_help{lib = Lib{path,help,...}, topic} = 
    Help.helper (map (fn d => ((!path)^"help/"^d^slash)) help) topic;


(* Prettyprinting *)

fun pp_library ppstrm (Lib{lib_id,doc,parents,...}) =
   let val {add_string,add_break,begin_block,end_block,add_newline,...} =
                  PP.with_ppstream ppstrm
       val bbc = begin_block PP.CONSISTENT
       val bbi = begin_block PP.INCONSISTENT
       val eb = end_block
       val S = add_string 
       fun comma() = S ","
       fun lbracket() = S "["
       fun rbracket() = S "]"
       fun space() = add_break(1,0)
       val nl = add_newline
       fun pr_sml_list f L = 
          ( bbc 1;lbracket();PP.pr_list f comma space L;rbracket();eb())
   in
     bbc 0;
     S ("library name: "^Lib_data.lib_id_name lib_id);
     nl();
     bbc 0; S "description:"; space(); S doc; eb();
     nl();
     bbc 0; S "parents:"; space(); pr_sml_list (S o lib_name) parents; eb();
     nl();
     end_block ()
   end handle e => (Lib.say "Error in prettyprinting library description!";
                    raise e);
  
  
end; (* abstype *)

end; (* LIBRARY *)
