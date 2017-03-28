structure Cache : Cache_sig =
struct

  type term = CoreHol.Term.term
  type thm = CoreHol.Thm.thm
  type conv = Abbrev.conv;

open Lib liteLib;
open LiteLib Trace Termtable;

infix <<;  (* A subsetof B *)
fun x << y = all (C mem y) x;

type table = (term list * thm option) list termtable
type cache = table ref;

fun CACHE (filt,conv) =
  let exception FIRST
      fun first p [] = raise FIRST
        | first p (h::t) = if p h then h else first p t;        
      val cache = (ref (mk_termtable (100,Subscript)): cache);
      fun cache_proc thms tm =
        let val _ = if (filt tm) then () 
                    else failwith "CACHE_CCONV: not applicable"
            val prevs = termtable_find (!cache) ([],tm) handle Subscript => []
            val curr = flatten (map CoreHol.Thm.hyp thms)
            fun ok (prev,SOME thm) = prev << curr
              | ok (prev,NONE) = curr << prev
        in (case (snd (first ok prevs)) of
              SOME x => (trace(1,PRODUCE(tm,"cache hit!",x)); x) 
            | NONE => failwith "cache hit was failure")
          handle FIRST => 
          let val thm = conv thms tm
              handle e => (termtable_insert (!cache) (([],tm),(curr,NONE)::prevs);
                           raise e)
          in (termtable_insert (!cache) (([],tm),(curr,SOME thm)::prevs); thm)
          end
        end;
  in (cache_proc, cache)
  end;
  
fun clear_cache cache = (cache := (mk_termtable (100,Subscript):table));

end (* struct *)
