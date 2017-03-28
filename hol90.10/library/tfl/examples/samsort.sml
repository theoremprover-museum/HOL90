(*---------------------------------------------------------------------------
 *
 *               SMOOTH APPLICATIVE MERGE SORT
 *
 * from Richard O'Keefe, as found in Paulson's ML book 
 *---------------------------------------------------------------------------*)


cons_path "../" theory_path;
new_theory"samsort" handle _ => ();
map new_parent ["kls_list", "sorting"];
(* map add_theory_to_sml["list", "kls_list", "sorting"]; *)


(*---------------------------------------------------------------------------
 *     Merge two lists using R.
 *---------------------------------------------------------------------------*)
val merge_def = 
    function  `(merge(R, [], x) = (x:'a list)) /\
               (merge(R, h::t, []) = h::t)     /\
               (merge(R, h1::t1, h2::t2) = 
                 (R h1 h2 => h1::merge(R,t1,h2::t2)
                           | h2::merge(R,h1::t1,t2)))`;


(*---------------------------------------------------------------------------
 *     Reverse a list.
 *---------------------------------------------------------------------------*)
val rev_def = function  `(rev([]:'a list, rl) = rl)     /\
                         (rev(h::t, rl) = rev(t, h::rl))`;

val reverse_def = 
    Q.new_definition("reverse", 
                     `reverse (L:'a list) = rev(L,[])`);


(*---------------------------------------------------------------------------
 *     Merge adjacent lists.
 *---------------------------------------------------------------------------*)
val mergepairs_def =
   function  `(mergepairs(R,[],k) = [])           /\
              (mergepairs(R,[l],k) = [l:'a list]) /\
              (mergepairs(R,l1::l2::rst, k) =
               ((k MOD 2 = 1) => (l1::l2::rst)
                              |  mergepairs(R,merge(R,l1,l2)::rst, k DIV 2)))`;


(*---------------------------------------------------------------------------
 *     Unbundled bottom-up merge sort 
 *---------------------------------------------------------------------------*)
val msort_def = 
    function
    `(msort(R, ([]:'a list), ll, k) = HD(mergepairs(R,ll,0))) /\
     (msort(R, h::t,ll,k) = msort(R, t, mergepairs(R,[h]::ll, k+1), k+1))`;


(*---------------------------------------------------------------------------
 *     Break the next Rchain off from the list. 
 *---------------------------------------------------------------------------*)
val nextrun_def =
     function  `(nextrun(R, run, []) = (reverse run:'a list, [])) /\
                (nextrun(R, run, h::t) =
                   (R h (HD run) => (reverse run, h::t)
                                 |  nextrun(R, h::run, t)))`;


(*---------------------------------------------------------------------------
 *     Unbundled "smooth" bottom-up merge sort.
 *---------------------------------------------------------------------------*)
val samsortl_def = 
       function  `(samsortl(R,[],ll,k):'a list = HD(mergepairs(R,ll,0))) /\
                  (samsortl(R,h::t,ll,k) =
                     let (run,rst) = nextrun(R,[h],t)
                     in
                     samsortl(R, rst, mergepairs(R,run::ll, k+1), k+1))`;


(*---------------------------------------------------------------------------
 *     Bundled bottom-up smooth merge sort.
 *---------------------------------------------------------------------------*)
val samsort_def = 
   Q.new_definition("samsort",
                    `samsort(R, alist):'a list = samsortl(R,alist,[],0)`);



(* Now all we have to do is prove termination and properties! *)
