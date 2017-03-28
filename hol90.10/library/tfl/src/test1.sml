new_theory"test";
new_parent"kls_list";

fun function q =
   let val _ = counting_thms true
       val _ = reset_thm_count()
       val eqs_ind = Tfl.function q
       val {ABS,ASSUME,BETA_CONV,DISCH,INST_TYPE,MP,
            REFL,SUBST,drule,other,...} = thm_count()
   in {eqs_ind = eqs_ind, 
       thms = ABS + ASSUME + BETA_CONV + DISCH + INST_TYPE + 
              MP + REFL + SUBST + drule + other}
   end;


val nested_function = LIST_CONJ o map #1 o #extracta o 
                      Tfl.Prim.wfrec_eqns o Parse.term_parser;

val fact_cond_def = function `fact x = ((x = 0) => 1 | x * fact(x-1))`;

val fact_pattern_def = function
   `(Fact 0 = 1) /\
    (Fact (SUC x) = Fact x * SUC x)`;

val Ffact_def = function`(Ffact (SUC x) = Ffact x * SUC x)`;

val Fib_def = function
   `(Fib 0 = 1) /\
    (Fib (SUC 0) = 1) /\
    (Fib (SUC(SUC x)) = Fib x + Fib (SUC x))`;

val Ffib_def = function`(Ffib (SUC(SUC x)) = Ffib x + Fib (SUC x))`;

val ack_def = nested_function
   `(Ack (0,n) =  n+1) /\
    (Ack (SUC m,0) = Ack (m, 1)) /\
    (Ack (SUC m, SUC n) = Ack (m, Ack (SUC m, n)))`;

val map2_def = function 
  `(map2(f, ([]:'a list),(L:'b list)) = ([]:'c list)) /\
   (map2(f, CONS h t,   []) = [])                         /\
   (map2(f, CONS h1 t1, CONS h2 t2) = CONS (f h1 h2) (map2 (f, t1, t2)))`;

(* Try a different arrangement of arguments. *)
val Map2_def = function 
  `(Map2((([]:'a list),(L:'b list)), f) = ([]:'c list)) /\
   (Map2((CONS h t, []),             f) = [])           /\
   (Map2((CONS h1 t1, CONS h2 t2),   f) = CONS (f h1 h2) (Map2((t1,t2),f)))`;


val Mmap2_def = function 
  `(Mmap2((fn:'a->'b->'c), [],      []) = []) /\
   (Mmap2(fn,  CONS h1 t1, CONS h2 t2) = CONS (fn h1 h2) (Mmap2 (fn, t1,t2)))`;

val order = ty_antiq(==`:'a -> 'a -> bool`==);
val finiteRchain_def = function 
   `(finiteRchain (R:^order, []) = T) /\
    (finiteRchain (R,       [x]) = T) /\   
    (finiteRchain (R, CONS x (CONS y rst)) = R x y /\ 
                                             finiteRchain(R, CONS y rst))`;

val fin_def = function `(fin(R:^order,[x:'a]) = T)`;

val qsort_def = function 
   `(qsort(ord:^order,[]) = []) /\
    (qsort(ord, CONS (x:'a) rst) = 
      qsort(ord,filter($~ o ord x) rst)++[x]++qsort(ord,filter(ord x) rst))`;

val variant_def = function`variant(x, L) = (mem x L => variant(SUC x,L) | x)`;

val gcd_def = function
   `(gcd (0,y) = y) /\
    (gcd (SUC x, 0) = SUC x) /\
    (gcd (SUC x, SUC y) = 
        ((y <= x)     => gcd(x-y, SUC y) 
         | (*otherwise*) gcd(SUC x, y-x)))`;

val AND_def = function
   `(AND(x,[]) = x) /\
    (AND(y, CONS h t) = AND(y /\ h, t))`;

val ninety_one_eqn = nested_function
`ninety_one x = (x>100 => (x-10) | ninety_one (ninety_one (x+11)))`;

val div_def = function
   `(div(0,x) = (0,0)) /\
    (div(SUC x, y) = let (q,r) = div(x,y)
                     in y <= SUC r => (SUC q,0) 
                                   |  (q, SUC r))`;

(* Nested paired lets *)
val div_def = function
   `(Div(0,x) = (0,0)) /\
    (Div(SUC x, y) = let (q,r) = Div(x,y) in
                     let (s,t) = (x,y) 
                     in y <= SUC r => (SUC q,0) 
                                   |  (q, SUC r))`;

val qsort_def = function 
   `(Qsort(ord:^order,[]) = []) /\
    (Qsort(ord, CONS (x:'a) rst) = 
      let ((L1,L2),P) = ((filter($~ o ord x) rst,
                          filter (ord x) rst),
                       (x,rst)) in
      let (lower,upper) = ((ord,L1),(ord,L2))
      in
      Qsort lower ++[x]++ Qsort upper)`;


(* From Tobias Nipkow; "acc1" forms part of a lexer. *)
val acc1_def = 
  function`(acc1 ((f,p),([]:'a list),(s:'b),xss,zs,xs) =
                  ((xs=[]) => (xss, zs) 
                           |  acc1((f,p), zs, s, (xss++[xs]),[],[]))) /\
           (acc1((f,(p:'c)), CONS y ys, s, xss, zs, xs) = 
             let s' = s in
             let zs' = (f s' => [] | zs++[y]) in
             let xs' = (f s' => xs++zs++[y] | xs)
             in 
             acc1((f,p), ys, s', xss, zs', xs'))`;

val nested_if = function
  `(f(0,x) = (0,0)) /\ 
   (f(SUC x, y) = (y = x => (0<y => (0,0) | f(x,y)) | (x,y)))`;

val tricky = function
    `vary(x, L) = (mem x L => let x = SUC x in vary(x,L) | x)`;

val tricky1 = function
    `vary1(x, L) = (mem x L => let x = SUC x in 
                              let x = x in vary1(x,L) | x)`;

val tricky2 = function
    `vary2(x, L) = (mem x L => let (x,y) = (SUC x,x) in 
                               let (x,y) = (x,y) in vary2(x,L) | x)`;



(* Test nested lets -- auto-def will fail, since the binding to r is nested! *)
val Divide_def = nested_function
   `(Divide(0,x) = (0,0)) /\
    (Divide(SUC x, y) = let q = FST(Divide(x,y)) in
                     let r = SND(Divide(x,y))
                     in y <= SUC r => (SUC q, 0) 
                                   |  (q, SUC r))`;


(* Should fail on repeated variables. *)
val And_def = function
   `(And(x:bool,[]) = x) /\
    (And(y, CONS y t) = And(y,t))`;

