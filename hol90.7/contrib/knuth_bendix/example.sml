load_library{lib = find_library"knuth_bendix", 
             theory = "knuth_bendix_examples"};

(* Install some constants in the signature *)

(* Product *)
val _ = Psyntax.new_infix("#", ==`:'a -> 'a -> 'a`==, 120);

(* Unit *)
val _ = Psyntax.new_constant("One",==`:'a`==);
val _ = Psyntax.new_constant("Id",==`:'a`==);

(* Inverse *)
val _ = Psyntax.new_constant("Inv",==`:'a->'a`==);
val _ = Psyntax.new_constant("Flip",==`:'a->'a`==);

(* Misc. *)
val _ = Psyntax.new_constant("Foo",==`:'a->'a`==);
val _ = Psyntax.new_constant("Bar",==`:'a->'a`==);

fun mk_const(s,qtm) = Dsyntax.mk_const{Name = s, Ty = Parse.type_parser qtm};
fun mk_ax(s,qtm) = Theory.new_open_axiom(s, Parse.term_parser qtm);

(* bind some constants to ML identifiers *)
val Mult = mk_const("#",  `:'a -> 'a -> 'a`);
val One  = mk_const("One",`:'a`);
val Inv  = mk_const("Inv",`:'a -> 'a`);

val Flip = mk_const("Flip",`:'a -> 'a`);
val Foo  = mk_const("Foo", `:'a -> 'a`);
val Bar  = mk_const("Bar", `:'a -> 'a`);
val Id   = mk_const("Id",  `:'a`);

(* Declare some axioms *)

val e1  =  mk_ax("e1",  `One # x:'a = x`);
val e2  =  mk_ax("e2",  `(Inv x) # x:'a = One`);
val e3  =  mk_ax("e3",  `(x # y) # z:'a = x # y # z`);

val e4  =  mk_ax("e4",  `x # One:'a = x`);
val e5  =  mk_ax("e5",  `x # (Inv x):'a = One`);
val e6  =  mk_ax("e6",  `(Inv x) # (x # y):'a = y`);
val e7  =  mk_ax("e7",  `Id # x:'a = x`);
val e8  =  mk_ax("e8",  `(Flip x) # x:'a = Id`);
val e9  =  mk_ax("e9",  `(x # y) # (y # z):'a = y`);
val e10 =  mk_ax("e10", `(x # x) # x:'a = Foo x`);
val e11 =  mk_ax("e11", `x # (x # x):'a = Bar x`);
val e12 =  mk_ax("e12", `Bar x # y:'a = x # y`);

close_theory();

val tmp = !System.Control.interp;
System.Control.interp := false;

(* Define some orderings *)
fun status tm = (tm = Mult);

(* Inv > Mult > One *)
fun Inv_Mult_One x y = 
   if (x = y)
   then false 
   else (x = Inv) orelse
        ((x = Mult) andalso (y = One));

(* Flip > Inv > Mult > Id > One *)
fun Flip_Inv_Mult_Id_One x y =
   if (x = y)
   then false
   else ((x = Mult) andalso ((y = One) orelse (y = Id)))
        orelse
        ((x = Id) andalso (y = One))
        orelse
        (x = Flip) 
        orelse
        ((x = Inv) andalso (not (y = Flip)));

(* Ordering for example sixteen and seventeen
 *
 * Mult > Foo andalso Mult > Bar
 ********************************************************)
fun o16 x y =
   if (x = y)
   then false 
   else ((x = Mult) andalso ((y = Foo) orelse (y = Bar)));


(* Examples from Knuth&Bendix paper *)

(* Example 1, groups  *)
val ex1 = [e1,e2,e3];

(* Example 3 *)
val ex3 = [e4,e5,e3];

(* Example 4 *)
val ex4 = [e6];

(* Example 5  tests generation of critical pairs *)
val ex5a = [ e3, e1, e7, e2, e8 ];

(* Example 5  *)
val ex5b = [e1,e7,e2,e8,e3];

(* Example 6, central groupoids 1 *)
val ex6 = [e9];

(* Example 12, (l,r) systems *)
val ex12 = [ e1,e5,e3];

(* Example 16, central groupoids 2 *)
val ex16 = [ e9, e10, e11, e12 ];

(* Example 17, central groupoids 3 *)
val ex17 = [ e9, e10, e11 ];

val (test1, test3, test4, test5a, test5b, test6, test12, test16, test17) =
   let fun nl() = output(std_out,"\n")
       fun show_list _ [] =  output(std_out, "none\n") |
           show_list pfun alist = 
            ( output(std_out, "\n");  map pfun alist;  output(std_out,"\n"))

       fun test order eset () = 
          ( output(std_out, "Equations:\n");
            show_list (fn (th:thm) => (print_thm th; nl()))  eset; 
            nl();
            output(std_out,"Rewrite Rules:");
            nl();
            show_list (fn (th:thm) => (print_thm th;nl()))
                      (KB.kb (KB_order.rpos status order) eset);
            ())
   in
   (test Inv_Mult_One ex1,
    test Inv_Mult_One ex3,
    test Inv_Mult_One ex4,
    test Flip_Inv_Mult_Id_One ex5a,
    test Flip_Inv_Mult_Id_One ex5b,
    test Inv_Mult_One ex6,
    test Inv_Mult_One ex12,
    test o16 ex16,
    test o16 ex17)
   end;


fun timer f =
   let open System.Timer
       val start = start_timer ()
       val _ = f()
       val non_gc_time = check_timer start
       val gc_time = check_timer_gc start
       val total_time = add_time(non_gc_time,gc_time)
   in
     print (makestring total_time);
     print "\n"
   end;

(* Execute tests individually *)

(*
timer test1;

timer test3;

timer test4;

timer test5a;

timer test5b;

timer test6;

timer test12;

timer test16;

timer test17;
*)



(* Execute tests collectively *)
local
fun test_all() = 
  ( test1();
    test3();
    test4();
    test5a();
    test5b();
    test6();
    test12();
    test16();
    test17())
in
fun time_test_all() = timer test_all
end;

System.Control.interp := tmp;
