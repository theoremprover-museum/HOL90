new_theory "test";

val {desc,induction_thm} =
   let val N = --`N (R:num->num->bool) : num->num->bool`--
   in 
   new_inductive_definition
      {name="N", 
       fixity=Prefix,
       patt = (--`^N n m`--, [--`R:num->num->bool`--]),
       rules = 
        [{hypotheses=[],side_conditions=[],
          conclusion = --`^N 0 m`--},
          {hypotheses=[--`^N n m`--, --`R (m:num) (n:num):bool`--], 
           side_conditions=[],
           conclusion = --`^N (n+2) k`--}]}
   end;

let val RTC = --`RTC:('a->'a->bool)->'a->'a->bool`--
in
new_inductive_definition{name="RTC",fixity=Prefix,
  patt = (--`^RTC R x y`--, [--`R:'a->'a->bool`--]),
  rules =[
   {hypotheses=[], side_conditions=[(--`R (x:'a) (y:'a):bool`--)],
   (* ----------------------------------------------------------*)  
                  conclusion = --`^RTC R x y`--},
   
             {hypotheses=[], side_conditions=[],
            (*------------------------------- *) 
               conclusion = (--`^RTC R x x`--)},
   
   {hypotheses=[ (--`^RTC R z y`--) , (--`(R:'a->'a->bool) x z`--) ],
   side_conditions=[],
   (*------------------------------------------------------------ *)
               conclusion = (--`^RTC R x y`--)}]}
end;

let val RTC = --`RTC1:('a->'a->bool)->'a->'a->bool`-- 
in
new_inductive_definition{name="RTC1",fixity=Prefix,
   patt=(--`^RTC R x y`--,  [--`R:'a->'a->bool`--]),
   rules=[
    {               hypotheses=[],
     side_conditions=[(--`R (x:'a) (y:'a):bool`--)],
     (* -------------------------------------------- *)  
             conclusion =  (--`^RTC R x y`--)},

    {hypotheses=[],side_conditions=[],
    (*------------------------------- *) 
     conclusion = (--`^RTC R x x`--) },

    {hypotheses=[ (--`^RTC R z y`--), (--`(R:'a->'a->bool) x z`--)],
    (*-------------------------------------------------------------*)
             conclusion = (--`^RTC R x y`--),            side_conditions=[]}]}
end;


let val RTC = --`RTC2:('a->'a->bool)->'a->'a->bool`-- 
in
new_inductive_definition{name="RTC2",fixity=Prefix,
    patt =(--`^RTC R x y`--, [--`R:'a->'a->bool`--]),
    rules=[
     {hypotheses=[],side_conditions=[--`R (x:'a) (y:'a):bool`--],
     (* ------------------------------------------------------ *)
      conclusion =     (--`^RTC R x y`--)                       },

     {hypotheses=[],           side_conditions=[],
      (*------------------------------------------ *)
      conclusion =     (--`^RTC R x x`--)},

    {hypotheses=[(--`^RTC R x z`--) , (--`^RTC R z y`--)  ],side_conditions=[],
    (*----------------------------------------------------*)
     conclusion=       (--`^RTC R x y`--)                          }]}
end;


let val ODD = --`ODD_REL:num->num->bool`--
in
new_inductive_definition{name="ODD_REL",fixity=Prefix,
  patt=(--`^ODD n m`--, []),
  rules=[
   {hypotheses=[],side_conditions=[(--`T /\ F`--)],
  (*--------------------------------------------- *)
    conclusion=      (--`^ODD 2 3`--)},

    {hypotheses=[(--`^ODD n m`--), (--`(1=2) /\ (3=4)`--), (--`^ODD 2 3`--)],
   (*-----------------------------------------------------------------------*)
     conclusion =             (--`^ODD (n+m) m`--)                          ,
     side_conditions=[]                                                     }]}
end;



