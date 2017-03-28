(* File: MLinitial_bindings.sml *)

(* functions that define the initial basis *)

(* composition: fun (F o G) x = F (G x)    or, in basic ML
   val o = fn {1 = F, 2 = G} => (fn x => F (G x))  
   NOTE: I'm using "comp" instead of "o" since o is already defined as 
   a constant (this is the same problem encountered when trying to define
   initial_varenv_data) *)

val comp_def =
--`VALdec
(PLAIN1valbind 
 (ATPATpat (VARatpat (VAR "comp")))
 (FNexp (MATCH1 (MRULE 
		 (ATPATpat (RECORDatpat (SOME
					 (PATROW
					  (LABEL "1")
					  (ATPATpat (VARatpat (VAR "F")))
					  (SOME
					   (PATROW
					    (LABEL "2")
					    (ATPATpat (VARatpat (VAR "G")))
					    NONE))))))

		 (FNexp (MATCH1 (MRULE
				 (ATPATpat (VARatpat (VAR "x")))
				 (APPexp
				  (ATEXPexp (VARatexp (BASE (VAR "F"))))
				  (PARatexp (APPexp
					     (ATEXPexp (VARatexp
                                                        (BASE (VAR "G"))))
					     (VARatexp
                                              (BASE (VAR "x")))))))))))))`--;

(* append: fun nil @ M = M | (x::L) @ M = x :: (L @ M)     or
   val rec @ = fn {1 = nil, 2 = M} => M
                | {1 = :: {1 = x, 2 = L}, 2 = M} =>
		      ::{1 = x, 2 = @ {1 = L, 2 = M}}  *)

val append_match =
--`(MATCH
    (MRULE
     (ATPATpat
      (RECORDatpat
       (SOME (PATROW (LABEL "1") (ATPATpat (CONatpat (BASE (CON "nil"))))
	      (SOME
	       (PATROW (LABEL "2") (ATPATpat (VARatpat (VAR "M"))) NONE))))))
     (ATEXPexp (VARatexp (BASE (VAR "M")))))
    (SOME
     (MATCH
      (MRULE
       (ATPATpat
	(RECORDatpat
	 (SOME
	  (PATROW (LABEL "1")
	   (CONpat
	    (BASE (CON "::"))
	    (RECORDatpat
	     (SOME
	      (PATROW (LABEL "1") (ATPATpat (VARatpat (VAR "x")))
	       (SOME
		(PATROW (LABEL "2") (ATPATpat (VARatpat (VAR "L"))) NONE))))))
	   (SOME
	    (PATROW (LABEL "2") (ATPATpat (VARatpat (VAR "M"))) NONE))))))
       (APPexp
	(ATEXPexp (CONatexp (BASE (CON "::"))))
	(RECORDatexp
	 (SOME
	  (EXPROW (LABEL "1") (ATEXPexp (VARatexp (BASE (VAR "x"))))
	   (SOME
	    (EXPROW (LABEL "2")
	     (APPexp
	      (ATEXPexp (VARatexp (BASE (VAR "@"))))
	      (RECORDatexp
	       (SOME
		(EXPROW (LABEL "1") (ATEXPexp (VARatexp (BASE (VAR "L"))))
		 (SOME
		  (EXPROW
		   (LABEL "2")
		   (ATEXPexp (VARatexp (BASE (VAR "M"))))
		   NONE))))))
	     NONE)))))))
      NONE)))`--;

val append_def =
--`VALdec
(RECvalbind
 (PLAIN1valbind
  (ATPATpat (VARatpat (VAR "@")))
  (FNexp ^append_match)))`--;


(* string concatenation: fun s ^ s' = implode((explode s) @ (explode s'))  or
   val ^ = fn {1 = s, s = s'} => implode (@ {1 = explode s, 2 = explode s'}) 
   NOTE: I'm using "cat" below instead of "^" as ^ is the antiquote char *)

val cat_def =
--`VALdec
(PLAINvalbind 
 (ATPATpat (VARatpat (VAR "cat")))
 (FNexp (MATCH (MRULE
		 (ATPATpat
		  (RECORDatpat
		   (SOME(PATROW (LABEL "1") (ATPATpat (VARatpat (VAR "nil")))
			 (SOME(PATROW (LABEL "2")
			       (ATPATpat (VARatpat (VAR "M")))
			       NONE))))))
		 (APPexp
		  (ATEXPexp (VARatexp (BASE (VAR "@"))))
		  (RECORDatexp
		   (SOME
		   (EXPROW
		    (LABEL "1")
		    (APPexp
		     (ATEXPexp (VARatexp (BASE (VAR "explode"))))
		     (VARatexp (BASE (VAR "s"))))
		    (SOME(EXPROW 
		     (LABEL "2")
		     (APPexp
		      (ATEXPexp (VARatexp (BASE (VAR "explode"))))
		      (VARatexp (BASE (VAR "s'")))) NONE)))))))
	 NONE)) NONE)`--;

(* map: map F nil = nil | map F (x :: L) = (F x)::(map F L)  or
   val map = fn F => fn nil => nil
		      | :: {1 = x, 2 = L} => 
			    ::{1 = F x, 2 = map F L}
   NOTE: the basic ML version given above is not the one the derived form
   would translate to! *)

val map_def =
--`VALdec
(RECvalbind
 (PLAINvalbind
  (ATPATpat (VARatpat (VAR "map")))
  (FNexp (MATCH
	  (MRULE
	   (ATPATpat (VARatpat (VAR "F")))
	   (FNexp
	    (MATCH
	     (MRULE
	      (ATPATpat (CONatpat (BASE (CON "nil"))))
	      (ATEXPexp (CONatexp (BASE (CON "nil")))))
	     (SOME(MATCH
	      (MRULE
	       (CONpat
		(BASE (CON "::"))
		(RECORDatpat
		 (SOME(PATROW (LABEL "1") (ATPATpat (VARatpat (VAR "x")))
		       (SOME(PATROW (LABEL "2")
			     (ATPATpat (VARatpat (VAR "L")))
			     NONE))))))
	       (APPexp
		(ATEXPexp (CONatexp (BASE (CON "::"))))
		(RECORDatexp
		 (SOME(EXPROW
		       (LABEL "1")
		       (APPexp (ATEXPexp (VARatexp (BASE (VAR "F"))))
			(VARatexp (BASE (VAR "x"))))
		       (SOME(EXPROW
			     (LABEL "2")
			     (APPexp
			      (APPexp
			       (ATEXPexp (VARatexp (BASE (VAR "F"))))
			       (VARatexp (BASE (VAR "x"))))
			      (VARatexp (BASE (VAR "L"))))
			     NONE)))))))
		   NONE))))) NONE)) NONE))`--;


(* rev: rev nil = nil | rev (x::L) = (rev L) @ [x]   or
   val rec rev = fn nil => nil
		  | ::{1 = x, 2 = L} => @ {1 = rev L, 2 = ::{1 = x, 2 = nil}}
*)

val rev_def =
--`VALdec
(RECvalbind
 (PLAINvalbind
  (ATPATpat (VARatpat (VAR "rev")))
  (FNexp
   (MATCH
    (MRULE
     (ATPATpat (CONatpat (BASE (CON "nil"))))
     (ATEXPexp (CONatexp (BASE (CON "nil")))))
    (SOME
     (MATCH
      (MRULE
       (CONpat (BASE (CON "::"))
	(RECORDatpat
	 (SOME
	  (PATROW (LABEL "1") (ATPATpat (VARatpat (VAR "x")))
	   (SOME
	    (PATROW (LABEL "2") (ATPATpat (VARatpat (VAR "L")))
	     NONE))))))
       (APPexp
	(ATEXPexp (VARatexp (BASE (VAR "@"))))
	(RECORDatexp
	 (SOME
	  (EXPROW (LABEL "1")
	   (APPexp 
	    (ATEXPexp (VARatexp (BASE (VAR "rev"))))
	    (VARatexp (BASE (VAR "L"))))
	   (SOME
	    (EXPROW (LABEL "2")
	     (APPexp
	      (ATEXPexp (CONatexp (BASE (CON "::"))))
	      (RECORDatexp
	       (SOME
		(EXPROW (LABEL "1")
		 (ATEXPexp (VARatexp (BASE (VAR "x"))))
		 (SOME
		  (EXPROW (LABEL "2")
		   (ATEXPexp (CONatexp (BASE (CON "nil"))))
		   NONE))))))
	     NONE)))))))
     NONE))))
  NONE))`--;

(* not: fun not true = false | not false = true     or
   val not = fn true => false | false => true *)

val not_def =
--`VALdec
(PLAINvalbind
 (ATPATpat (VARatpat (VAR "not")))
 (FNexp (MATCH
	 (MRULE
	  (ATPATpat (CONatpat (BASE (CON "true"))))
	  (ATEXPexp (CONatexp (BASE (CON "false")))))
	 (SOME(MATCH1
	  (MRULE
	   (ATPATpat (CONatpat (BASE (CON "false"))))
	   (ATEXPexp (CONatexp (BASE (CON "true")))))))))
 NONE)`--;

(* dereference: fun ! (ref x) = x     or
   val ! = fn ref x => x    *)

val deref_def =
--`VALdec
(PLAINvalbind
 (ATPATpat (VARatpat (VAR "!")))
 (FNexp (MATCH
	 (MRULE
	  (CONpat (BASE (CON "ref")) (VARatpat (VAR "x")))
	  (ATEXPexp (VARatexp (BASE (VAR "x")))))
	 NONE))
 NONE)`--;

(* to use the above declarations, you need to include them with your
   declarations like so:

val program = 
--`SEQdec ^comp_def
    (SEQdec ^append_def
     (SEQdec ^cat_def
      (SEQdec ^map_def
       (SEQdec ^rev_def
	(SEQdec ^not_def
	 (SEQdec ^deref_def
	  your_declaration_goes_here))))))`--
*)


