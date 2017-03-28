(* File: contrib/holML/theories/src/more_string/mk_more_string.sml *)

(* Set the path to write the theory to. *)

local
    val path = (!HOLdir)^"contrib/holML/theories/"^
	       Globals.theory_file_type^"/"
in
    val _ = theory_path := path :: (!Globals.theory_path)
end;

val _ = new_theory "more_string";

val _ = new_parent "string";

val _ = new_parent "integer";

(* string functions *)
(* All of these should probably go into the string library *)

(* bit extraction *)
val bit0_DEF = new_recursive_definition
{def =  --`bit0 (ASCII b7 b6 b5 b4 b3 b2 b1 b0) = b0`--,
 fixity = Prefix, name = "bit0_DEF", 
 rec_axiom = theorem "ascii" "ascii_Axiom"};

val bit1_DEF = new_recursive_definition
{def =  --`bit1 (ASCII b7 b6 b5 b4 b3 b2 b1 b0) = b1`--,
 fixity = Prefix, name = "bit1_DEF", 
 rec_axiom = theorem "ascii" "ascii_Axiom"};

val bit2_DEF = new_recursive_definition
{def =  --`bit2 (ASCII b7 b6 b5 b4 b3 b2 b1 b0) = b2`--,
 fixity = Prefix, name = "bit2_DEF", 
 rec_axiom = theorem "ascii" "ascii_Axiom"};

val bit3_DEF = new_recursive_definition
{def =  --`bit3 (ASCII b7 b6 b5 b4 b3 b2 b1 b0) = b3`--,
 fixity = Prefix, name = "bit3_DEF", 
 rec_axiom = theorem "ascii" "ascii_Axiom"};

val bit4_DEF = new_recursive_definition
{def =  --`bit4 (ASCII b7 b6 b5 b4 b3 b2 b1 b0) = b4`--,
 fixity = Prefix, name = "bit4_DEF", 
 rec_axiom = theorem "ascii" "ascii_Axiom"};

val bit5_DEF = new_recursive_definition
{def =  --`bit5 (ASCII b7 b6 b5 b4 b3 b2 b1 b0) = b5`--,
 fixity = Prefix, name = "bit5_DEF", 
 rec_axiom = theorem "ascii" "ascii_Axiom"};

val bit6_DEF = new_recursive_definition
{def =  --`bit6 (ASCII b7 b6 b5 b4 b3 b2 b1 b0) = b6`--,
 fixity = Prefix, name = "bit6_DEF", 
 rec_axiom = theorem "ascii" "ascii_Axiom"};

val bit7_DEF = new_recursive_definition
{def =  --`bit7 (ASCII b7 b6 b5 b4 b3 b2 b1 b0) = b7`--,
 fixity = Prefix, name = "bit7_DEF", 
 rec_axiom = theorem "ascii" "ascii_Axiom"};

(* < for ascii chars *)
val ltascii_DEF = new_recursive_definition
{def = 
 --`(ltascii (ASCII b7 b6 b5 b4 b3 b2 b1 b0) = \a2.
      (~b7 /\   bit7 a2  => T | 
      ( b7 /\ ~(bit7 a2) => F |
      (~b6 /\   bit6 a2  => T | 
      ( b6 /\ ~(bit6 a2) => F |
      (~b5 /\   bit5 a2  => T | 
      ( b5 /\ ~(bit5 a2) => F |
      (~b4 /\   bit4 a2  => T | 
      ( b4 /\ ~(bit4 a2) => F |
      (~b3 /\   bit3 a2  => T | 
      ( b3 /\ ~(bit3 a2) => F |
      (~b2 /\   bit2 a2  => T | 
      ( b2 /\ ~(bit2 a2) => F |
      (~b1 /\   bit1 a2  => T | 
      ( b1 /\ ~(bit1 a2) => F |
      (~b0 /\   bit0 a2  => T | F))))))))))))))))`--,
 fixity = Prefix, name = "ltascii_DEF", 
 rec_axiom = theorem "ascii" "ascii_Axiom"};


val ltascii_lemma = store_thm("ltascii_lemma",
(--`!b7 b6 b5 b4 b3 b2 b1 b0 c7 c6 c5 c4 c3 c2 c1 c0.
     ltascii (ASCII b7 b6 b5 b4 b3 b2 b1 b0) (ASCII c7 c6 c5 c4 c3 c2 c1 c0) =
      (~b7 /\ c7  => T | 
      ( b7 /\ ~c7 => F |
      (~b6 /\ c6  => T | 
      ( b6 /\ ~c6 => F |
      (~b5 /\ c5  => T | 
      ( b5 /\ ~c5 => F |
      (~b4 /\ c4  => T | 
      ( b4 /\ ~c4 => F |
      (~b3 /\ c3  => T | 
      ( b3 /\ ~c3 => F |
      (~b2 /\ c2  => T | 
      ( b2 /\ ~c2 => F |
      (~b1 /\ c1  => T | 
      ( b1 /\ ~c1 => F |
      (~b0 /\ c0  => T | F)))))))))))))))`--),
PURE_ONCE_REWRITE_TAC [ltascii_DEF] THEN BETA_TAC THEN
REWRITE_TAC [bit0_DEF,bit1_DEF,bit2_DEF,bit3_DEF,
	      bit4_DEF,bit5_DEF,bit6_DEF,bit7_DEF]);


(* auxiliary string ftns *)
val empty_str_DEF = new_recursive_definition
{def = --`(empty_str "" = T) /\ (empty_str (STRING a s) = F)`--,
 fixity = Prefix, name = "empty_str_DEF", 
 rec_axiom = theorem "string" "string_Axiom"};

val first_char_DEF = new_recursive_definition
{def = --`first_char (STRING a s) = a`--,
 fixity = Prefix, name = "first_char_DEF", 
 rec_axiom = theorem "string" "string_Axiom"};

val rest_string_DEF = new_recursive_definition
{def = --`rest_string (STRING a s) = s`--,
 fixity = Prefix, name = "rest_string_DEF", 
 rec_axiom = theorem "string" "string_Axiom"};

(* < for strings *)
val ltstring_DEF = new_recursive_definition
{def = 
 --`(ltstring "" s2 = ~(empty_str s2)) /\
    (ltstring (STRING a s) s2 =
     (a = first_char s2
      => ltstring s (rest_string s2)
       | ltascii a (first_char s2)))`--,
 fixity = Prefix, name = "ltstring_DEF", 
 rec_axiom = theorem "string" "string_Axiom"};

(* string_size -- # chars in string *)
val string_size_DEF = new_recursive_definition
{def = 
 --`(string_size "" = INT 0) /\
    (string_size (STRING a s) = (INT 1) plus (string_size s))`--,
 fixity = Prefix, name = "string_size_DEF", 
 rec_axiom = theorem "string" "string_Axiom"};

(* ord_char & ord_str -- get int associated with the first char of a str *)
val _ = new_recursive_definition
{def = 
 --`ord_char (ASCII b7 b6 b5 b4 b3 b2 b1 b0) = 
    INT ((b7 => 128 | 0) + (b6 => 64 | 0) + (b5 => 32 | 0) +
	 (b4 => 16 | 0) + (b3 => 8 | 0) + (b2 => 4 | 0) +
	 (b1 => 2 | 0) + (b0 => 1 | 0))`--,
 fixity = Prefix, name = "ord_char_DEF", 
 rec_axiom = theorem "ascii" "ascii_Axiom"};

val _ = new_recursive_definition
{def = --`ord_str (STRING a s) = ord_char a`--,
 fixity = Prefix, name = "ord_str_DEF", 
 rec_axiom = theorem "string" "string_Axiom"};

(* getchar implements the chr function of ML. *)
val _ = new_definition
("getchar_DEF",
 --`getchar i = 
    let b7 = (i below (INT 128)) => F | T in
     let i2 = i minus (b7 => (INT 128) | (INT 0)) in
      let b6 = (i2 below (INT 64)) => F | T in
       let i3 = i2 minus (b6 => (INT 64) | (INT 0)) in
	let b5 = (i3 below (INT 32)) => F | T in
	 let i4 = i3 minus (b5 => (INT 32) | (INT 0)) in
	  let b4 = (i4 below (INT 16)) => F | T in
	   let i5 = i4 minus (b4 => (INT 16) | (INT 0)) in
	    let b3 = (i5 below (INT 8)) => F | T in
	     let i6 = i5 minus (b3 => (INT 8) | (INT 0)) in
	      let b2 = (i6 below (INT 4)) => F | T in
	       let i7 = i6 minus (b2 => (INT 4) | (INT 0)) in
	        let b1 = (i7 below (INT 2)) => F | T in
		 let i8 = i7 minus (b1 => (INT 2) | (INT 0)) in
	          let b0 = (i8 below (INT 1)) => F | T in
		      STRING (ASCII b7 b6 b5 b4 b3 b2 b1 b0) ""`--);



val _ = export_theory();
