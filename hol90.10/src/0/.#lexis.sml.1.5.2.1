(* ===================================================================== *)
(* FILE          : lexis.sml                                             *)
(* DESCRIPTION   : predicates defining various lexical classes for       *)
(*                 hol90:                                                *)
(*                                                                       *)
(*                     1. type variables                                 *)
(*                     2. type constants                                 *)
(*                     3. term constants                                 *)
(*                                                                       *)
(*                 The lexer (generated from the file "hol_lex")         *)
(*                 should duplicate this.                                *)
(*                                                                       *)
(* AUTHOR        : Konrad Slind, University of Calgary                   *)
(* DATE          : August 26, 1991                                       *)
(* REVISED       : October,   1994, to improve efficiency.               *)
(* ===================================================================== *)

structure Lexis : Lexis_sig =
struct
open Portable;
fun LEXIS_ERR {func,mesg} =
   Exception.HOL_ERR{origin_structure="Lexis",
                    origin_function=func, message=mesg};

(*---------------------------------------------------------------------------
 * Here we use extra space to get better runtimes. Strings are not exploded;
 * finding out whether a string belongs in a particular syntax class is done
 * by checking that the ordinal of each character in the string is the
 * index (in a particular bytearray) of a box containing a 1.
 *---------------------------------------------------------------------------*)

(*---------------------------------------------------------------------------
 * We work only with ascii characters, so we allocate bytearrays of size 128. 
 * A bytearray is compact - each element of the array occupies only 1 byte. 
 * Since we are using only 0 and 1, we could probably use "bit"arrays, but
 * sheer laziness prevents us.
 *---------------------------------------------------------------------------*)

val ordof = Portable.String.ordof;
 
val hol_symbols   = ByteArray.array(128,0);
val sml_symbols   = ByteArray.array(128,0);
val alphabet      = ByteArray.array(128,0);
val numbers       = ByteArray.array(128,0);
val tyvar_ids     = ByteArray.array(128,0);
val alphanumerics = ByteArray.array(128,0);
val parens        = ByteArray.array(128,0);

fun setup table pred =
   Lib.for_se 0 127 
     (fn i => if pred(Portable.String.charof i)
               then ByteArray.update(table,i,1) else ());

(*---------------------------------------------------------------------------
 * Utility for examining the contents of character tables
 *
 * fun accum table =
 *    implode
 *      (Lib.for 0 127 
 *      (fn i => if (ByteArray.sub(table,i) = 1) then chr i else ""));
 *---------------------------------------------------------------------------*)

(*---------------------------------------------------------------------------
 * Various familiar predicates, used only to build the tables, so we can 
 * afford to write them naively.
 *---------------------------------------------------------------------------*)
fun is_alphabetic ch = 
   (ch >= "a" andalso ch <= "z" orelse ch >= "A" andalso ch <= "Z");

fun is_numeric ch = (ch >= "0" andalso ch <= "9");

fun is_alphanumeric ch = 
   is_alphabetic ch orelse is_numeric ch orelse ch = "_" orelse ch = "'";

fun is_paren "(" = true
  | is_paren ")" = true
  | is_paren _ = false;


(*---------------------------------------------------------------------------
 * Used for type variables, in which a prime is required in the first
 * position in the string, but allowed nowhere else.
 *---------------------------------------------------------------------------*)
fun is_alphanumeric_no_prime ch = 
   is_alphabetic ch orelse is_numeric ch orelse ch = "_";

fun in_string str =
   let val strlist = Portable.explode str
       val memb = Lib.C Lib.mem strlist
   in memb
   end;

val hol_symbolics = "#?+*/\\=<>&%@!,:;_|~-";
val sml_symbolics = "!%&$+/:<=>?@~|#*\\-~^";
val is_hol_symbol = in_string hol_symbolics
val is_sml_symbol = in_string sml_symbolics;

(* Build the character tables *)
val _ = setup hol_symbols is_hol_symbol;
val _ = setup sml_symbols is_sml_symbol;
val _ = setup alphabet is_alphabetic;
val _ = setup numbers is_numeric;
val _ = setup alphanumerics is_alphanumeric;
val _ = setup tyvar_ids is_alphanumeric_no_prime;
val _ = setup parens is_paren;

(*---------------------------------------------------------------------------
 * Now for the efficient string predicates. Generally, the empty string
 * is not allowed.
 *---------------------------------------------------------------------------*)

fun ok_thy_index "" = false
  | ok_thy_index str =
     let fun loop i = (ByteArray.sub(parens,ordof(str,i)) = 0) 
                       andalso loop(i+1)
     in (loop 0 handle _ => true)
     end;

fun ok_identifier str =
   let fun loop i = (ByteArray.sub(alphanumerics,ordof(str,i)) = 1) 
                     andalso loop(i+1)
   in 
   ((ByteArray.sub(alphabet,ordof(str,0)) = 1) handle _ => false)
   andalso 
   (loop 1 handle _ => true)
   end;


val allowed_type_constant = ok_identifier;

local val prime = ordof("'",0)
in
fun allowed_user_type_var str =
   let fun loop i = (ByteArray.sub(tyvar_ids,ordof(str,i)) = 1) 
                     andalso loop(i+1)
   in 
   ((ordof(str,0) = prime) handle _ => false)
   andalso 
   ((ByteArray.sub(alphabet,ordof(str,1)) = 1) handle _ => false)
   andalso 
   (loop 2 handle _ => true)
   end
end;


fun ok_symbolic str =
   let fun loop i = (ByteArray.sub(hol_symbols,ordof(str,i)) = 1) 
                     andalso loop(i+1)
   in 
   ((ByteArray.sub(hol_symbols,ordof(str,0)) = 1) handle _ => false)
   andalso 
   (loop 1 handle _ => true)
   end;

fun ok_sml_identifier str =
   let fun alphaloop i = (ByteArray.sub(alphanumerics,ordof(str,i)) = 1) 
                     andalso alphaloop(i+1)
       fun symloop i = (ByteArray.sub(sml_symbols,ordof(str,i)) = 1) 
                     andalso symloop(i+1)
   in  if ((ByteArray.sub(alphabet,ordof(str,0)) = 1) handle _ => false)
       then (alphaloop 1 handle _ => true)
       else if (ByteArray.sub(sml_symbols,ordof(str,0)) = 1)
            then (symloop 1 handle _ => true)
            else false
   end;


(*---------------------------------------------------------------------------
 * Predicate to tell if a prospective constant to-be-defined has an 
 * acceptable name. Note that this function does not recognize members of
 * constant families (just those that serve to define such families). 
 *---------------------------------------------------------------------------*)
fun allowed_term_constant "let" = false
  | allowed_term_constant "in"  = false
  | allowed_term_constant "and" = false
  | allowed_term_constant "of"  = false
  | allowed_term_constant "\\"  = false
  | allowed_term_constant ";"   = false
  | allowed_term_constant "=>"  = false
  | allowed_term_constant "|"   = false
  | allowed_term_constant ":"   = false
  | allowed_term_constant "0"   = not (Globals.nums_defined())
  | allowed_term_constant "\"\""= not (Globals.strings_defined())
  | allowed_term_constant str = 
     if (ByteArray.sub(alphabet,ordof(str,0)) = 1)
     then ok_identifier str
     else
     if (ByteArray.sub(hol_symbols,ordof(str,0)) = 1)
     then ok_symbolic str
     else false;


(*---------------------------------------------------------------------------
 * Strings representing negative integers return false, since we are only
 * (currently) interested in :num.
 *---------------------------------------------------------------------------*)
fun is_num_literal str =
   let fun loop i = (ByteArray.sub(numbers,ordof(str,i)) = 1) 
                     andalso loop(i+1)
   in 
   ((ByteArray.sub(numbers,ordof(str,0)) = 1) handle _ => false)
   andalso 
   (loop 1 handle _ => true)
   end;

local val dquote = "\""
in
fun is_string_literal s =
    (Portable.String.size s > 1)
    andalso (substring(s,0,1) = dquote)
    andalso (substring(s,String.size s - 1,1) = dquote)
end;

end; (* LEXIS *)
