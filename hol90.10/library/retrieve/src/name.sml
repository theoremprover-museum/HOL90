(****************************************************************************)
(* FILE          : name.sml                                                 *)
(* DESCRIPTION   : Matching names.                                          *)
(*                                                                          *)
(* AUTHOR (HOL88): R.J.Boulton                                              *)
(* DATE          : 1989                                                     *)
(*                                                                          *)
(* TRANSLATED BY : D.R.Syme                                                 *)
(* DATE          : 1995                                                     *)
(*                                                                          *)
(* LAST MODIFIED : R.J.Boulton                                              *)
(* DATE          : 12th August 1996                                         *)
(****************************************************************************)

structure RetrieveName : RETRIEVE_NAME =
struct

local

structure String = Portable.String
structure Char = Portable.Char;

open Exception Lib RetrieveExceptions;

fun failwith_message function message =
   raise HOL_ERR{origin_structure = "RetrieveName",
                 origin_function = function,
                 message = message};

(*--------------------------------------------------------------------------*)
(* Default values for wildcards in namepatterns.                            *)
(*--------------------------------------------------------------------------*)

val wildchar1 = "?"
and wildcharn = "*";

in

(*==========================================================================*)
(* Datatype for string wildcards.                                           *)
(*==========================================================================*)

datatype wildchar = Wildchar of Char.char;

(*--------------------------------------------------------------------------*)
(* show_wildchar : wildchar -> string                                       *)
(*                                                                          *)
(* Function to convert a wildchar into a string.                            *)
(*--------------------------------------------------------------------------*)

fun show_wildchar (Wildchar c) = String.str c;

(*--------------------------------------------------------------------------*)
(* make_wildchar : string -> wildchar                                       *)
(*                                                                          *)
(* Function to make a wildchar from a string.                               *)
(*                                                                          *)
(* A string can only be made into a wildchar if it is of length 1.          *)
(*--------------------------------------------------------------------------*)

fun make_wildchar s =
   if (String.size s) = 1
   then Wildchar (String.sub (s,0))
   else failwith_message "make_wildchar" "wildchar must be a single character";

(*==========================================================================*)
(* Datatype for patterns used to match theory names and theorem names.      *)
(*                                                                          *)
(* The string represents the pattern. The first of the wildchars is the     *)
(* character which is to be used to mean `match any character'. The second  *)
(* wildchar is the character which is to be used to mean `match any number  *)
(* of characters (including none)'.                                         *)
(*==========================================================================*)

datatype namepattern = NamePattern of string * wildchar * wildchar;

(*--------------------------------------------------------------------------*)
(* show_namepattern : namepattern -> string * wildchar * wildchar           *)
(*                                                                          *)
(* Function to convert a namepattern into its representing type.            *)
(*--------------------------------------------------------------------------*)

fun show_namepattern (NamePattern np) = np;

(*--------------------------------------------------------------------------*)
(* make_namepattern : string * wildchar * wildchar -> namepattern           *)
(*                                                                          *)
(* Function to make a namepattern from a string and two wildchars.          *)
(*                                                                          *)
(* This will only succeed if the two wildchars are different. The pattern   *)
(* is simplified here, so that it need not be done every time a match is    *)
(* performed.                                                               *)
(*--------------------------------------------------------------------------*)

fun make_namepattern (s,w1,wn) =
   let (* Function to simplify a pattern, so that matching is easier.       *)
       (*                                                                   *)
       (* For example with wild1 = "?" and wildn = "*", the following       *)
       (* transformations are made:                                         *)
       (*                                                                   *)
       (* "a***b"   --> "a*b"                                               *)
       (* "a*?*b"   --> "a?*b"                                              *)
       (* "a**?*?"  --> "a??*"                                              *)
       (* "a?b?"    --> "a?b?"                                              *)
       (* "a*?**b*" --> "a?*b*"                                             *)

       fun simplify wild1 wildn sp =
          let (* Subsidiary function to do most of the work.                *)
              (*                                                            *)
              (* The boolean value is used to keep track of whether or not  *)
              (* a `wildn' character has been encountered. While passing    *)
              (* through a sequence of wildcard characters, `b' will be set *)
              (* to true if a `wildn' is encountered, and the `wildn' will  *)
              (* be omitted. At the end of the wildcard sequence, a `wildn' *)
              (* will be inserted and `b' will be reset to false.           *)

              fun simplify' s1 sn true [] = [sn]
                | simplify' s1 sn false [] = []
                | simplify' s1 sn b (s::ss) =
                 if (s = sn) then simplify' s1 sn true ss
                 else if (s = s1) then s1 :: simplify' s1 sn b ss
                 else if b
                      then sn :: s :: simplify' s1 sn false ss
                      else s :: simplify' s1 sn false ss

          in  (* Call subsidiary function with wildcards (converted to      *)
              (* strings), `wildn' inactive, and with the pattern converted *)
              (* to a list of single-character strings. Then convert the    *)
              (* processed list back to a string.                           *)

              String.concat
                 (simplify' (show_wildchar wild1) (show_wildchar wildn)
                     false (map String.str (String.explode sp)))
          end

   in  if (w1 = wn)
       then failwith_message "make_namepattern" "wildchars must be different"
       else NamePattern (simplify w1 wn s,w1,wn)
   end;

(*--------------------------------------------------------------------------*)
(* show_full_namepattern : namepattern -> string * string * string          *)
(*                                                                          *)
(* Function to convert a namepattern into the three strings representing    *)
(* it.                                                                      *)
(*--------------------------------------------------------------------------*)

fun show_full_namepattern np =
   let val (s,w1,wn) = show_namepattern np
   in  (s,show_wildchar w1,show_wildchar wn)
   end;

(*--------------------------------------------------------------------------*)
(* make_full_namepattern : string * string * string -> namepattern          *)
(*                                                                          *)
(* Function to make a namepattern from three strings.                       *)
(*                                                                          *)
(* The first string represents the pattern. The second is the wildcard      *)
(* character which means `match any character', and the third is the        *)
(* wildcard character which means `match any number of characters           *)
(* (including none)'.                                                       *)
(*--------------------------------------------------------------------------*)

fun make_full_namepattern (s,c1,cn) =
   make_namepattern (s,make_wildchar c1,make_wildchar cn);

(*--------------------------------------------------------------------------*)
(* autonamepattern : string -> namepattern                                  *)
(*                                                                          *)
(* Function to convert a string into a namepattern using the default        *)
(* wildcard characters.                                                     *)
(*--------------------------------------------------------------------------*)

fun autonamepattern s = make_full_namepattern (s,wildchar1,wildcharn);

(*--------------------------------------------------------------------------*)
(* namematch : namepattern -> string -> bool                                *)
(*                                                                          *)
(* Function to match a namepattern against a string.                        *)
(*--------------------------------------------------------------------------*)

fun namematch p s =
   let (* Extract components of namepattern.                                *)

       val (spatt,wild1,wildn) = show_full_namepattern p

       (* Function to perform the match.                                    *)
       (*                                                                   *)
       (* The last two arguments are the pattern and string converted to    *)
       (* lists of single-character strings.                                *)
       (* The function has no data to return, so it either returns (),      *)
       (* or it fails. This is done rather than returning a boolean value   *)
       (* so that exception handling can be used for backtracking.          *)
       (*                                                                   *)
       (* If both the pattern and the string are exhausted, succeed.        *)
       (* If only the pattern is exhausted, fail.                           *)
       (* If the remainder of the pattern is `wildn' on its own, succeed.   *)
       (* Any other pattern matched against a null string must fail.        *)
       (*                                                                   *)
       (* If the first character in the pattern is `wildn', try matching it *)
       (* against nothing, and if this fails, try matching it against one   *)
       (* or more characters of the string (by recursion).                  *)
       (*                                                                   *)
       (* If the first character of the pattern is `wild1', match it to the *)
       (* the first character of the string, and try to match the tails.    *)
       (* Do the same if the head of the pattern equals the head of the     *)
       (* string. If the heads differ, fail.                                *)
       (*                                                                   *)
       (* Note that this function has been specially written to be          *)
       (* efficient for the pattern `wildn' (on its own), i.e. for the      *)
       (* pattern which means `match anything'.                             *)
       (*                                                                   *)
       (* The function does not cater for quotation of the characters used  *)
       (* as wildcards.                                                     *)

       fun stringmatch w1 wn [] [] = ()
         | stringmatch w1 wn [] _ = raise NO_MATCH
         | stringmatch w1 wn (pl as p::ps) sl =
          if (p = wn) andalso (null ps)
          then ()
          else case sl
               of [] => raise NO_MATCH
                | s::ss =>
                  if (p = wn) then stringmatch w1 wn ps sl
                                   handle NO_MATCH => stringmatch w1 wn pl ss
                  else if (p = w1) then stringmatch w1 wn ps ss
                  else if (p = s) then stringmatch w1 wn ps ss
                  else raise NO_MATCH

   in  (* Convert the pattern and the string to a list of single-character  *)
       (* strings, and attempt a match. If the match succeeds return true.  *)
       (* If it fails, return false.                                        *)

       can (stringmatch wild1 wildn (map String.str (String.explode spatt)))
          (map String.str (String.explode s))

   end;

end;

end; (* RetrieveName *)
