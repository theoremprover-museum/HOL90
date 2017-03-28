
new_theory "zip";

(* These first 2 are not strictly zipping, but tend to be useful
   when zip is used *)

val PAIR = theorem "pair" "PAIR";

val PAIR_FORALL = TAC_PROOF (([],
  (--`!P. (!s:'a#'b. P s) = (! s1 s2. P (s1,s2))`--)),
 GEN_TAC THEN
 EQ_TAC THEN
 REPEAT STRIP_TAC THEN
 PURE_ONCE_REWRITE_TAC[SYM (SPEC_ALL PAIR)] THEN
 ASM_REWRITE_TAC[]);

val PAIR_EXISTS = TAC_PROOF (([],
  (--`!P. (?s:'a#'b. P s) = (? s1 s2. P(s1,s2))`--)),
 GEN_TAC THEN
 EQ_TAC THEN
 STRIP_TAC THENL
 [
  EXISTS_TAC (--`FST (s:'a#'b)`--) THEN
  EXISTS_TAC (--`SND (s:'a#'b)`--)
 ,
  EXISTS_TAC (--`(s1:'a),(s2:'b)`--)
 ] THEN
 ASM_REWRITE_TAC[]);

val ZIP = new_definition ("ZIP",
 (--`!(x:'a) (y:'a->'b) (z:'a->'c). ZIP (y,z) x = (y x,z x)`--));

(* infix version of ZIP - not a true inverse of UNZIP,
  but often much easier to read *)

val Zip_DEF = new_infix_definition ("Zip_DEF",
 (--`!(a:'a->'b) (b:'a->'c). $Zip a b = ZIP (a,b)`--), 1000);

val UNZIP = new_definition ("UNZIP",
 (--`!y:'a->'b#'c. UNZIP y = ((\x. FST (y x)),(\x. SND (y x)))`--));

(*  |- !a b x. (a Zip b)x = a x,b x *)

val Zip = REWRITE_RULE[ZIP] (CONV_RULE (ONCE_DEPTH_CONV FUN_EQ_CONV) Zip_DEF);

val ZIP_UNZIP = TAC_PROOF (([], (--`!y:'a->'b#'c. ZIP (UNZIP y) = y`--)),
 CONV_TAC (ONCE_DEPTH_CONV FUN_EQ_CONV) THEN
 REWRITE_TAC[UNZIP,ZIP] THEN
 BETA_TAC THEN
 REWRITE_TAC[]);

val UNZIP_ZIP = TAC_PROOF (([],
   (--`! y:('a->'b)#('a->'c). UNZIP(ZIP y) = y`--)),
 GEN_TAC THEN
 SUBST_TAC[SYM (SPEC (--` y:('a->'b)#('a->'c)`--) (INST_TYPE
  [{residue=(==`:'a->'b`==),redex=(==`:'a`==)},
   {residue=(==`:('a->'c)`==),redex=(==`:'b`==)}]
  PAIR))] THEN
 REWRITE_TAC[ZIP,UNZIP,ETA_AX]);

val EXISTS_ZIP = TAC_PROOF (([],
  (--`!P:('a->'b#'c)->bool. (?s. P s) = (? s1 s2. P (ZIP (s1, s2)))`--)),
 GEN_TAC THEN EQ_TAC THEN STRIP_TAC THENL
 [
  EXISTS_TAC (--`FST (UNZIP (s:'a->'b#'c))`--) THEN
  EXISTS_TAC (--`SND (UNZIP (s:'a->'b#'c))`--) THEN
  REWRITE_TAC[ZIP_UNZIP]
 ,
  EXISTS_TAC (--`ZIP((s1:'a->'b),(s2:'a->'c))`--)
 ] THEN
 POP_ASSUM ACCEPT_TAC);

(*  |- !P. (?s. P s) = (?s1 s2. P (s1 Zip s2)) *)

val EXISTS_Zip = REWRITE_RULE[SYM (SPEC_ALL Zip_DEF)] EXISTS_ZIP;

val FORALL_ZIP = TAC_PROOF (([],
  (--`!P:('a->'b#'c)->bool. (!s. P s) = (! s1 s2. P (ZIP (s1, s2)))`--)),
 GEN_TAC THEN
 EQ_TAC THEN
 REPEAT STRIP_TAC THENL
 [
  ASM_REWRITE_TAC[]
 ,
  POP_ASSUM (ACCEPT_TAC o REWRITE_RULE[ZIP_UNZIP] o SPECL
   [(--`FST (UNZIP (s:'a->'b#'c))`--),(--`SND (UNZIP (s:'a->'b#'c))`--)])
 ]);

(*  |- !P. (!s. P s) = (!s1 s2. P (s1 Zip s2)) *)

val FORALL_Zip = REWRITE_RULE[SYM (SPEC_ALL Zip_DEF)] FORALL_ZIP;

save_thm ("PAIR_FORALL",PAIR_FORALL);
save_thm ("PAIR_EXISTS",PAIR_EXISTS);
save_thm ("Zip",Zip);
save_thm ("UNZIP_ZIP",UNZIP_ZIP);
save_thm ("ZIP_UNZIP",ZIP_UNZIP);
save_thm ("EXISTS_ZIP",EXISTS_ZIP);
save_thm ("EXISTS_Zip",EXISTS_Zip);
save_thm ("FORALL_ZIP",FORALL_ZIP);
save_thm ("FORALL_Zip",FORALL_Zip);

export_theory();

