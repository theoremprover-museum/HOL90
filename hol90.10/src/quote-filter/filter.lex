   /* hol-quote-filter.lex */

   /* Filter to provide quotation and antiquotation for the HOL system. */
   /* Written by R.J.Boulton, 13th November 1995.                       */
   /* Modified on 9th July 1997 by RJB to fix bug spotted by M. Norrish.*/

   /* Expects the following Standard ML datatype to have been declared: */
   /*                                                                   */
   /*    datatype 'a frag = QUOTE of string | ANTIQUOTE of 'a;          */
   /*                                                                   */
   /* and also the functions term_parser, type_parser, and ty_antiq.    */

   /* This filter adds the following special features to Standard ML:   */
   /*                                                                   */
   /*    `...`        a generic quotation                               */
   /*    ``...``      a HOL term quotation                              */
   /*    ``:...``     a HOL type quotation                              */
   /*    --`...`--    a HOL term quotation (for backward compatibility) */
   /*    ==`:...`==   a HOL type quotation (for backward compatibility) */
   /*                                                                   */
   /*    `... ^(...) ...`      antiquotation in a generic quotation     */
   /*    ``... ^(...) ...``    term antiquotation in a HOL term         */
   /*    ``... :^(...) ...``   type antiquotation in a HOL term         */
   /*    ``:... ^(...) ...``   type antiquotation in a HOL type         */
   /*                                                                   */
   /* where (...) may be an alphanumeric or symbolic ML identifier or a */
   /* parenthesized expression. The number of lines in the processed    */
   /* text remains unchanged.                                           */
   /*                                                                   */
   /* Limitations:                                                      */
   /*                                                                   */
   /*    o No carriage return or line feed may appear between the `--'  */
   /*      or `==' and the quotation marks in the old-style quotations. */

%{
unsigned antiquote = 0;
%}

%s STRING COMMENT QUOTE TMQUOTE OLDTMQUOTE TYQUOTE OLDTYQUOTE ANTIQUOTE

letter [A-Za-z]
digit  [0-9]
symbol [!%&$+/:<=>?@~|#*]|\\|\-|\^
id     {letter}({letter}|{digit}|_|')*|{symbol}+
ws     [ \t]

%%

%{
int pardepth = 0;
int comdepth = 0;
int prevstate = INITIAL;
%}

<INITIAL>\"       { ECHO; BEGIN STRING; }
<INITIAL>"(*"     { ECHO; ++comdepth; BEGIN COMMENT; }
<INITIAL>"("      { ECHO; ++pardepth; }
<INITIAL>")"      { ECHO; --pardepth;
                    if (antiquote && pardepth < 1) return 0; }
<INITIAL>=={ws}*` { printf("(type_parser [QUOTE \""); BEGIN OLDTYQUOTE; }
<INITIAL>--{ws}*` { printf("(term_parser [QUOTE \""); BEGIN OLDTMQUOTE; }
<INITIAL>``{ws}*: { printf("(type_parser [QUOTE \":"); BEGIN TYQUOTE; }
<INITIAL>``       { printf("(term_parser [QUOTE \""); BEGIN TMQUOTE; }
<INITIAL>`        { printf("[QUOTE \""); BEGIN QUOTE; }
<INITIAL>\n       { ECHO; fflush(stdout); fflush(stdout); }

<STRING>\\\\      { ECHO; }
<STRING>\\\"      { ECHO; }
<STRING>\"        { ECHO; BEGIN INITIAL; }

<COMMENT>"(*"     { ECHO; ++comdepth; }
<COMMENT>"*)"     { ECHO; --comdepth; if (comdepth < 1) BEGIN INITIAL; }

<QUOTE>`          { printf("\"]"); BEGIN INITIAL; }
<QUOTE>\^         { printf("\",ANTIQUOTE (");
                    prevstate = QUOTE; BEGIN ANTIQUOTE; }
<QUOTE>\\         { printf("\\\\"); }
<QUOTE>\"         { printf("\\\""); }
<QUOTE>\t         { printf("\\t"); }
<QUOTE>\n         { printf(" \",\nQUOTE \""); }

<TMQUOTE>``       { printf("\"])"); BEGIN INITIAL; }
<TMQUOTE>:{ws}*\^ { printf(":\",ANTIQUOTE (ty_antiq ");
                    prevstate = TMQUOTE; BEGIN ANTIQUOTE; }
<TMQUOTE>\^       { printf("\",ANTIQUOTE (");
                    prevstate = TMQUOTE; BEGIN ANTIQUOTE; }
<TMQUOTE>\\       { printf("\\\\"); }
<TMQUOTE>\"       { printf("\\\""); }
<TMQUOTE>\t       { printf("\\t"); }
<TMQUOTE>\n       { printf(" \",\nQUOTE \""); }

<OLDTMQUOTE>`{ws}*-- { printf("\"])"); BEGIN INITIAL; }
<OLDTMQUOTE>\^       { printf("\",ANTIQUOTE (");
                       prevstate = OLDTMQUOTE; BEGIN ANTIQUOTE; }
<OLDTMQUOTE>\\       { printf("\\\\"); }
<OLDTMQUOTE>\"       { printf("\\\""); }
<OLDTMQUOTE>\t       { printf("\\t"); }
<OLDTMQUOTE>\n       { printf(" \",\nQUOTE \""); }

<TYQUOTE>``       { printf("\"])"); BEGIN INITIAL; }
<TYQUOTE>\^       { printf("\",ANTIQUOTE (ty_antiq ");
                    prevstate = TYQUOTE; BEGIN ANTIQUOTE; }
<TYQUOTE>\\       { printf("\\\\"); }
<TYQUOTE>\"       { printf("\\\""); }
<TYQUOTE>\t       { printf("\\t"); }
<TYQUOTE>\n       { printf(" \",\nQUOTE \""); }

<OLDTYQUOTE>`{ws}*== { printf("\"])"); BEGIN INITIAL; }
<OLDTYQUOTE>\^       { printf("\",ANTIQUOTE (");
                       prevstate = OLDTYQUOTE; BEGIN ANTIQUOTE; }
<OLDTYQUOTE>\\       { printf("\\\\"); }
<OLDTYQUOTE>\"       { printf("\\\""); }
<OLDTYQUOTE>\t       { printf("\\t"); }
<OLDTYQUOTE>\n       { printf(" \",\nQUOTE \""); }

<ANTIQUOTE>{id}   { ECHO; printf("),QUOTE \""); BEGIN prevstate; }
<ANTIQUOTE>"("    { yyless(0); BEGIN INITIAL; anti();
                    printf("),QUOTE \""); BEGIN prevstate; }
<ANTIQUOTE>{ws}+  { }
<ANTIQUOTE>\n     { ECHO; }
<ANTIQUOTE>.      { yyless(0); printf("),QUOTE \""); BEGIN prevstate; }

%%

#include <signal.h>

anti()
{ int x;
  unsigned old = antiquote;
  antiquote = 1;
  x = yylex();
  antiquote = old;
  return x;
}

main()
{ signal(SIGINT,SIG_IGN); /* Allows ^C to pass to the HOL process
                             -- thanks to J.R.Harrison for this code */
  return yylex();
}
