/** \file pes.lex.c
 * Source file generated from flex lexer file pes.l.
 * @author Peter Fontana and Dezhuang Zhang. 
 * @note Although Doxygen does not read pes.l, all Doxygen
 * comments in pes.lex.c are obtained from the pes.y file.
 * @see pes.l
 * @version 1.21
 * @date November 8, 2013 */

%{
#include "ExprNode.hh"
#include <string>
#include <iostream>
#include "pes.tab.h"


int yyline=1;

extern char lastToken[1024];
char currentToken[1024];

#define SAVELAST strcpy(lastToken,currentToken); strcpy(currentToken,yytext)

char * install_ID();
int install_INT();
void do_comment();

%}


/* Marcros for certain symbol (Token) types. */

/** Instead of using token IDs, # define ___ is dealt 
 * within the set of rules . */


yyDELIM  [ \t]
/** Whitespace sequences */
yyWS     {yyDELIM}+
yyDIGIT  [0-9]
yyALPHA  [a-zA-Z]
yyALPHA_S [a-or-z]
yyINT     {yyDIGIT}+
/** Predicate Variables (LHS of PES) IDs */
yyID_C    [X-Z]({yyALPHA}|{yyDIGIT})*
/** Clock ID's  */
yyID_S    {yyALPHA_S}({yyDIGIT})*
/** Constraint IDs / CONTROL IDs */
yyID_U    [pq]({yyALPHA}|{yyDIGIT})*
/** Constant Variables */
yyCONST   C({yyALPHA}|{yyDIGIT})*
yyCHAR   .
yyLINE   \n|\r|\r\n
yyCOMM1  \/\*
yyCOMM2  \/\/{yyCHAR}*

%%

{yyCOMM2} {           }
{yyLINE}  { yyline++; }
{yyWS}    {           }
"CLOCKS"     { return TOK_CLOCKS;  }
"CONTROL"     { return TOK_ATOMIC;  }
"PREDICATE"  { return TOK_PREDICATE;  }
"EQUATIONS"  { return TOK_EQUATIONS;  }
"TRUE"       { return TOK_TRUE;       }
"FALSE"      { return TOK_FALSE;      }
"START"      { return TOK_START;      }
"mu"         { return TOK_MU;      }
"nu"         { return TOK_NU;      }
"\\forall"   { return TOK_FORALL;      }
"\\exists"   { return TOK_EXISTS;      }
"time"       { return TOK_TIME;      }
"time\\rel"    { return TOK_TIME_REL; }
"#define"       { return TOK_DEFINE;      }
"INITIALLY"       { return TOK_INITIALLY;      }
"INVARIANT"       { return TOK_INVARIANT;      }

"TRANSITIONS"   { return TOK_TRANSITIONS; }
"AbleWaitInf"    { return TOK_ABLEWAITINF;}
"UnableWaitInf" { return TOK_UNABLEWAITINF;}
"\\AllAct"    { return TOK_ALLACT;}
"\\ExistAct"  { return TOK_EXISTACT;}

"!="  {        return TOK_NEQ      ;     }
":"  {        return TOK_COLON      ;     }
","  {        return TOK_COMMA      ;     }
";"  {        return TOK_SEMICOLON  ;     }
"["  {        return TOK_LBRACK     ;     }
"]"  {        return TOK_RBRACK     ;     }
"("  {        return TOK_LPAREN     ;     }
")"  {        return TOK_RPAREN     ;     }
"{"  {        return TOK_LBRACE     ;     }
"}"  {        return TOK_RBRACE     ;     }
"+"  {        return TOK_PLUS       ;     }
"-"  {        return TOK_MINUS      ;     }
"="  {        return TOK_ASSIGN     ;     }
"&&" {        return TOK_AND        ;     }
"||" {        return TOK_OR         ;     }
"|s|" {       return TOK_OR_SIMPLE       ;     }
">"  {        return TOK_GT         ;     }
"<"  {        return TOK_LT         ;     }
"==" {        return TOK_EQ         ;     }
">=" {        return TOK_GE         ;     }
"<=" {        return TOK_LE         ;     }
"->" {        return TOK_IMPLY      ;     }

{yyINT}   {
  yylval.intVal = install_INT();
  return TOK_INT;
}

{yyID_C} { SAVELAST;  
  //yylval.strVal = strdup(yytext);
  yylval.strVal = strdup(yytext);
  return TOK_ID_PREDICATE ; 
}

{yyID_S} { SAVELAST;   
  yylval.strVal = strdup(yytext);
  return TOK_ID_CLOCK ; 
}

{yyID_U} { SAVELAST;  
  yylval.strVal = strdup(yytext);
  return TOK_ID_ATOMIC ; 
}

{yyCONST} { SAVELAST;  
  yylval.strVal = strdup(yytext);
  return TOK_ID_CONST ; 
}

{yyCOMM1} {
  do_comment();
}

{yyCHAR}  {
  yylval.strVal = yytext;
  return TOK_SYNTAX_ERROR;
}    

%%


/* Methods that are defined in the C File. */

/** Token yywrap here as dummy function. 
 * @return 1. */
inline int yywrap(void) {
  return 1;
}


/** Reads and returns the next input's (integer) value.
 * This method is used to give values to tokens lexed as integers. This
 * method assumes that the next input is an integer.
 * @return The integer value of the int being read in. */
int install_INT()
{
  int i;
  sscanf(yytext, "%d", &i);
  return i;
}

/** Properly lexes and keeps track of /-* *-/ Comments in the lex file.
 * The text characters inside the comments are ignored, yet line numbers
 * are preserved.
 * @return None. */
void do_comment()
{
  register int c;
  for( ; ; )
  {
    while ((c = yyinput())!='*' && c != EOF)
    if ( c == '\n' ) yyline++;
    if ( c == '*' )
    {
      while ( (c = yyinput()) == '*')
      ;
      if ( c == '/' )
      break;
    }
    if ( c == EOF )
    {
      break;
    }
  }
}

/** Reads and returns the next input's (string) value.
 * This method is used to give values to tokens lexed as strings. This
 * method assumes that the next input is an string.
 * @return The string value of the input being read in. */
char * install_ID() 
{
  return yytext;   
}

