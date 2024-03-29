// clang-format off
%{
  // clang-format on
  /* Doxygen does not read pes.y; it reads the files pes.y generates:
   * pes.tab.h and pes.tab.c. Doxygen comments are included in pes.y. */

  /** \file pes.tab.h
   * Header file generated by Bison parser file pes.y.
   * @author Peter Fontana, Dezhuang Zhang, and Rance Cleaveland.
   * @note Although Doxygen does not read pes.y, all Doxygen
   * comments in pes.tab.h are obtained from the pes.y file.
   * @see pes.y
   * @version 1.21
   * @date November 8, 2013 */

  /** \file pes.tab.c
   * Source file generated by Bison parser file pes.y.
   * @author Peter Fontana, Dezhuang Zhang, and Rance Cleaveland.
   * @note Although Doxygen does not read pes.y, all Doxygen
   * comments in pes.tab.c are obtained from the pes.y file.
   * @see pes.y
   * @version 1.21
   * @date November 8, 2013 */

#include <iostream>
#include <vector>
#include "pes.h"
#include "ExprNode.h"
#include "transition.h"
#include "array.h"
#include "DBM.h"
#include "pes.tab.h"
#include "pes.lex.h"

  // using namespace std;

  char lastToken[1024];

  extern void yyerror(void* scanner, bool debug, pes& input_pes, char *s);
  extern int  yylex(YYSTYPE * lvalp, void *scanner);

  std::map<std::string, int> defined_constants;

  // clang-format off
%}
// clang-format on

// reentrant parser
%pure-parser

// tell the parser to send the lexer an extra argument
%lex-param {void * scanner}

// Create  the thing to pass into the lexer as an argument to the parser.
%parse-param {void * scanner}

  // Parameters for the parser.
%parse-param {bool debug}
%parse-param {pes& input_pes}

%start pes


/** This union represents
 * the different values/data types used in the parser when
 * parsing the input file. */
%union {
  char* strVal;
  short int   intVal;
  ExprNode* exprVal;
  clock_set* cSet;
  SubstList* subList;
  DBM* constraint;
  Transition * ttrans;
}

%type <ttrans> trans_list
%type <exprVal>  	expr exprProp atomicProp trans_left_list trans_source_list  trans_atomic trans_replace_list_top trans_replace_list
%type <constraint> 	constraints initial_list guard_list
%type <cSet>  	        reset trans_reset_list_top trans_reset_list
%type <subList>  	sublist trans_dest_list_top trans_dest_list

%token TOK_SYNTAX_ERROR
/* Keywords */
%token TOK_CLOCKS TOK_ATOMIC TOK_PREDICATE TOK_EQUATIONS TOK_START TOK_DEFINE TOK_INITIALLY TOK_INVARIANT TOK_TRANSITIONS
TOK_FORALL TOK_EXISTS TOK_TIME TOK_TIME_REL TOK_IMPLY TOK_MU TOK_NU TOK_TRUE TOK_FALSE TOK_ALLACT TOK_EXISTACT TOK_ABLEWAITINF TOK_UNABLEWAITINF

/* constants and identifiers */
%token <intVal> TOK_INT
%token <strVal> TOK_ID_CLOCK TOK_ID_PREDICATE TOK_ID_ATOMIC TOK_ID_CONST

/* miscellaneous operators */
%token TOK_COLON TOK_COMMA TOK_SEMICOLON
%token TOK_LBRACK TOK_RBRACK TOK_LPAREN TOK_RPAREN
%token TOK_LBRACE TOK_RBRACE

/* Arithmetic operators, with precedence info */
%right TOK_ASSIGN
%left TOK_IMPLY
%left TOK_OR
%left TOK_OR_SIMPLE
%left TOK_AND
%left TOK_EQ TOK_NEQ
%left TOK_GT TOK_LT TOK_GE TOK_LE
%left TOK_PLUS TOK_MINUS
%left TOK_LPAREN
%left TOK_LBRACK

%%
/** Overall structure of an input (PES Model + Formula) file.
 * Structure:
 * 		#define (define_list)
 *		CLOCKS :{} (clock_Decl)
 *		CONTROL :{} (atomic_Decl)
 *		INITIALLY :{} (initial_Decl)
 * 		PREDICATE :{} (predicate_Decl)
 * 		START:  (start_Decl)
 * 		EQUATIONS: {} (equation_Defn)
 * 		INVARIANT: (inv_Decl)
 *    TRANSITIONS: (trans_Decl)
 * */
pes:    	/*empty*/
/* For consistency of parser, if no initial condition, print saying
 * that default initial condition is used */
{ /*do nothing*/ }
| clocks_Decl atomic_Decl predicate_Decl start_Decl equation_Defn inv_Decl
{  /*do nothing */         }
| define_list clocks_Decl atomic_Decl predicate_Decl start_Decl equation_Defn inv_Decl
{  /*do nothing */         }
| clocks_Decl atomic_Decl initial_Decl predicate_Decl start_Decl equation_Defn inv_Decl
{  /*do nothing */         }
| define_list clocks_Decl atomic_Decl initial_Decl predicate_Decl start_Decl equation_Defn inv_Decl
{  /*do nothing */         }
/* Now add grammar for transitions */
| clocks_Decl atomic_Decl predicate_Decl start_Decl equation_Defn inv_Decl trans_Decl
{  /*do nothing */         }
| define_list clocks_Decl atomic_Decl predicate_Decl start_Decl equation_Defn inv_Decl trans_Decl
{  /*do nothing */         }
| clocks_Decl atomic_Decl initial_Decl predicate_Decl start_Decl equation_Defn inv_Decl trans_Decl
{  /*do nothing */         }
| define_list clocks_Decl atomic_Decl initial_Decl predicate_Decl start_Decl equation_Defn inv_Decl trans_Decl
{  /*do nothing */         };


/* Now parse transitions */
trans_Decl:
 TOK_TRANSITIONS TOK_COLON trans_list_top  { /* do nothing */ };
trans_list_top: /* empty */ { }
| trans_list {};
trans_list: /* Do not allow an empty list of transitions */
/* Grammar for transitions. Note that any (or all) of the components
 * can be empty. */
// trans_dest_list_top gives assignments to atomic variables
// trans_reset_list_top gives resets of clock variables
// trans_replace_list_top gives assignments to clock variables.
trans_left_list TOK_IMPLY trans_dest_list_top trans_reset_list_top trans_replace_list_top TOK_SEMICOLON
{
  ExprNode *leftExpr = $1;
  ExprNode *parExpr = nullptr;
  ExprNode *rightExpr = nullptr;
  bool leftBool = true;
  // leftBool = false iff there are no assignments to atomic variables, no clock resets, and no assignments to clock variables
  if($3==nullptr && $4==nullptr && $5==nullptr) {
    rightExpr = nullptr;
    leftBool = false;
  }
  else if($3==nullptr && $4==nullptr) {

    /* Iterate through the assignment expression
     * until we reach the boolean expression. */
    ExprNode *currExpr = $5;
    while(currExpr->getExpr()->getOpType() != BOOL) {
      currExpr = currExpr->getExpr();
    }
    ExprNode *tempExprC = currExpr->getExpr();
    currExpr->setExprDestLeft(nullptr);
    parExpr = currExpr;
    delete tempExprC;
  }
  else if($3==nullptr && $5==nullptr) {
    rightExpr = new ExprNode(RESET, nullptr, $4, input_pes.clocks(), input_pes.atomic());
    parExpr = rightExpr;
  }
  else if($4==nullptr && $5==nullptr) {
    rightExpr = new ExprNode(SUBLIST, nullptr, $3, input_pes.clocks(), input_pes.atomic());
    parExpr = rightExpr;
  }
  else if($3 == nullptr) {
    /* Iterate through the assignment expression
     * until we reach the boolean expression. */
    ExprNode *currExpr = $5;
    while(currExpr->getExpr()->getOpType() != BOOL) {
      currExpr = currExpr->getExpr();
    }
    ExprNode *tempExprC = currExpr->getExpr();
    ExprNode *tempExpr = new ExprNode(RESET, nullptr, $4, input_pes.clocks(), input_pes.atomic());
    currExpr->setExprDestLeft(tempExpr);
    parExpr = tempExpr;
    delete tempExprC;
    rightExpr = $5;

  }
  else if($4 == nullptr) {
    /* Iterate through the assignment expression
     * until we reach the boolean expression. */
    ExprNode *currExpr = $5;
    while(currExpr->getExpr()->getOpType() != BOOL) {
      currExpr = currExpr->getExpr();
    }
    ExprNode *tempExprC = currExpr->getExpr();
    ExprNode *tempExpr = new ExprNode(SUBLIST, nullptr, $3, input_pes.clocks(), input_pes.atomic());
    currExpr->setExprDestLeft(tempExpr);
    parExpr = tempExpr;
    delete tempExprC;
    rightExpr = $5;

  }
  else if($5 == nullptr) {
    ExprNode *tempExpr = new ExprNode(SUBLIST, nullptr, $3, input_pes.clocks(), input_pes.atomic());
    parExpr = tempExpr;
    rightExpr = new ExprNode(RESET, tempExpr, $4, input_pes.clocks(), input_pes.atomic());
  }
  else {
    /* Iterate through the assignment expression
     * until we reach the boolean expression. */
    ExprNode *currExpr = $5;
    while(currExpr->getExpr()->getOpType() != BOOL) {
      currExpr = currExpr->getExpr();
    }
    ExprNode *tempExprC = currExpr->getExpr();
    ExprNode *tempExpr = new ExprNode(SUBLIST, nullptr, $3, input_pes.clocks(), input_pes.atomic());
    ExprNode *aboveTempExpr = new ExprNode(RESET, tempExpr, $4, input_pes.clocks(), input_pes.atomic());
    currExpr->setExprDestLeft(aboveTempExpr);
    parExpr = tempExpr;
    delete tempExprC;
    rightExpr = $5;
  }
  std::vector<std::pair<atomic_size_type, atomic_value_t>> *assignVector =
      nullptr;
  if($5 != nullptr) {
    assignVector =
        new std::vector<std::pair<atomic_size_type, atomic_value_t>>(0);
    makeAssignmentList(*$5, assignVector);
  }
  Transition * t = new Transition(parExpr, leftExpr, rightExpr, leftBool, $3, $4, assignVector);
  input_pes.add_transition(t);
  delete assignVector;

}
| trans_list trans_left_list TOK_IMPLY trans_dest_list_top trans_reset_list_top trans_replace_list_top TOK_SEMICOLON
{
  ExprNode *leftExpr = $2;

  ExprNode *parExpr = nullptr;
  ExprNode *rightExpr;
  bool leftBool = true;
  if($4==nullptr && $5==nullptr && $6==nullptr) {
    rightExpr = nullptr;
    leftBool = false;
  }
  else if($4==nullptr && $5==nullptr) {

    /* Iterate through the assignment expression
     * until we reach the boolean expression. */
    ExprNode *currExpr = $6;
    while(currExpr->getExpr()->getOpType() != BOOL) {
      currExpr = currExpr->getExpr();
    }
    ExprNode *tempExprC = currExpr->getExpr();
    currExpr->setExprDestLeft(nullptr);
    parExpr = currExpr;
    delete tempExprC;
  }
  else if($4==nullptr && $6==nullptr) {
    rightExpr = new ExprNode(RESET, nullptr, $5, input_pes.clocks(), input_pes.atomic());
    parExpr = rightExpr;
  }
  else if($5==nullptr && $6==nullptr) {
    rightExpr = new ExprNode(SUBLIST, nullptr, $4, input_pes.clocks(), input_pes.atomic());
    parExpr = rightExpr;
  }
  else if($4 == nullptr) {
    /* Iterate through the assignment expression
     * until we reach the boolean expression. */
    ExprNode *currExpr = $6;
    while(currExpr->getExpr()->getOpType() != BOOL) {
      currExpr = currExpr->getExpr();
    }
    ExprNode *tempExprC = currExpr->getExpr();
    ExprNode *tempExpr = new ExprNode(RESET, nullptr, $5, input_pes.clocks(), input_pes.atomic());
    currExpr->setExprDestLeft(tempExpr);
    parExpr = tempExpr;
    delete tempExprC;
    rightExpr = $6;

  }
  else if($5 == nullptr) {
    /* Iterate through the assignment expression
     * until we reach the boolean expression. */
    ExprNode *currExpr = $6;
    while(currExpr->getExpr()->getOpType() != BOOL) {
      currExpr = currExpr->getExpr();
    }
    ExprNode *tempExprC = currExpr->getExpr();
    ExprNode *tempExpr = new ExprNode(SUBLIST, nullptr, $4, input_pes.clocks(), input_pes.atomic());
    currExpr->setExprDestLeft(tempExpr);
    parExpr = tempExpr;
    delete tempExprC;
    rightExpr = $6;

  }
  else if($6 == nullptr) {
    ExprNode *tempExpr = new ExprNode(SUBLIST, nullptr, $4, input_pes.clocks(), input_pes.atomic());
    parExpr = tempExpr;
    rightExpr = new ExprNode(RESET, tempExpr, $5, input_pes.clocks(), input_pes.atomic());
  }
  else {
    /* Iterate through the assignment expression
     * until we reach the boolean expression. */
    ExprNode *currExpr = $6;
    while(currExpr->getExpr()->getOpType() != BOOL) {
      currExpr = currExpr->getExpr();
    }
    ExprNode *tempExprC = currExpr->getExpr();
    ExprNode *tempExpr = new ExprNode(SUBLIST, nullptr, $4, input_pes.clocks(), input_pes.atomic());
    ExprNode *aboveTempExpr = new ExprNode(RESET, tempExpr, $5, input_pes.clocks(), input_pes.atomic());
    currExpr->setExprDestLeft(aboveTempExpr);
    parExpr = tempExpr;
    delete tempExprC;
    rightExpr = $6;
  }
  std::vector<std::pair<atomic_size_type, atomic_value_t>> *assignVector =
      nullptr;
  if($6 != nullptr) {
    assignVector =
        new std::vector<std::pair<atomic_size_type, atomic_value_t>>(0);
    makeAssignmentList(*$6, assignVector);
  }
  Transition * t = new Transition(parExpr, leftExpr, rightExpr, leftBool, $4, $5, assignVector);
  input_pes.add_transition(t);
  delete assignVector;

};

trans_left_list: /* must be nonempty */
TOK_LPAREN TOK_RPAREN /* Empty left expression indicated by () */
{
    $$ = new ExprNode(BOOL, true, input_pes.clocks(), input_pes.atomic());
}
| TOK_LPAREN trans_source_list TOK_RPAREN /* State constraints only */
{
    $$ = $2;
}
| TOK_LPAREN guard_list TOK_RPAREN /* Guards only */
{
  $$ = new ExprNode(CONSTRAINT, $2, input_pes.clocks(), input_pes.atomic());
}
| TOK_LPAREN trans_source_list TOK_COMMA guard_list TOK_RPAREN
/* State and clock constraints */
{
  $$ = new ExprNode(AND, $2, new ExprNode(CONSTRAINT, $4, input_pes.clocks(), input_pes.atomic()), input_pes.clocks(), input_pes.atomic());
};


trans_source_list: /* Cannot be empty */
trans_atomic
{
  $$ = $1;
}
| trans_source_list TOK_AND trans_source_list
{
   $$ = new ExprNode(AND, $1, $3, input_pes.clocks(), input_pes.atomic());
}
| trans_source_list TOK_OR trans_source_list
{
   $$ = new ExprNode(OR, $1, $3, input_pes.clocks(), input_pes.atomic());
}
| TOK_LPAREN trans_source_list TOK_RPAREN
{
   $$ = $2;
};

trans_atomic: /* Cannot be empty */
TOK_ID_ATOMIC TOK_LT TOK_INT
{
  const std::size_t x = input_pes.lookup_atomic($1);
  $$ = new ExprNode(ATOMIC_LT, x, $3, input_pes.clocks(), input_pes.atomic());
  delete $1;
}
|TOK_ID_ATOMIC TOK_GT TOK_INT
{
  const std::size_t x = input_pes.lookup_atomic($1);
  $$ = new ExprNode(ATOMIC_GT, x, $3, input_pes.clocks(), input_pes.atomic());
  delete $1;
}
|TOK_ID_ATOMIC TOK_LE TOK_INT
{
  const std::size_t x = input_pes.lookup_atomic($1);
  $$ = new ExprNode(ATOMIC_LE, x, $3, input_pes.clocks(), input_pes.atomic());
  delete $1;
}
|TOK_ID_ATOMIC TOK_GE TOK_INT
{
  const std::size_t x = input_pes.lookup_atomic($1);
  $$ = new ExprNode(ATOMIC_GE, x, $3, input_pes.clocks(), input_pes.atomic());
  delete $1;
}
|TOK_ID_ATOMIC TOK_EQ TOK_INT
{
  const std::size_t x = input_pes.lookup_atomic($1);
  $$ = new ExprNode(ATOMIC, x, $3, input_pes.clocks(), input_pes.atomic());
  delete $1;
}
|TOK_ID_ATOMIC TOK_NEQ TOK_INT
{
  const std::size_t x = input_pes.lookup_atomic($1);
  $$ = new ExprNode(ATOMIC_NOT, x, $3, input_pes.clocks(), input_pes.atomic());
  delete $1;
} ;


guard_list: /* Cannot be empty */
constraints
{
  $$ = $1;
  $$->cf();
}
| guard_list TOK_AND constraints
{
  DBM tt(*($1));
  /* Intersection of two DBMs to represent
   * an intersection of DBM clock constraints. */
  tt.intersect(*($3));
  $$ = new DBM(tt);
  $$->cf();
  delete $1;
  delete $3;
};

trans_dest_list_top: /* empty */ { $$ = nullptr;}
| TOK_LPAREN trans_dest_list TOK_RPAREN {$$ = $2;}

trans_dest_list: /* cannot be empty */
TOK_ID_ATOMIC TOK_ASSIGN TOK_INT
{
  const std::size_t x = input_pes.lookup_atomic($1);
  $$ = new SubstList(x, $3, input_pes.atomic()->size(), input_pes.atomic());
  delete $1;
}
|trans_dest_list TOK_COMMA TOK_ID_ATOMIC TOK_ASSIGN TOK_INT
{
  const std::size_t x = input_pes.lookup_atomic($3);
  $$                  = ($1)->addst(x, $5);
  delete $3;
};

trans_reset_list_top : /*empty */ {$$ = nullptr;}
| TOK_LBRACE trans_reset_list TOK_RBRACE { $$ = $2;};

trans_reset_list: /* cannot be empty */
TOK_ID_CLOCK
{
  const std::size_t x = input_pes.lookup_clock($1);
  $$                  = new clock_set(x, input_pes.clocks()->size());
  delete $1;
}
|trans_reset_list TOK_COMMA TOK_ID_CLOCK
{
  const std::size_t x = input_pes.lookup_clock($3);
  $$                  = ($1)->set(x);
  delete $3;
};

trans_replace_list_top: /* empty */ {$$ = nullptr;}
| TOK_LBRACK trans_replace_list TOK_RBRACK { $$ = $2;};

trans_replace_list: /* cannot be empty */
TOK_LBRACK TOK_ID_CLOCK TOK_ASSIGN TOK_ID_CLOCK TOK_RBRACK
{
  const std::size_t x = input_pes.lookup_clock($2);
  const std::size_t y = input_pes.lookup_clock($4);
  $$ = new ExprNode(ASSIGN, new ExprNode(BOOL,true, input_pes.clocks(), input_pes.atomic()),x,y, input_pes.clocks(), input_pes.atomic());
  delete $2;
  delete $4;
}
|trans_replace_list TOK_COMMA TOK_LBRACK TOK_ID_CLOCK TOK_ASSIGN TOK_ID_CLOCK TOK_RBRACK
{
  const std::size_t x = input_pes.lookup_clock($4);
  const std::size_t y = input_pes.lookup_clock($6);
  $$ = new ExprNode(ASSIGN, $1, x, y, input_pes.clocks(), input_pes.atomic());
  delete $4;
  delete $6;
};

/** Make an expression node for an invariant, using opType = ATOMIC.
 * The invariant is a list of implications: ATOMIC = VAL -> constraints.
 * Each condition has only one atomic value (with = constraint), yet
 * can have a conjunction of constraints.
 * The invariant is the conjunction of this implication list. */
inv_Decl:	/* empty */ { /*do nothing*/}
/* Allow "INVARIANTS:" to be specified with no list */
| TOK_INVARIANT TOK_COLON { /* do nothing */};
| TOK_INVARIANT TOK_COLON inv_list { /* do nothing */ };
/** For invariants, the atomic structure allowed is the same
 * as for transitions. Hence, we use the same parsing structure
 * for both */
inv_list:
trans_source_list TOK_IMPLY constraints
{
  ($1)->setDBM($3);
  input_pes.add_invariant($1);
}
|inv_list trans_source_list TOK_IMPLY constraints
{
  ($2)->setDBM($4);
  input_pes.add_invariant($2);
};



/** Define is a #define CONST VAL, which
 * allows the user to use constants in the examples. */
define_Decl:
TOK_DEFINE TOK_ID_CONST TOK_INT
{
  defined_constants.insert(std::make_pair($2, $3));
  // Since the string is not a pointer in defined_constants, $2 can be deleted
  delete $2;
};

define_list: define_Decl
/* empty */
{}
| define_Decl define_list
{};

clocks_Decl:
TOK_CLOCKS TOK_COLON TOK_LBRACE clocks_list TOK_RBRACE
{
  if(debug){
    std::cerr << "clocks declared: ";
    input_pes.print_clocks(std::cerr);
    std::cerr << std::endl;
  }
};

/** Take the list of clocks and store then one at a time into the
 * list of clocks. */
clocks_list:
TOK_ID_CLOCK
{ input_pes.add_clock($1) ;
  delete $1;
}
| clocks_list TOK_COMMA TOK_ID_CLOCK
{ input_pes.add_clock($3);
  delete $3;
};

atomic_Decl:
TOK_ATOMIC TOK_COLON TOK_LBRACE atomic_list TOK_RBRACE
{
  if(debug) {
    std::cerr << "control variable declared: ";
    input_pes.print_atomic(std::cerr);
    std::cerr << std::endl;
  }
};

/** Take the list of atomics (or control propositions)
 * that can take on any integer value.
 * If not assigned a value, each atomic is initially 0. */
atomic_list: /* empty */
{/*do nothing*/}
/* These parts initially give the proposition value 0. */
| TOK_ID_ATOMIC { input_pes.add_atomic($1) ; delete $1;}
| TOK_ID_ATOMIC TOK_LPAREN TOK_INT TOK_RPAREN
{
  /* Here the atomic number has the number of values
   * in () - they are for the reader, and can
   * can be ignored by the program. */
  input_pes.add_atomic($1) ;
  delete $1;
}
| atomic_list TOK_COMMA TOK_ID_ATOMIC { input_pes.add_atomic($3); delete $3; }
| atomic_list TOK_COMMA TOK_ID_ATOMIC TOK_LPAREN TOK_INT TOK_RPAREN {
  /* Here the atomic number has the number of values
   * in () - they are for the reader, and can
   * can be ignored by the program. */
  input_pes.add_atomic($3);
  delete $3;
}
/* These next two parts give the atomic the specified
 * initial value */
| TOK_ID_ATOMIC TOK_ASSIGN TOK_INT
{ input_pes.add_atomic($1,$3);
  delete $1;
}
| atomic_list TOK_COMMA TOK_ID_ATOMIC TOK_ASSIGN TOK_INT
{ input_pes.add_atomic($3,$5);
  delete $3;
};

initial_Decl:
TOK_INITIALLY TOK_COLON initial_list
{
  input_pes.set_initial_clock_zone($3);
  if(debug) {
    std::cerr << "initial condition defined" << std::endl;
  }
};

/** Here, make an initial clock zone.
 * Clock constraints can be specified; all clocks without
 * specified constraints have the default value of $0$. */
initial_list:
constraints
{ $$ = $1; $$->cf(); }
| initial_list TOK_AND constraints
{
  DBM tt(*($1));
  /* Intersection of two DBMs to represent
   * an intersection of DBM clock constraints */
  /* Can be optimized with andguard()
   * To reduce number of calls to canonical
   * Form.  */
  tt.intersect(*($3)) ;
  $$ = new DBM(tt);
  $$->cf();
  delete $1;
  delete $3;
};

predicate_Decl:
TOK_PREDICATE TOK_COLON TOK_LBRACE predicate_list TOK_RBRACE
{
  if(debug) {
    std::cerr << "predicate declared: ";
    input_pes.print_predicates(std::cerr);
    std::cerr << std::endl;
  }
};

/** Add List of Predicates with their labels. */
predicate_list:
TOK_ID_PREDICATE
{
  input_pes.add_predicate($1) ;
  // Do not delete $1 since it has its shallow copy as a predicate
  // However, delete $1 in the ExprNode at the end of the program
}
| predicate_list TOK_COMMA TOK_ID_PREDICATE
{
  input_pes.add_predicate($3);
  // Do not delete $3 since it has its shallow copy as a predicate
  // However, delete $3 in the ExprNode at the end of the program
};

start_Decl:
TOK_START TOK_COLON TOK_ID_PREDICATE
{ input_pes.start_predicate() = $3; };

equation_Defn:
TOK_EQUATIONS TOK_COLON TOK_LBRACE equation_list TOK_RBRACE
{ };

equation_list:
equation {  }
| equation TOK_SEMICOLON equation_list {  }
| equation equation_list {  };

/* For now, each equation stores the equation number as the block number,
 * and the parity as true = nu (gfp) or false = mu (lfp) */
equation:
TOK_INT TOK_COLON TOK_NU TOK_ID_PREDICATE TOK_ASSIGN expr
{
  input_pes.add_equation($1, true, $4, $6);
  delete $4;
}
|TOK_INT TOK_COLON TOK_MU TOK_ID_PREDICATE TOK_ASSIGN expr
{
  input_pes.add_equation($1, false, $4, $6);
  delete $4;
};


/** Makes most of the ExprNodes here, parsing the expression
 * in a recursive manner. */
expr:
/** The ( ) requirement for FORALL and EXISTS
 * is used to eliminate shift-reduce conflicts. */
TOK_FORALL TOK_TIME TOK_LPAREN expr TOK_RPAREN
{ $$ = new ExprNode(FORALL, $4, input_pes.clocks(), input_pes.atomic()); }
|TOK_EXISTS TOK_TIME TOK_LPAREN expr TOK_RPAREN
{ $$ = new ExprNode(EXISTS,$4, input_pes.clocks(), input_pes.atomic()); }
|TOK_FORALL TOK_TIME TOK_LPAREN TOK_LBRACE exprProp TOK_RBRACE TOK_RPAREN
{ $$ = $5; }
|TOK_EXISTS TOK_TIME TOK_LPAREN TOK_LBRACE exprProp TOK_RBRACE TOK_RPAREN
{ $$ = $5; }
/* Simplified FORALL_REL when relativized expression involves only
 * atomic proposition. */
| TOK_FORALL TOK_TIME_REL TOK_LBRACK TOK_LBRACE exprProp TOK_RBRACE TOK_RBRACK TOK_LPAREN expr TOK_RPAREN
{
  /* For now, let the operator handle the simplification rather than
   * using a simplified form for atomic propositions */
  $$ = new ExprNode(FORALL_REL, $5, $9, input_pes.clocks(), input_pes.atomic());
}
/* Simplified EXISTS_REL when relativized expression involves only
 * atomic proposition. */
|TOK_EXISTS TOK_TIME_REL TOK_LBRACK TOK_LBRACE exprProp TOK_RBRACE TOK_RBRACK TOK_LPAREN expr TOK_RPAREN
{
  /* For now, let the operator handle the simplification rather than
   * using a simplified form for atomic propositions */
  $$ = new ExprNode(EXISTS_REL, $5, $9, input_pes.clocks(), input_pes.atomic());
}
| TOK_FORALL TOK_TIME_REL TOK_LBRACK expr TOK_RBRACK TOK_LPAREN expr TOK_RPAREN
{
  $$ = new ExprNode(FORALL_REL, $4, $7, input_pes.clocks(), input_pes.atomic());
}
|TOK_EXISTS TOK_TIME_REL TOK_LBRACK expr TOK_RBRACK TOK_LPAREN expr TOK_RPAREN
{

  $$ = new ExprNode(EXISTS_REL, $4, $7, input_pes.clocks(), input_pes.atomic());
}
|TOK_ALLACT TOK_LPAREN expr TOK_RPAREN
{ $$ = new ExprNode(ALLACT, $3, input_pes.clocks(), input_pes.atomic()); }
|TOK_EXISTACT TOK_LPAREN expr TOK_RPAREN
{ $$ = new ExprNode(EXISTACT,$3, input_pes.clocks(), input_pes.atomic()); }
|expr TOK_OR expr
{ $$ = new ExprNode(OR, $1, $3, input_pes.clocks(), input_pes.atomic()); }
|expr TOK_OR_SIMPLE expr
{ $$ = new ExprNode(OR_SIMPLE, $1, $3, input_pes.clocks(), input_pes.atomic()); }
|expr TOK_AND expr
{
  /* Since both expressions are constraints,
   * intersect the constraints to optimize */
  if ($1->getOpType() == CONSTRAINT && $3->getOpType() == CONSTRAINT){
    /* Copy DBM to eliminate a memory leak */
    DBM * newDBM = new DBM(*($1->dbm()));
    newDBM->intersect(*($3->dbm()));
    newDBM->cf();
    $$ = new ExprNode(CONSTRAINT, newDBM, input_pes.clocks(), input_pes.atomic());
    delete $1;
    delete $3;

  }
  else{
    $$ = new ExprNode(AND, $1, $3, input_pes.clocks(), input_pes.atomic());
  }
}
| TOK_LBRACE exprProp TOK_RBRACE TOK_OR expr
{ $$ = new ExprNode(OR_SIMPLE, $2, $5, input_pes.clocks(), input_pes.atomic()); }
/** Creates an IMPLY.  Note that this has some restrictions
 * for the user so that expressions are well formed.
 * The program does not check for these restrictions; it
 * just produces the expression. */
|expr TOK_IMPLY expr
{ $$ = new ExprNode(IMPLY, $1, $3, input_pes.clocks(), input_pes.atomic()); }
|constraints
{
  $1->cf();
  $$ = new ExprNode(CONSTRAINT, $1, input_pes.clocks(), input_pes.atomic());
}
|TOK_ID_PREDICATE
{
  $$ = input_pes.lookup_predicate($1);
  delete $1;
}
|atomicProp
{ $$ = $1; }
|TOK_ABLEWAITINF
{
  $$ = new ExprNode(ABLEWAITINF, true, input_pes.clocks(), input_pes.atomic());
}
|TOK_UNABLEWAITINF
{
  $$ = new ExprNode(UNABLEWAITINF, false, input_pes.clocks(), input_pes.atomic());
}
/** This segment is the resets, substitutions
 * of atomic proposition values, and assignments
 * of clocks to the value of other clocks. */
|expr TOK_LBRACK reset TOK_RBRACK
{ $$ = new ExprNode(RESET, $1, $3, input_pes.clocks(), input_pes.atomic()); }
|expr TOK_LBRACK sublist TOK_RBRACK
{ $$ = new ExprNode(SUBLIST, $1, $3, input_pes.clocks(), input_pes.atomic()); }
|expr TOK_LBRACK TOK_ID_CLOCK TOK_ASSIGN TOK_ID_CLOCK TOK_RBRACK
{
  const std::size_t x = input_pes.lookup_clock($3);
  const std::size_t y = input_pes.lookup_clock($5);
  $$ = new ExprNode(ASSIGN, $1, x, y, input_pes.clocks(), input_pes.atomic());
  delete $3;
  delete $5;
}
|expr TOK_LBRACK TOK_ID_ATOMIC TOK_ASSIGN TOK_ID_ATOMIC TOK_RBRACK
{
  std::size_t x = input_pes.lookup_atomic($3);
  std::size_t y = input_pes.lookup_atomic($5);
  $$ = new ExprNode(REPLACE, $1, x, y, input_pes.clocks(), input_pes.atomic());
  delete $3;
  delete $5;
}
|TOK_LPAREN expr TOK_RPAREN  { $$ = $2 ;};


/* Cover the special case where the expression is just atomic proposition
 * constraints with conjunctions and disjunctions.
 * This case allows us to eliminate the relativization for simpler operators */
exprProp:
atomicProp { $$ = $1;};
| exprProp TOK_OR exprProp
{ $$ = new ExprNode(OR, $1, $3, input_pes.clocks(), input_pes.atomic()); }
| exprProp TOK_OR_SIMPLE exprProp
{ $$ = new ExprNode(OR_SIMPLE, $1, $3, input_pes.clocks(), input_pes.atomic()); }
| exprProp TOK_AND exprProp
{

  $$ = new ExprNode(AND, $1, $3, input_pes.clocks(), input_pes.atomic());

}
|TOK_LPAREN exprProp TOK_RPAREN  { $$ = $2 ;}


/* Just atomic propositions */
atomicProp:
TOK_TRUE { $$ = new ExprNode(BOOL, true, input_pes.clocks(), input_pes.atomic()); }
|TOK_FALSE { $$ = new ExprNode(BOOL, false, input_pes.clocks(), input_pes.atomic()); }
/* This next segment of clauses represents the constraints
 * on the atomic (control) propositions. */
|TOK_ID_ATOMIC TOK_LT TOK_INT
{
  const std::size_t x = input_pes.lookup_atomic($1);
  $$ = new ExprNode(ATOMIC_LT, x, $3, input_pes.clocks(), input_pes.atomic());
  delete $1;
}
|TOK_ID_ATOMIC TOK_GT TOK_INT
{
  const std::size_t x = input_pes.lookup_atomic($1);
  $$ = new ExprNode(ATOMIC_GT, x, $3, input_pes.clocks(), input_pes.atomic());
  delete $1;
}
|TOK_ID_ATOMIC TOK_LE TOK_INT
{
  const std::size_t x = input_pes.lookup_atomic($1);
  $$ = new ExprNode(ATOMIC_LE, x, $3, input_pes.clocks(), input_pes.atomic());
  delete $1;
}
|TOK_ID_ATOMIC TOK_GE TOK_INT
{
  const std::size_t x = input_pes.lookup_atomic($1);
  $$ = new ExprNode(ATOMIC_GE, x, $3, input_pes.clocks(), input_pes.atomic());
  delete $1;
}
|TOK_ID_ATOMIC TOK_EQ TOK_INT
{
  const std::size_t x = input_pes.lookup_atomic($1);
  $$ = new ExprNode(ATOMIC, x, $3, input_pes.clocks(), input_pes.atomic());
  delete $1;
}
|TOK_ID_ATOMIC TOK_NEQ TOK_INT
{
  const std::size_t x = input_pes.lookup_atomic($1);
  $$ = new ExprNode(ATOMIC_NOT, x, $3, input_pes.clocks(), input_pes.atomic());
  delete $1;
};

/** Here we find the maximum constant,
 * in any constraint involving
 * any clock, and add this as the maximum constant for
 * all DBMs in the PES.
 *
 * These rules do not convert the DBM
 * to canonical form (each constraint is just added to the DBM).
 * The parser structure utilizing these rules is responsible
 * for converting the final DBM to canonical form. */
constraints:
TOK_ID_CLOCK TOK_GE TOK_INT
{
  $$ = new DBM(input_pes.clocks());
  input_pes.update_max_constant($3);
  const std::size_t x = input_pes.lookup_clock($1);
  $$->addConstraint(0, x, bound_to_constraint(-$3, weak));
  delete $1;
}
|TOK_ID_CLOCK TOK_GE TOK_ID_CONST
{
  $$ = new DBM(input_pes.clocks());
  std::map<std::string, int>::iterator it = defined_constants.find($3);
  if (it == defined_constants.end()) {
    throw std::runtime_error("Macro " + std::string($3) + " not defined.");
  }
  int v = (*it).second;
  input_pes.update_max_constant(v);
  const std::size_t x = input_pes.lookup_clock($1);
  $$->addConstraint(0, x, bound_to_constraint(-v, weak));
  delete $1;
  delete $3;
}
|TOK_ID_CLOCK TOK_GT TOK_INT
{
  $$ = new DBM(input_pes.clocks());
  input_pes.update_max_constant($3);
  const std::size_t x = input_pes.lookup_clock($1);
  $$->addConstraint(0, x, bound_to_constraint(-$3, strict));
  delete $1;
}
|TOK_ID_CLOCK TOK_GT TOK_ID_CONST
{
  $$ = new DBM(input_pes.clocks());
  std::map<std::string, int>::iterator it = defined_constants.find($3);
  if (it == defined_constants.end()) {
    throw std::runtime_error("Macro " + std::string($3) + " not defined.");
  }
  int v = (*it).second;
  input_pes.update_max_constant(v);
  const std::size_t x = input_pes.lookup_clock($1);
  $$->addConstraint(0, x, bound_to_constraint(-v, strict));
  delete $1;
  delete $3;
}
|TOK_ID_CLOCK TOK_LE TOK_INT
{
  $$ = new DBM( input_pes.clocks());
  input_pes.update_max_constant($3);
  const std::size_t x = input_pes.lookup_clock($1);
  $$->addConstraint(x, 0, bound_to_constraint($3, weak));
  delete $1;
}
|TOK_ID_CLOCK TOK_LE TOK_ID_CONST
{
  $$ = new DBM(input_pes.clocks());
  std::map<std::string, int>::iterator it = defined_constants.find($3);
  if (it == defined_constants.end()) {
    throw std::runtime_error("Macro " + std::string($3) + " not defined.");
  }
  int v = (*it).second;
  input_pes.update_max_constant(v);
  const std::size_t x = input_pes.lookup_clock($1);
  $$->addConstraint(x, 0, bound_to_constraint(v, weak));
  delete $1;
  delete $3;
}
|TOK_ID_CLOCK TOK_LT TOK_INT
{
  $$ = new DBM(input_pes.clocks());
  input_pes.update_max_constant($3);
  const std::size_t x = input_pes.lookup_clock($1);
  $$->addConstraint(x, 0, bound_to_constraint($3, strict));
  delete $1;
}
|TOK_ID_CLOCK TOK_LT TOK_ID_CONST
{
  $$ = new DBM(input_pes.clocks());
  std::map<std::string, int>::iterator it = defined_constants.find($3);
  if (it == defined_constants.end()) {
    throw std::runtime_error("Macro " + std::string($3) + " not defined.");
  }
  int v = (*it).second;
  input_pes.update_max_constant(v);
  const std::size_t x = input_pes.lookup_clock($1);
  $$->addConstraint(x, 0, bound_to_constraint(v, strict));
  delete $1;
  delete $3;
}
|TOK_ID_CLOCK TOK_EQ TOK_INT
{
  $$ = new DBM(input_pes.clocks());
  input_pes.update_max_constant($3);
  const std::size_t x = input_pes.lookup_clock($1);
  $$->addConstraint(x, 0, bound_to_constraint($3, weak));
  $$->addConstraint(0, x, bound_to_constraint(-$3, weak));
  delete $1;
}
|TOK_ID_CLOCK TOK_EQ TOK_ID_CONST
{
  $$ = new DBM(input_pes.clocks());
  std::map<std::string, int>::iterator it = defined_constants.find($3);
  if (it == defined_constants.end()) {
    throw std::runtime_error("Macro " + std::string($3) + " not defined.");
  }
  int v = (*it).second;
  input_pes.update_max_constant(v);
  const std::size_t x = input_pes.lookup_clock($1);
  $$->addConstraint(x, 0, bound_to_constraint(v, weak));
  $$->addConstraint(0, x, bound_to_constraint(-v, weak));
  delete $1;
  delete $3;
}
|TOK_ID_CLOCK TOK_MINUS TOK_ID_CLOCK TOK_GE TOK_INT
{
  $$ = new DBM(input_pes.clocks());
  input_pes.update_max_constant($5);
  const std::size_t x = input_pes.lookup_clock($1);
  const std::size_t y = input_pes.lookup_clock($3);
  $$->addConstraint(y, x, bound_to_constraint(-$5, weak));
  delete $1;
  delete $3;
}
|TOK_ID_CLOCK TOK_MINUS TOK_ID_CLOCK TOK_GT TOK_INT
{
  $$ = new DBM(input_pes.clocks());
  input_pes.update_max_constant($5);
  const std::size_t x = input_pes.lookup_clock($1);
  const std::size_t y = input_pes.lookup_clock($3);
  $$->addConstraint(y, x, bound_to_constraint(-$5, strict));
  delete $1;
  delete $3;
}
|TOK_ID_CLOCK TOK_MINUS TOK_ID_CLOCK TOK_LE TOK_INT
{
  $$ = new DBM(input_pes.clocks());
  input_pes.update_max_constant($5);
  const std::size_t x = input_pes.lookup_clock($1);
  const std::size_t y = input_pes.lookup_clock($3);
  $$->addConstraint(x, y, bound_to_constraint($5, weak));
  delete $1;
  delete $3;
}
|TOK_ID_CLOCK TOK_MINUS TOK_ID_CLOCK TOK_LT TOK_INT
{
  $$ = new DBM(input_pes.clocks());
  input_pes.update_max_constant($5);
  const std::size_t x = input_pes.lookup_clock($1);
  const std::size_t y = input_pes.lookup_clock($3);
  $$->addConstraint(x, y, bound_to_constraint($5, strict));
  delete $1;
  delete $3;
}
|TOK_ID_CLOCK TOK_MINUS TOK_ID_CLOCK TOK_EQ TOK_INT
{
  $$ = new DBM(input_pes.clocks());
  input_pes.update_max_constant($5);
  const std::size_t x = input_pes.lookup_clock($1);
  const std::size_t y = input_pes.lookup_clock($3);
  $$->addConstraint(x, y, bound_to_constraint($5, weak));
  $$->addConstraint(y, x, bound_to_constraint(-$5, weak));
  delete $1;
  delete $3;
};

/** Generates the set of clocks that needs to be reset
 * as a clock_set object. */
reset:      TOK_ID_CLOCK
{
  const std::size_t x = input_pes.lookup_clock($1);
  $$                  = new clock_set(x, input_pes.clocks()->size());
  delete $1;
}
|TOK_ID_CLOCK TOK_COMMA reset
{
  const std::size_t x = input_pes.lookup_clock($1);
  $$                  = ($3)->set(x);
  delete $1;
};

/** Generate the list of proposition substitutions. */
sublist:   TOK_ID_ATOMIC TOK_ASSIGN TOK_INT
{
  const std::size_t x = input_pes.lookup_atomic($1);
  $$ = new SubstList(x, $3, input_pes.atomic()->size(), input_pes.atomic());
  delete $1;
}
|TOK_ID_ATOMIC TOK_ASSIGN TOK_INT TOK_COMMA sublist
{
  const std::size_t x = input_pes.lookup_atomic($1);
  $$                  = ($5)->addst(x, $3);
  delete $1;
};
