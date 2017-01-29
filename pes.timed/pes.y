

%{ 
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
  #include "ExprNode.hh"
  #include "transition.hh"
  #include "OneDIntArray.hh"
  #include "DBM.hh"


  using namespace std;

  #define errPrtExit(x) { \
  cerr << x <<endl; \
  exit(1); \
  }
  #define pout(x) {\
  }
  char lastToken[1024];

  extern void yyerror(bool debug, std::vector<Transition *> *transList,
                      std::vector<ExprNode*>& invs, int& MAXC,
                      std::string& start_predicate, int& predicateInd,
                      DBM*& InitC, bidirectional_map<std::string, int>* declared_clocks,
                      bidirectional_map<std::string, int>* declared_atomic,
                      std::map<std::string, ExprNode*>* declared_predicates,
                      char *s);
  extern int yylex();
  extern SubstList * add_subst(SubstList *, char*, int );
  extern int yyline;
  extern int spaceDimension;

  map <string, int> defcons;

 %}

  // Parameters for the parser.
  // TODO: clean up by providing a simple structure/class interface.
%parse-param {bool debug}
%parse-param {std::vector<Transition *> *transList}
%parse-param {std::vector<ExprNode *>& invs}
%parse-param {int& MAXC}
%parse-param {std::string& start_predicate}
%parse-param {int& predicateInd}
%parse-param {DBM*& InitC}
%parse-param {bidirectional_map<std::string, int>* declared_clocks}
%parse-param {bidirectional_map<std::string, int>* declared_atomic}
%parse-param {std::map<std::string, ExprNode*>* declared_predicates}

%start pes


/** This union represents
 * the different values/data types used in the parser when
 * parsing the input file. */
%union {
  char* strVal;
  short int   intVal;
  ExprNode* exprVal;
  ClockSet* cSet;
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
trans_left_list TOK_IMPLY trans_dest_list_top trans_reset_list_top trans_replace_list_top TOK_SEMICOLON
{
  ExprNode *leftExpr = $1;
  ExprNode *parExpr = NULL;
  ExprNode *rightExpr = NULL;
  bool leftBool = true;
  if($3==NULL && $4==NULL && $5==NULL) {
    rightExpr = NULL;
    leftBool = false;
  }
  else if($3==NULL && $4==NULL) {

    /* Iterate through the assignment expression
     * until we reach the boolean expression. */
    ExprNode *currExpr = $5;
    while(currExpr->getExpr()->getOpType() != BOOL) {
      currExpr = currExpr->getExpr();
    }
    ExprNode *tempExprC = currExpr->getExpr();
    currExpr->setExprDestLeft(NULL);
    parExpr = currExpr;
    delete tempExprC;
  }
  else if($3==NULL && $5==NULL) {
    rightExpr = new ExprNode(RESET, NULL, $4, declared_clocks, declared_atomic);
    parExpr = rightExpr;
  }
  else if($4==NULL && $5==NULL) {
    rightExpr = new ExprNode(SUBLIST, NULL, $3, declared_clocks, declared_atomic);
    parExpr = rightExpr;
  }
  else if($3 == NULL) {
    /* Iterate through the assignment expression
     * until we reach the boolean expression. */
    ExprNode *currExpr = $5;
    while(currExpr->getExpr()->getOpType() != BOOL) {
      currExpr = currExpr->getExpr();
    }
    ExprNode *tempExprC = currExpr->getExpr();
    ExprNode *tempExpr = new ExprNode(RESET, NULL, $4, declared_clocks, declared_atomic);
    currExpr->setExprDestLeft(tempExpr);
    parExpr = tempExpr;
    delete tempExprC;
    rightExpr = $5;

  }
  else if($4 == NULL) {
    /* Iterate through the assignment expression
     * until we reach the boolean expression. */
    ExprNode *currExpr = $5;
    while(currExpr->getExpr()->getOpType() != BOOL) {
      currExpr = currExpr->getExpr();
    }
    ExprNode *tempExprC = currExpr->getExpr();
    ExprNode *tempExpr = new ExprNode(SUBLIST, NULL, $3, declared_clocks, declared_atomic);
    currExpr->setExprDestLeft(tempExpr);
    parExpr = tempExpr;
    delete tempExprC;
    rightExpr = $5;

  }
  else if($5 == NULL) {
    ExprNode *tempExpr = new ExprNode(SUBLIST, NULL, $3, declared_clocks, declared_atomic);
    parExpr = tempExpr;
    rightExpr = new ExprNode(RESET, tempExpr, $4, declared_clocks, declared_atomic);
  }
  else {
    /* Iterate through the assignment expression
     * until we reach the boolean expression. */
    ExprNode *currExpr = $5;
    while(currExpr->getExpr()->getOpType() != BOOL) {
      currExpr = currExpr->getExpr();
    }
    ExprNode *tempExprC = currExpr->getExpr();
    ExprNode *tempExpr = new ExprNode(SUBLIST, NULL, $3, declared_clocks, declared_atomic);
    ExprNode *aboveTempExpr = new ExprNode(RESET, tempExpr, $4, declared_clocks, declared_atomic);
    currExpr->setExprDestLeft(aboveTempExpr);
    parExpr = tempExpr;
    delete tempExprC;
    rightExpr = $5;
  }
  vector<pair<short int, short int> > * assignVector = NULL;
  if($5 != NULL) {
    assignVector = new vector<pair<short int, short int> >(0);
    makeAssignmentList($5, assignVector);
  }
  Transition * t = new Transition(parExpr, leftExpr, rightExpr, leftBool, $3, $4, assignVector);
  transList->push_back(t);
  delete assignVector;

}
| trans_list trans_left_list TOK_IMPLY trans_dest_list_top trans_reset_list_top trans_replace_list_top TOK_SEMICOLON
{
  ExprNode *leftExpr = $2;

  ExprNode *parExpr = NULL;
  ExprNode *rightExpr;
  bool leftBool = true;
  if($4==NULL && $5==NULL && $6==NULL) {
    rightExpr = NULL;
    leftBool = false;
  }
  else if($4==NULL && $5==NULL) {

    /* Iterate through the assignment expression
     * until we reach the boolean expression. */
    ExprNode *currExpr = $6;
    while(currExpr->getExpr()->getOpType() != BOOL) {
      currExpr = currExpr->getExpr();
    }
    ExprNode *tempExprC = currExpr->getExpr();
    currExpr->setExprDestLeft(NULL);
    parExpr = currExpr;
    delete tempExprC;
  }
  else if($4==NULL && $6==NULL) {
    rightExpr = new ExprNode(RESET, NULL, $5, declared_clocks, declared_atomic);
    parExpr = rightExpr;
  }
  else if($5==NULL && $6==NULL) {
    rightExpr = new ExprNode(SUBLIST, NULL, $4, declared_clocks, declared_atomic);
    parExpr = rightExpr;
  }
  else if($4 == NULL) {
    /* Iterate through the assignment expression
     * until we reach the boolean expression. */
    ExprNode *currExpr = $6;
    while(currExpr->getExpr()->getOpType() != BOOL) {
      currExpr = currExpr->getExpr();
    }
    ExprNode *tempExprC = currExpr->getExpr();
    ExprNode *tempExpr = new ExprNode(RESET, NULL, $5, declared_clocks, declared_atomic);
    currExpr->setExprDestLeft(tempExpr);
    parExpr = tempExpr;
    delete tempExprC;
    rightExpr = $6;

  }
  else if($5 == NULL) {
    /* Iterate through the assignment expression
     * until we reach the boolean expression. */
    ExprNode *currExpr = $6;
    while(currExpr->getExpr()->getOpType() != BOOL) {
      currExpr = currExpr->getExpr();
    }
    ExprNode *tempExprC = currExpr->getExpr();
    ExprNode *tempExpr = new ExprNode(SUBLIST, NULL, $4, declared_clocks, declared_atomic);
    currExpr->setExprDestLeft(tempExpr);
    parExpr = tempExpr;
    delete tempExprC;
    rightExpr = $6;

  }
  else if($6 == NULL) {
    ExprNode *tempExpr = new ExprNode(SUBLIST, NULL, $4, declared_clocks, declared_atomic);
    parExpr = tempExpr;
    rightExpr = new ExprNode(RESET, tempExpr, $5, declared_clocks, declared_atomic);
  }
  else {
    /* Iterate through the assignment expression
     * until we reach the boolean expression. */
    ExprNode *currExpr = $6;
    while(currExpr->getExpr()->getOpType() != BOOL) {
      currExpr = currExpr->getExpr();
    }
    ExprNode *tempExprC = currExpr->getExpr();
    ExprNode *tempExpr = new ExprNode(SUBLIST, NULL, $4, declared_clocks, declared_atomic);
    ExprNode *aboveTempExpr = new ExprNode(RESET, tempExpr, $5, declared_clocks, declared_atomic);
    currExpr->setExprDestLeft(aboveTempExpr);
    parExpr = tempExpr;
    delete tempExprC;
    rightExpr = $6;
  }
  vector<pair<short int, short int> > * assignVector = NULL;
  if($6 != NULL) {
    assignVector = new vector<pair<short int, short int> >(0);
    makeAssignmentList($6, assignVector);
  }
  Transition * t = new Transition(parExpr, leftExpr, rightExpr, leftBool, $4, $5, assignVector);
  transList->push_back(t);
  delete assignVector;

};

trans_left_list: /* must be nonempty */
TOK_LPAREN TOK_RPAREN /* Empty left expression indicated by () */
{
    $$ = new ExprNode(BOOL, true, declared_clocks, declared_atomic);
}
| TOK_LPAREN trans_source_list TOK_RPAREN /* State constraints only */
{
    $$ = $2;
}
| TOK_LPAREN guard_list TOK_RPAREN /* Guards only */
{
  $$ = new ExprNode(CONSTRAINT, $2, declared_clocks, declared_atomic);
}
| TOK_LPAREN trans_source_list TOK_COMMA guard_list TOK_RPAREN
/* State and clock constraints */
{
  $$ = new ExprNode(AND, $2, new ExprNode(CONSTRAINT, $4, declared_clocks, declared_atomic), declared_clocks, declared_atomic);
};


trans_source_list: /* Cannot be empty */
trans_atomic
{
  $$ = $1;
}
| trans_source_list TOK_AND trans_source_list
{
   $$ = new ExprNode(AND, $1, $3, declared_clocks, declared_atomic);
}
| trans_source_list TOK_OR trans_source_list
{
   $$ = new ExprNode(OR, $1, $3, declared_clocks, declared_atomic);
}
| TOK_LPAREN trans_source_list TOK_RPAREN
{
   $$ = $2;
};

trans_atomic: /* Cannot be empty */
TOK_ID_ATOMIC TOK_LT TOK_INT
{
  int x = lookup_atomic($1, declared_atomic);
  if( x != -1) {

    $$ = new ExprNode(ATOMIC_LT, x, $3, declared_clocks, declared_atomic);
  }
  else {
    errPrtExit("control variable not declared");
  }
  delete $1;
}
|TOK_ID_ATOMIC TOK_GT TOK_INT
{
  int x = lookup_atomic($1, declared_atomic);
  if( x != -1) {
    $$ = new ExprNode(ATOMIC_GT, x, $3, declared_clocks, declared_atomic);
  }
  else {
    errPrtExit("control variable not declared");
  }
  delete $1;
}
|TOK_ID_ATOMIC TOK_LE TOK_INT
{
  int x = lookup_atomic($1, declared_atomic);
  if( x != -1) {
    $$ = new ExprNode(ATOMIC_LE, x, $3, declared_clocks, declared_atomic);
  }
  else {
    errPrtExit("control variable not declared");
  }
  delete $1;
}
|TOK_ID_ATOMIC TOK_GE TOK_INT
{
  int x = lookup_atomic($1, declared_atomic);
  if( x != -1) {
    $$ = new ExprNode(ATOMIC_GE, x, $3, declared_clocks, declared_atomic);
  }
  else {
    errPrtExit("control variable not declared");
  }
  delete $1;
}
|TOK_ID_ATOMIC TOK_EQ TOK_INT
{
  int x = lookup_atomic($1, declared_atomic);
  if( x != -1) {
    $$ = new ExprNode(ATOMIC, x, $3, declared_clocks, declared_atomic);
  }
  else {
    errPrtExit("control variable not declared");
  }
  delete $1;
}
|TOK_ID_ATOMIC TOK_NEQ TOK_INT
{
  int x = lookup_atomic($1, declared_atomic);
  if( x != -1) {
    $$ = new ExprNode(ATOMIC_NOT, x, $3, declared_clocks, declared_atomic);
  }
  else {
    errPrtExit("control variable not declared");
  }
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
  tt & *($3);
  $$ = new DBM(tt);
  $$->cf();
  delete $1;
  delete $3;
};

trans_dest_list_top: /* empty */ { $$ = NULL;}
| TOK_LPAREN trans_dest_list TOK_RPAREN {$$ = $2;}

trans_dest_list: /* cannot be empty */
TOK_ID_ATOMIC TOK_ASSIGN TOK_INT
{
  int x = lookup_atomic($1, declared_atomic);
  if (x != -1) {
    $$ = new SubstList(x, $3, declared_atomic->size(), declared_atomic);
  }
  else {
    errPrtExit("control variable not defined");
  }
  delete $1;
}
|trans_dest_list TOK_COMMA TOK_ID_ATOMIC TOK_ASSIGN TOK_INT
{
  int x = lookup_atomic($3, declared_atomic);
  if ( x!= -1) {
    $$ = ($1)->addst(x, $5);
  }
  else {
    errPrtExit("control variable not defined");
  }
  delete $3;

};

trans_reset_list_top : /*empty */ {$$ = NULL;}
| TOK_LBRACE trans_reset_list TOK_RBRACE { $$ = $2;};

trans_reset_list: /* cannot be empty */
TOK_ID_CLOCK
{
  int x = lookup_clock($1, declared_clocks);
  if ( x != -1){
    $$ = new ClockSet(x, declared_clocks->size());
  }
  else {
    errPrtExit("clock variable not defined");
  }
  delete $1;
}
|trans_reset_list TOK_COMMA TOK_ID_CLOCK
{
  int x = lookup_clock($3, declared_clocks);
  if ( x!= -1){
    $$ = ($1)->addclock(x);
  }
  else {
    errPrtExit("clock variable not defined");
  }
  delete $3;
};

trans_replace_list_top: /* empty */ {$$ = NULL;}
| TOK_LBRACK trans_replace_list TOK_RBRACK { $$ = $2;};

trans_replace_list: /* cannot be empty */
TOK_LBRACK TOK_ID_CLOCK TOK_ASSIGN TOK_ID_CLOCK TOK_RBRACK
{
  short int x = lookup_clock($2, declared_clocks);
  short int y = lookup_clock($4, declared_clocks);
  $$ = new ExprNode(ASSIGN, new ExprNode(BOOL,true, declared_clocks, declared_atomic),x,y, declared_clocks, declared_atomic);
  delete $2;
  delete $4;
}
|trans_replace_list TOK_COMMA TOK_LBRACK TOK_ID_CLOCK TOK_ASSIGN TOK_ID_CLOCK TOK_RBRACK
{
  short int x = lookup_clock($4, declared_clocks);
  short int y = lookup_clock($6, declared_clocks);
  $$ = new ExprNode(ASSIGN, $1, x, y, declared_clocks, declared_atomic);
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
  invs.push_back($1);
}
|inv_list trans_source_list TOK_IMPLY constraints
{
  ($2)->setDBM($4);
  invs.push_back($2);
};



/** Define is a #define CONST VAL, which
 * allows the user to use constants in the examples. */
define_Decl:
TOK_DEFINE TOK_ID_CONST TOK_INT
{ defcons.insert(make_pair($2,$3));
  // Since the string is not a pointer in defcons, $2 can be deleted
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
    cout << "clocks declared: ";
    print_clocks(cout, declared_clocks);
    cout << endl;
  }
};

/** Take the list of clocks and store then one at a time into the
 * list of clocks. */
clocks_list:
TOK_ID_CLOCK
{ add_clock($1, declared_clocks) ;
  delete $1;
}
| clocks_list TOK_COMMA TOK_ID_CLOCK
{ add_clock($3, declared_clocks);
  delete $3;
};

atomic_Decl:
TOK_ATOMIC TOK_COLON TOK_LBRACE atomic_list TOK_RBRACE
{
  if(debug) {
    cout << "control variable declared: ";
    print_atomic(cout, declared_atomic);
    cout << endl;
  }
};

/** Take the list of atomics (or control propositions)
 * that can take on any integer value.
 * If not assigned a value, each atomic is initially 0. */
atomic_list: /* empty */
{/*do nothing*/}
/* These parts initially give the proposition value 0. */
| TOK_ID_ATOMIC { add_atomic($1, declared_atomic) ; delete $1;}
| TOK_ID_ATOMIC TOK_LPAREN TOK_INT TOK_RPAREN
{
  /* Here the atomic number has the number of values
   * in () - they are for the reader, and can
   * can be ignored by the program. */
  add_atomic($1, declared_atomic) ;
  delete $1;
}
| atomic_list TOK_COMMA TOK_ID_ATOMIC { add_atomic($3, declared_atomic); delete $3; }
| atomic_list TOK_COMMA TOK_ID_ATOMIC TOK_LPAREN TOK_INT TOK_RPAREN {
  /* Here the atomic number has the number of values
   * in () - they are for the reader, and can
   * can be ignored by the program. */
  add_atomic($3, declared_atomic);
  delete $3;
}
/* These next two parts give the atomic the specified
 * initial value */
| TOK_ID_ATOMIC TOK_ASSIGN TOK_INT
{ add_atomicv($1,$3, declared_atomic);
  delete $1;
}
| atomic_list TOK_COMMA TOK_ID_ATOMIC TOK_ASSIGN TOK_INT
{ add_atomicv($3,$5, declared_atomic);
  delete $3;
};

initial_Decl:
TOK_INITIALLY TOK_COLON initial_list
{
  InitC = $3;
  if(debug) {
    cout << "initial condition defined" <<endl;
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
  tt & *($3) ;
  $$ = new DBM(tt);
  $$->cf();
  delete $1;
  delete $3;
};

predicate_Decl:
TOK_PREDICATE TOK_COLON TOK_LBRACE predicate_list TOK_RBRACE
{
  if(debug) {
    cout << "predicate declared: ";
    print_predicates(std::cout, declared_predicates);
    cout << endl;
  }
};

/** Add List of Predicates with their labels. */
predicate_list:
TOK_ID_PREDICATE
{
  add_predicate($1, predicateInd, declared_predicates) ;
  predicateInd++;
  // Do not delete $1 since it has its shallow copy as a predicate
  // However, delete $1 in the ExprNode at the end of the program
}
| predicate_list TOK_COMMA TOK_ID_PREDICATE
{
  add_predicate($3, predicateInd, declared_predicates);
  predicateInd++;
  // Do not delete $3 since it has its shallow copy as a predicate
  // However, delete $3 in the ExprNode at the end of the program
};

start_Decl:
TOK_START TOK_COLON TOK_ID_PREDICATE
{ start_predicate=$3; };

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
  if (add_equation($1,true,$4,$6, declared_predicates)== 0) {
    errPrtExit("predicate vairable not declared");
  }
  delete $4;
}
|TOK_INT TOK_COLON TOK_MU TOK_ID_PREDICATE TOK_ASSIGN expr
{
  if (add_equation($1, false,$4,$6, declared_predicates)== 0) {
    errPrtExit("predicate vairbale not declared");
  }
  delete $4;
};


/** Makes most of the ExprNodes here, parsing the expression
 * in a recursive manner. */
expr:
/** The ( ) requirement for FORALL and EXISTS
 * is used to eliminate shift-reduce conflicts. */
TOK_FORALL TOK_TIME TOK_LPAREN expr TOK_RPAREN
{ $$ = new ExprNode(FORALL, $4, declared_clocks, declared_atomic); }
|TOK_EXISTS TOK_TIME TOK_LPAREN expr TOK_RPAREN
{ $$ = new ExprNode(EXISTS,$4, declared_clocks, declared_atomic); }
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
  $$ = new ExprNode(FORALL_REL, $5, $9, declared_clocks, declared_atomic);
}
/* Simplified EXISTS_REL when relativized expression involves only
 * atomic proposition. */
|TOK_EXISTS TOK_TIME_REL TOK_LBRACK TOK_LBRACE exprProp TOK_RBRACE TOK_RBRACK TOK_LPAREN expr TOK_RPAREN
{
  /* For now, let the operator handle the simplification rather than
   * using a simplified form for atomic propositions */
  $$ = new ExprNode(EXISTS_REL, $5, $9, declared_clocks, declared_atomic);
}
| TOK_FORALL TOK_TIME_REL TOK_LBRACK expr TOK_RBRACK TOK_LPAREN expr TOK_RPAREN
{
  $$ = new ExprNode(FORALL_REL, $4, $7, declared_clocks, declared_atomic);
}
|TOK_EXISTS TOK_TIME_REL TOK_LBRACK expr TOK_RBRACK TOK_LPAREN expr TOK_RPAREN
{

  $$ = new ExprNode(EXISTS_REL, $4, $7, declared_clocks, declared_atomic);
}
|TOK_ALLACT TOK_LPAREN expr TOK_RPAREN
{ $$ = new ExprNode(ALLACT, $3, declared_clocks, declared_atomic); }
|TOK_EXISTACT TOK_LPAREN expr TOK_RPAREN
{ $$ = new ExprNode(EXISTACT,$3, declared_clocks, declared_atomic); }
|expr TOK_OR expr
{ $$ = new ExprNode(OR, $1, $3, declared_clocks, declared_atomic); }
|expr TOK_OR_SIMPLE expr
{ $$ = new ExprNode(OR_SIMPLE, $1, $3, declared_clocks, declared_atomic); }
|expr TOK_AND expr
{
  /* Since both expressions are constraints,
   * intersect the constraints to optimize */
  if ($1->getOpType() == CONSTRAINT && $3->getOpType() == CONSTRAINT){
    /* Copy DBM to eliminate a memory leak */
    DBM * newDBM = new DBM(*($1->dbm()));
    *newDBM & *($3->dbm());
    newDBM->cf();
    $$ = new ExprNode(CONSTRAINT, newDBM, declared_clocks, declared_atomic);
    delete $1;
    delete $3;

  }
  else{
    $$ = new ExprNode(AND, $1, $3, declared_clocks, declared_atomic);
  }
}
| TOK_LBRACE exprProp TOK_RBRACE TOK_OR expr
{ $$ = new ExprNode(OR_SIMPLE, $2, $5, declared_clocks, declared_atomic); }
/** Creates an IMPLY.  Note that this has some restrictions
 * for the user so that expressions are well formed.
 * The program does not check for these restrictions; it
 * just produces the expression. */
|expr TOK_IMPLY expr
{ $$ = new ExprNode(IMPLY, $1, $3, declared_clocks, declared_atomic); }
|constraints
{
  $1->cf();
  $$ = new ExprNode(CONSTRAINT, $1, declared_clocks, declared_atomic);
}
|TOK_ID_PREDICATE
{
  $$ = lookup_predicate($1, declared_predicates);
  if ( $$ == NULL ) {
    errPrtExit("predicate variable not declared");
  }
  delete $1;
}
|atomicProp
{ $$ = $1; }
|TOK_ABLEWAITINF
{
  $$ = new ExprNode(ABLEWAITINF, true, declared_clocks, declared_atomic);
}
|TOK_UNABLEWAITINF
{
  $$ = new ExprNode(UNABLEWAITINF, false, declared_clocks, declared_atomic);
}
/** This segment is the resets, substitutions
 * of atomic proposition values, and assignments
 * of clocks to the value of other clocks. */
|expr TOK_LBRACK reset TOK_RBRACK
{ $$ = new ExprNode(RESET, $1, $3, declared_clocks, declared_atomic); }
|expr TOK_LBRACK sublist TOK_RBRACK
{ $$ = new ExprNode(SUBLIST, $1, $3, declared_clocks, declared_atomic); }
|expr TOK_LBRACK TOK_ID_CLOCK TOK_ASSIGN TOK_ID_CLOCK TOK_RBRACK
{
  short int x = lookup_clock($3, declared_clocks);
  short int y = lookup_clock($5, declared_clocks);
  $$ = new ExprNode(ASSIGN, $1, x, y, declared_clocks, declared_atomic);
  delete $3;
  delete $5;
}
|expr TOK_LBRACK TOK_ID_ATOMIC TOK_ASSIGN TOK_ID_ATOMIC TOK_RBRACK
{
  short int x = lookup_atomic($3, declared_atomic);
  short int y = lookup_atomic($5, declared_atomic);
  $$ = new ExprNode(REPLACE, $1, x, y, declared_clocks, declared_atomic);
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
{ $$ = new ExprNode(OR, $1, $3, declared_clocks, declared_atomic); }
| exprProp TOK_OR_SIMPLE exprProp
{ $$ = new ExprNode(OR_SIMPLE, $1, $3, declared_clocks, declared_atomic); }
| exprProp TOK_AND exprProp
{

  $$ = new ExprNode(AND, $1, $3, declared_clocks, declared_atomic);

}
|TOK_LPAREN exprProp TOK_RPAREN  { $$ = $2 ;}


/* Just atomic propositions */
atomicProp:
TOK_TRUE { $$ = new ExprNode(BOOL, true, declared_clocks, declared_atomic); }
|TOK_FALSE { $$ = new ExprNode(BOOL, false, declared_clocks, declared_atomic); }
/* This next segment of clauses represents the constraints
 * on the atomic (control) propositions. */
|TOK_ID_ATOMIC TOK_LT TOK_INT
{
  int x = lookup_atomic($1, declared_atomic);
  if( x != -1) {
    $$ = new ExprNode(ATOMIC_LT, x, $3, declared_clocks, declared_atomic);
  }
  else {
    errPrtExit("control variable not declared");
  }
  delete $1;
}
|TOK_ID_ATOMIC TOK_GT TOK_INT
{
  int x = lookup_atomic($1, declared_atomic);
  if( x != -1) {
    $$ = new ExprNode(ATOMIC_GT, x, $3, declared_clocks, declared_atomic);
  }
  else {
    errPrtExit("control variable not declared");
  }
  delete $1;
}
|TOK_ID_ATOMIC TOK_LE TOK_INT
{
  int x = lookup_atomic($1, declared_atomic);
  if( x != -1) {
    $$ = new ExprNode(ATOMIC_LE, x, $3, declared_clocks, declared_atomic);
  }
  else {
    errPrtExit("control variable not declared");
  }
  delete $1;
}
|TOK_ID_ATOMIC TOK_GE TOK_INT
{
  int x = lookup_atomic($1, declared_atomic);
  if( x != -1) {
    $$ = new ExprNode(ATOMIC_GE, x, $3, declared_clocks, declared_atomic);
  }
  else {
    errPrtExit("control variable not declared");
  }
  delete $1;
}
|TOK_ID_ATOMIC TOK_EQ TOK_INT
{
  int x = lookup_atomic($1, declared_atomic);
  if( x != -1) {
    $$ = new ExprNode(ATOMIC, x, $3, declared_clocks, declared_atomic);
  }
  else {
    errPrtExit("control variable not declared");
  }
  delete $1;
}
|TOK_ID_ATOMIC TOK_NEQ TOK_INT
{
  int x = lookup_atomic($1, declared_atomic);
  if( x != -1) {
    $$ = new ExprNode(ATOMIC_NOT, x, $3, declared_clocks, declared_atomic);
  }
  else {
    errPrtExit("control variable not declared");
  }
  delete $1;
};

/** Here we find the maximum constant MAXC,
 * the max constant in any constraint involving
 * any clock, and add MAXC as the maximum constant for
 * all DBMs.
 *
 * These rules do not convert the DBM
 * to canonical form (each constraint is just added to the DBM).
 * The parser structure utilizing these rules is responsible
 * for converting the final DBM to canonical form. */
constraints:
TOK_ID_CLOCK TOK_GE TOK_INT
{
  $$ = new DBM(spaceDimension, declared_clocks);
  MAXC = (MAXC < $3) ? $3 : MAXC ;
  int x = lookup_clock($1, declared_clocks);
  if ( x!= -1){
    $$->addConstraint(0, x, ((-$3) <<1) + 1);
  }
  else {
    errPrtExit("clock variable not defined");
  }
  delete $1;
}
|TOK_ID_CLOCK TOK_GE TOK_ID_CONST
{
  $$ = new DBM(spaceDimension, declared_clocks);
  map<string, int>::iterator it = defcons.find($3);
  if (it == defcons.end()) {
    errPrtExit("macro not defined");
  }
  int v = (*it).second;
  MAXC = (MAXC < v) ? v : MAXC ;
  int x = lookup_clock($1, declared_clocks);;
  if ( x!= -1){
    $$->addConstraint(0, x, ((-v) <<1) + 1);
  }
  else {
    errPrtExit("clock variable not defined");
  }
  delete $1;
  delete $3;
}
|TOK_ID_CLOCK TOK_GT TOK_INT
{
  $$ = new DBM(spaceDimension, declared_clocks);
  MAXC = (MAXC < $3) ? $3 : MAXC ;
  int x = lookup_clock($1, declared_clocks);;
  if ( x!= -1){
    $$->addConstraint(0, x, (-$3) <<1);
  }
  else {
    errPrtExit("clock variable not defined");
  }
  delete $1;
}
|TOK_ID_CLOCK TOK_GT TOK_ID_CONST
{
  $$ = new DBM(spaceDimension, declared_clocks);
  map<string, int>::iterator it = defcons.find($3);
  if (it == defcons.end()) {
    errPrtExit("macro not defined");
  }
  int v = (*it).second;
  MAXC = (MAXC < v) ? v : MAXC ;
  int x = lookup_clock($1, declared_clocks);;
  if ( x!= -1){
    $$->addConstraint(0, x, (-v) <<1);
  }
  else {
    errPrtExit("clock variable not defined");
  }
  delete $1;
  delete $3;
}
|TOK_ID_CLOCK TOK_LE TOK_INT
{
  $$ = new DBM(spaceDimension, declared_clocks);
  MAXC = (MAXC < $3) ? $3 : MAXC ;
  int x = lookup_clock($1, declared_clocks);;
  if ( x!= -1){
    $$->addConstraint(x, 0, ($3 <<1) + 1);
  }
  else {
    errPrtExit("clock variable not defined");
  }
  delete $1;
}
|TOK_ID_CLOCK TOK_LE TOK_ID_CONST
{
  $$ = new DBM(spaceDimension, declared_clocks);
  map<string, int>::iterator it = defcons.find($3);
  if (it == defcons.end()) {
    errPrtExit("macro not defined");
  }
  int v = (*it).second;
  MAXC = (MAXC < v) ? v : MAXC ;
  int x = lookup_clock($1, declared_clocks);;
  if ( x!= -1){
    $$->addConstraint(x, 0, (v <<1) + 1);
  }
  else {
    errPrtExit("clock variable not defined");
  }
  delete $1;
  delete $3;
}
|TOK_ID_CLOCK TOK_LT TOK_INT
{
  $$ = new DBM(spaceDimension, declared_clocks);
  MAXC = (MAXC < $3) ? $3 : MAXC ;
  int x = lookup_clock($1, declared_clocks);;
  if ( x!= -1){
    $$->addConstraint(x, 0, ($3 <<1));
  }
  else {
    errPrtExit("clock variable not defined");
  }
  delete $1;
}
|TOK_ID_CLOCK TOK_LT TOK_ID_CONST
{
  $$ = new DBM(spaceDimension, declared_clocks);
  map<string, int>::iterator it = defcons.find($3);
  if (it == defcons.end()) {
    errPrtExit("macro not defined");
  }
  int v = (*it).second;
  MAXC = (MAXC < v) ? v : MAXC ;
  int x = lookup_clock($1, declared_clocks);;
  if ( x!= -1){
    $$->addConstraint(x, 0, (v <<1));
  }
  else {
    errPrtExit("clock variable not defined");
  }
  delete $1;
  delete $3;
}
|TOK_ID_CLOCK TOK_EQ TOK_INT
{
  $$ = new DBM(spaceDimension, declared_clocks);
  MAXC = (MAXC < $3) ? $3 : MAXC ;
  int x = lookup_clock($1, declared_clocks);;
  if ( x!= -1){
    $$->addConstraint(x, 0, ($3 <<1) + 1);
    $$->addConstraint(0, x, ((-$3) <<1) + 1);
  }
  else {
    errPrtExit("clock variable not defined");
  }
  delete $1;
}
|TOK_ID_CLOCK TOK_EQ TOK_ID_CONST
{
  $$ = new DBM(spaceDimension, declared_clocks);
  map<string, int>::iterator it = defcons.find($3);
  if (it == defcons.end()) {
    errPrtExit("macro not defined");
  }
  int v = (*it).second;
  MAXC = (MAXC < v) ? v : MAXC ;
  int x = lookup_clock($1, declared_clocks);;
  if ( x!= -1){
    $$->addConstraint(x, 0, (v <<1) + 1);
    $$->addConstraint(0, x, ((-v) <<1) + 1);
  }
  else {
    errPrtExit("clock variable not defined");
  }
  delete $1;
  delete $3;
}
|TOK_ID_CLOCK TOK_MINUS TOK_ID_CLOCK TOK_GE TOK_INT
{
  $$ = new DBM(spaceDimension, declared_clocks);
  MAXC = (MAXC < $5) ? $5 : MAXC ;
  int x = lookup_clock($1, declared_clocks);;
  int y = lookup_clock($3, declared_clocks);;
  if ( x != -1 && y != -1) {
    $$->addConstraint(y, x, ((-$5) <<1) + 1);
  }
  else {
    errPrtExit("clock variable not defined");
  }
  delete $1;
  delete $3;
}
|TOK_ID_CLOCK TOK_MINUS TOK_ID_CLOCK TOK_GT TOK_INT
{
  $$ = new DBM(spaceDimension, declared_clocks);
  MAXC = (MAXC < $5) ? $5 : MAXC ;
  int x = lookup_clock($1, declared_clocks);;
  int y = lookup_clock($3, declared_clocks);;
  if ( x != -1 && y != -1) {
    $$->addConstraint(y, x, (-$5) <<1);
  }
  else {
    errPrtExit("clock variable not defined");
  }
  delete $1;
  delete $3;
}
|TOK_ID_CLOCK TOK_MINUS TOK_ID_CLOCK TOK_LE TOK_INT
{
  $$ = new DBM(spaceDimension, declared_clocks);
  MAXC = (MAXC < $5) ? $5 : MAXC ;
  int x = lookup_clock($1, declared_clocks);;
  int y = lookup_clock($3, declared_clocks);;
  if ( x != -1 && y != -1) {
    $$->addConstraint(x, y, ($5 <<1) + 1);
  }
  else {
    errPrtExit("clock variable not defined");
  }
  delete $1;
  delete $3;
}
|TOK_ID_CLOCK TOK_MINUS TOK_ID_CLOCK TOK_LT TOK_INT
{
  $$ = new DBM(spaceDimension, declared_clocks);
  MAXC = (MAXC < $5) ? $5 : MAXC ;
  int x = lookup_clock($1, declared_clocks);;
  int y = lookup_clock($3, declared_clocks);;
  if ( x != -1 && y != -1) {
    $$->addConstraint(x, y, ($5 <<1));
  }
  else {
    errPrtExit("clock variable not defined");
  }
  delete $1;
  delete $3;
}
|TOK_ID_CLOCK TOK_MINUS TOK_ID_CLOCK TOK_EQ TOK_INT
{
  $$ = new DBM(spaceDimension, declared_clocks);
  MAXC = (MAXC < $5) ? $5 : MAXC ;
  int x = lookup_clock($1, declared_clocks);;
  int y = lookup_clock($3, declared_clocks);;
  if ( x != -1 && y != -1){
    $$->addConstraint(x, y, ($5 <<1) + 1);
    $$->addConstraint(y, x, ((-$5) <<1) + 1);
  }
  else {
    errPrtExit("clock variable not defined");
  }
  delete $1;
  delete $3;
};

/** Generates the set of clocks that needs to be reset
 * as a ClockSet object. */
reset:      TOK_ID_CLOCK
{
  int x = lookup_clock($1, declared_clocks);;
  if ( x != -1){
    $$ = new ClockSet(x, declared_clocks->size());
  }
  else {
    errPrtExit("clock variable not defined");
  }
  delete $1;
}
|TOK_ID_CLOCK TOK_COMMA reset
{
  int x = lookup_clock($1, declared_clocks);;
  if ( x!= -1){
    $$ = ($3)->addclock(x);
  }
  else {
    errPrtExit("clock variable not defined");
  }
  delete $1;
};

/** Generate the list of proposition substitutions. */
sublist:   TOK_ID_ATOMIC TOK_ASSIGN TOK_INT
{
  int x = lookup_atomic($1, declared_atomic);
  if (x != -1) {
    $$ = new SubstList(x, $3, declared_atomic->size(), declared_atomic);
  }
  else {
    errPrtExit("control variable not defined");
  }
  delete $1;
}
|TOK_ID_ATOMIC TOK_ASSIGN TOK_INT TOK_COMMA sublist
{
  int x = lookup_atomic($1, declared_atomic);
  if ( x!= -1) {
    $$ = ($5)->addst(x, $3);
  }
  else {
    errPrtExit("control variable not defined");
  }
  delete $1;
};


