/** \file ExprNode.cc
 * Source file for proof classes: Sequents, Expressions and Transitions.
 * This file contains some additional methods not in the header file.
 * @author Peter Fontana, Dezhuang Zhang, and Rance Cleaveland. 
 * @note Many functions are inlined for better performance.
 * @version 1.21
 * @date November 8, 2013 */

#include <iostream>
#include <string>
#include <map>
#include "ExprNode.hh"

using namespace std;

/** A variable representing the line number. */
extern  int yyline;
/** The number of errors (syntax or otherwise) in the expressions.
 * I believe the inital value is 0. */
int numErrs;
/** The number of clocks in the timed automata, including the dummy
 * "zero clocks". Hence, a DBM with n clocks has spaceDimension value n + 1
 * (the first clock is the zero clock). */
int spaceDimension;

/** A Hash Table of clocks used to store the clocks (clock IDs). */
map <string, int> clocks;
/** A Hash table of Atomic values used to store predicate
 * and/or control variable ids */
map <string, int> atomic;
/** A Hash table of ints storing integer 
 * substituations for atomic variables. 
 * This maps atomic ids to atomic values.  0 is the default value.
 * This map represents the initial "state" of the model*/
map <int, int> InitSub;
/** A Hash table storing the list of declared predicates,
 * matching their label with their expression. */
map <string, ExprNode *> predicates;
/** A Hash table storing a list of PES, with their labels
 * and their expressions. */
map <string, ExprNode *> equations;


/** Assuming that e is a chain of ASSIGN expressions (possibly ending
 * with a BOOL expression, this converts that expression to an ordered
 * list of clock assignments. The innermost assignments are at the back
 * of the vector.
 * @param e (*) the pointer to the expression of clock assignments.
 * @param av (*) the pointer to the vector of clock assignments.
 * @return None. When finished, av is changed to be the vector of 
 * clock assignments.  */
void makeAssignmentList(ExprNode *e, vector<pair<short int,short int> > * av) {
  pair<short int,short int> p;
  switch (e->getOpType()){
    case ASSIGN:
      p.first=e->getAtomic();
      p.second=e->getIntVal();
      av->push_back(p);
      makeAssignmentList(e->getExpr(), av); 
      break;
    case BOOL: // terminal node
      break;
    default: // should not get here
      break;
  }

}

/** Adds a clock with a desired string label
 * to the current list of all clocks.
 * @param s (*) The string that is the clock label.
 * @return 1:when finished. */
int add_clock(const char *s)
{ 
  string name(s);
  clocks.insert(make_pair(name,clocks.size()+1));
  spaceDimension = clocks.size() + 1;
  return 1;
}

/** Determines if a clock with label s is already in
 * the list of clocks and gets its index if it is.
 * @param s (*) The label to search for
 * @return the int value of the clock index: if it is in the list;
 * -1: otherwise (s is not a clock). */
int lookup_clock(const char *s)
{
  string name(s);
  map<string, int>::iterator it = clocks.find(name);
  if (it != clocks.end())
    return (*it).second;
  else
    return -1;
}

/** Prints out the list of clocks with their labels
 * and current values.
 * @return 1 when done. */
int print_clocks()
{
  map <string, int>::iterator it;
  for (it = clocks.begin(); it != clocks.end(); it++)
    cout << (*it).first <<":"<< (*it).second <<"  ";
  return 1;	
}

/** Insert an atomic variable with label s
 * into the list of atomic variables and give it an id.
 * This gives the atomic variable the default value of 0.
 * @param s (*) The label for the atomic value.
 * @return 1 when done. */
int add_atomic(const char *s)
{
  string name(s);
  int idx = atomic.size();
  atomic.insert(make_pair(name, idx));
  InitSub.insert(make_pair(idx, 0));
  return 1;
}

/** Insert an atomic variable with label s and initial value
 * v into the list of atomic variables and give it an id.
 * This method gives the atomic variable the use-specified value i.
 * @param s (*) The label for the atomic value.
 * @param v The value of the atomic variable labeled by s.
 * @return 1 when done. */
int add_atomicv(const char *s, const int v)
{
  string name(s);
  int idx = atomic.size();
  atomic.insert(make_pair(name, idx));
  InitSub.insert(make_pair(idx, v));
  return 1;
}

/** Try to find the value of the atomic variable with label s
 * in the atomic list.
 * @param s (*) The label for the atomic value to look up.
 * @return the value of the atomic label if found or -1 if it is
 * not in the list. */
int lookup_atomic(const char *s)
{
  string name(s);
  map<string, int>::iterator it = atomic.find(name);
  if (it != atomic.end())
    return (*it).second;
  else
    return -1;
}

/** Prints out the list of atomic variables with their
 * labels (ids) and values.
 * @return 1 when done. */
int print_atomic()
{
  map <string, int>::iterator it;
  for (it = atomic.begin(); it != atomic.end(); it++)
    cout << (*it).first << ":" << (*it).second << "  ";
  return 1;	
}

/** Adds an empty PREDICATE expression to the list of
 * predicates. This list is later used to conjunct
 * equation expressions to these PREDICATE variables, providing a clean
 * way to terminate a predicate expression terminated due to circularity.
 * @note This method is only used in the parser (pes.y)
 * when forming ExprNode trees.
 * @param s The label of the predicate to add.
 * @param i The integer index of the predicate.
 * @return 1 when done. */
int add_predicate(const char *s, const int i)
{
  string name(s);
  predicates.insert(make_pair(name, (new ExprNode(PREDICATE, s, i))));
  return 1;
} 

/** Sets or changes the parity and the block number of a given
 * predicate ExprNode in the list of predicates.
 * @param name The key to look up the ExprNode in the ExprNode list
 * @param block The desired block number of the equation (predicate expression)
 * @param parity The desired parity: true = gfp, false = lfp.
 * @return true:if successful (found the predicate expression), 
 * false:otherwise. */
bool set_parity_block(const string& name, const int block, const bool parity)
{
  map<string, ExprNode *>::iterator it = predicates.find(name);
  if (it != predicates.end()){
    (*it).second->set_Parity(parity);
    (*it).second->set_Block(block);
    return true;
  }   
  else
    return false;
  
}

/** Adds an an equation, with its variable name and right hand side, to
 * the list of equations. This list links predicate variable expressions
 * with their right hand side equations. This separation of
 * predicates from equations provides a clean
 * way to terminate a predicate expression terminated due to circularity
 * and a clean way to delete expressions. 
 * @param block The block number for the equation.
 * @param parity The equation's parity: true = gfp, false = lfp.
 * @param s (*) The equation label.
 * @param e (*) The expression of the RHS of the equation.
 * @return 1 if successful in doing so and 0 otherwise. */
int add_equation(const int block, const bool parity, const char *s, ExprNode *e)
{
  string name(s);
  if(set_parity_block(name, block, parity)){
    equations.insert(make_pair(name, e));
    return 1;
  }
  else
    return 0;
}


/** Looks up a predicate with label s and returns the expression in
 * the list if it is there and NULL otherwise.
 * @param s (*) The label of the predicate to look up.
 * @return The reference to the Expression that the predicate is if in the
 * list and NULL otherwise. */
ExprNode * lookup_predicate(const char *s)
{
  string name(s);
  map<string, ExprNode *>::iterator it = predicates.find(name);
  if (it != predicates.end())
    return (*it).second;
  else
    return NULL;
}

/** Tries to find the RHS expression of an equation with a given predicate
 * variable label,
 * and returns the equation, or NULL if there is no such equation.
 * @param s (*) The label of the equation.
 * @return The Expression (a reference) if found in the list, or NULL if not
 * found in the list of equations. */
ExprNode * lookup_equation(const char *s)
{
  string name(s);
  map<string, ExprNode *>::iterator it = equations.find(name);
  if (it != equations.end())
    return (*it).second;
  else
    return NULL;
}

/** Prints out an error if it occurs during the parsing process. 
 * This method is only used in the parser.
 * @param s (*) The error string to print out.
 * @return None */
void
yyerror(char *s)
{
  cerr << " line " << yyline << ": ";
  if (s == NULL) cerr << "syntax error";
  else cerr << s;
  cerr << endl;
  numErrs++;
}


/** Prints out the list of predicate variables (without their right hand
 * side equations).  
 * @return 1 when done. */
int print_predicates()
{
  map <string, ExprNode *>::iterator it;
  for (it = predicates.begin(); it != predicates.end(); it++){    
    cout << (*it).first << "  "; 
    cout << "ind: " << ((*it).second)->getIntVal() << "  ";
  }
  return 1;	
}



/** Prints out a sequent in a proof tree.
 * @param step The tree level (sequent step) of the sequent (0 is root).
 * @param retVal The current value of the sequent (true or false).
 * @param lhs (*) The left hand clock state.
 * @param rhs (*) The right hand side of the sequent.
 * @param sub (*) The left hand discrete state.
 * @param op The Expression type of the proof rule; this is the rule that the
 * model checker applies to continue the proof.
 * @return None */
void print_sequent(const int step, const bool retVal, DBM *lhs, ExprNode *rhs, SubstList *sub, const opType op){
  cout << "seq#" << step << "  " <<retVal << "  ";
  if (lhs != NULL) {
    lhs->print_constraint() ;
  }
  if (sub != NULL) {
    cout << ", ";
    sub->print(cout);
  }
  cout << "\t|-  " ;
  if (rhs != NULL) {
    print_ExprNode(rhs, cout);
  }
  cout << "\t";
  print_ExprNodeType(op, cout);
  
  cout << endl;
}

/** Prints out a placeholder check sequent in the proof tree; used for
 * the exists sub-branch that checks (and restricts) the obtained placeholder
 * from the other branch of exists.
 * @param step The tree level (sequent step) of the sequent (0 is root).
 * @param retVal The current value of the sequent (true or false).
 * @param lhs (*) The left hand clock state.
 * @param rhsList (*) The right hand side; the obtained placeholder.
 * @param sub (*) The left hand discrete state.
 * @param op The Expression type of the proof rule; this is the rule that the
 * model checker applies to continue the proof.
 * @return None */
void print_sequentCheck(const int step, const bool retVal, DBM *lhs, DBMList *rhsList, SubstList *sub, const opType op){
  cout << "seq#" << step << "  " <<retVal << "  ";
  if (lhs != NULL) {
    lhs->print_constraint() ;
  }
  if (sub != NULL) {
    cout << ", ";
    sub->print(cout);
  }
  cout << "\t|-  " ;
  if (rhsList != NULL) {
    rhsList->print_constraint();
  }
  cout << "\t";
  print_ExprNodeType(op, cout);
  
  cout << endl;
}

/** Prints out a sequent with a placeholder clock state in a proof tree.
 * @param step The tree level (sequent step) of the sequent (0 is root).
 * @param retVal The current value of the sequent (true or false).
 * @param lhs (*) The left hand clock state.
 * @param place (*) The left hand placeholder clock state.
 * @param rhs (*) The right hand side of the sequent.
 * @param sub (*) The left hand discrete state.
 * @param op The Expression type of the proof rule; this is the rule that the
 * model checker applies to continue the proof.
 * @return None */
void print_sequent_place(const int step, const bool retVal, DBM *lhs, DBMList * place, ExprNode *rhs, SubstList *sub, const opType op){
  cout << "seq#" << step << "  " <<retVal << "  ";
  if (lhs != NULL) {
    lhs->print_constraint() ;
  }
  if (place != NULL) {
  	cout << " plhold: {";
  	place->print_constraint();
  	cout << "}";
  }
  if (sub != NULL) {
    cout << ", ";
    sub->print(cout);
  }
  cout << "\t|-  " ;
  if (rhs != NULL) {
    print_ExprNode(rhs, cout);
  }
  cout << "\t";
  print_ExprNodeTypePlace(op, cout);
  cout << endl;
}

/** Prints out a placeholder check sequent in the proof tree; used for
 * exists, forall and reset sequents within placeholder proofs. This check
 * takes the placeholder found in the left branch and restricts it to form
 * a (smaller) but valid placeholder to push up the tree.
 * @param step The tree level (sequent step) of the sequent (0 is root).
 * @param retVal The current value of the sequent (true or false).
 * @param lhs (*) The left hand clock state.
 * @param place (*) The left hand placeholder clock state.
 * @param rhsList (*) The right hand side; the obtained placeholder.
 * @param sub (*) The left hand discrete state.
 * @param op The Expression type of the proof rule; this is the rule that the
 * model checker applies to continue the proof.
 * @return None */
void print_sequent_placeCheck(const int step, const bool retVal, DBM *lhs, DBMList * place, DBMList *rhsList, SubstList *sub, const opType op){
  cout << "seq#" << step << "  " <<retVal << "  ";
  if (lhs != NULL) {
    lhs->print_constraint() ;
  }
  if (place != NULL) {
  	cout << " plhold: {";
  	place->print_constraint();
  	cout << "}";
  }
  if (sub != NULL) {
    cout << ", ";
    sub->print(cout);
  }
  cout << "\t|-  " ;
  if (rhsList != NULL) {
    rhsList->print_constraint();
  }
  cout << "\t";
  print_ExprNodeTypePlace(op, cout);
  cout << endl;
}

/** Prints out the expression to the desired output stream, labeling
 * the expression with its opType. The typical output stream is cout.
 * @param e (*) The expression to print out.
 * @param os (&) The type of output stream to print the output to.
 * @return None */
void print_ExprNode(ExprNode * e, std::ostream& os)
{
  switch (e->getOpType()){
    case PREDICATE:
      os << e->getPredicate() ; 
      break;
    case FORALL:
      os << "FORALL.[";
      print_ExprNode(e->getQuant(),os);
      os << "]";
      break;
    case EXISTS:
      os << "EXISTS.[";
      print_ExprNode(e->getQuant(), os); 
      os << "]";
      break;
    case FORALL_REL:
      os << "FORALLREL.(";
      print_ExprNode(e->getLeft(),os);
      os << ")[";
      print_ExprNode(e->getRight(),os);
      os << "]";
      break;
    case EXISTS_REL:
      os << "EXISTSREL.(";
      print_ExprNode(e->getLeft(),os);
      os << ")[";
      print_ExprNode(e->getRight(),os);
      os << "]";
      break;
    case ALLACT:
      os << "ALLACT.[";
      print_ExprNode(e->getQuant(),os);
      os << "]";
      break;
    case EXISTACT:
      os << "EXISTACT.[";
      print_ExprNode(e->getQuant(),os);
      os << "]";
      break;
    case AND:
      os << "(";
      print_ExprNode(e->getLeft(), os); 
      os << " AND ";
      print_ExprNode(e->getRight(), os); 
      os << ")";
      break;
    case OR:
      cout << "(";
      print_ExprNode(e->getLeft(), os); 
      os << " OR ";
      print_ExprNode(e->getRight(), os); 
      cout << ")";
      break;
    case OR_SIMPLE:
      cout << "(";
      print_ExprNode(e->getLeft(), os); 
      os << " OR_S ";
      print_ExprNode(e->getRight(), os); 
      cout << ")";
      break;
    case IMPLY:
      os << "-(-";
      print_ExprNode(e->getLeft(), os);
      os << " IMPLY ";
      print_ExprNode(e->getRight(), os);
      os << "-)-";
      break;
    case RESET:
      print_ExprNode(e->getExpr(), os);
      e->getClockSet()->print(os);
      break;
    case REPLACE:
      print_ExprNode(e->getExpr(), os);
      os << "p" << (e->getAtomic());
      os << ":=";
      os << e->getIntVal();
      break;
    case CONSTRAINT:
      e->dbm()->print_constraint();
      break;
    case ATOMIC:
      os << "p" << (e->getAtomic());
      os << "==";
      os << e->getIntVal();
      break;
    case ATOMIC_NOT:
      os << "p" << (e->getAtomic());
      os << "!=";
      os << e->getIntVal();
      break;
    case ATOMIC_LT:
      os << "p" << (e->getAtomic());
      os << "<";
      os << e->getIntVal();
      break;
    case ATOMIC_GT:
      os << "p" << (e->getAtomic());
      os << ">";
      os << e->getIntVal();
      break;
    case ATOMIC_LE:
      os << "p" << (e->getAtomic());
      os << "<=";
      os << e->getIntVal();
      break;
    case ATOMIC_GE:
      os << "p" << (e->getAtomic());
      os << ">=";
      os << e->getIntVal();
      break;
    case BOOL:
      os << ((e->getBool())? "TRUE" : "FALSE");
      break;
    case SUBLIST:
      print_ExprNode(e->getExpr(), os);
      e->getSublist()->print(os);
      break;
    case ASSIGN:
      print_ExprNode(e->getExpr(), os);
      os << "[";
      os << "x" << (e->getcX());
      os << "==";
      os << "x" << (e->getcY());
      os << "]";
      break;
    case ABLEWAITINF:
      os << "AbleWaitInf";
      break;
    case UNABLEWAITINF:
      os << "UnableWaitInf";
      break;
  }
  
}

/** Prints out the expression type (opType) to the desired output stream.
 * The typical output stream is cout.
 * @param op (*) The expression type.
 * @param os (&) The type of output stream to print the output to.
 * @return none */
void print_ExprNodeType(const opType op, std::ostream& os)
{
  os << "**(";
  switch (op){
    case PREDICATE:
      os << "PREDICATE";
      break;
    case FORALL:
      os << "FORALL";
      break;
    case EXISTS:
      os << "EXISTS - P";
      break;
    case FORALL_REL:
      os << "FORALLREL";
      break;
    case EXISTS_REL:
      os << "EXISTSREL - P";
      break;
    case ALLACT:
      os << "ALLACT";
      break;
    case EXISTACT:
      os << "EXISTACT";
      break;
    case AND:
      os << "AND - B";
      break;
    case OR:
      os << "OR - B";
      break;
    case OR_SIMPLE:
      os << "OR_S - B";
      break;
    case IMPLY:
      os << "IMPLY";
      break;
    case RESET:
      os << "RESET";
      break;
    case REPLACE:
      os << "REPLACE";
      break;
    case CONSTRAINT:
      os << "CONSTRAINT";
      break;
    case ATOMIC:
      os << "ATOMIC ==";
      break;
    case ATOMIC_NOT:
      os << "ATOMIC !=";
      break;
    case ATOMIC_LT:
      os << "ATOMIC <";
      break;
    case ATOMIC_GT:
      os << "ATOMIC >";
      break;
    case ATOMIC_LE:
      os << "ATOMIC <=";
      break;
    case ATOMIC_GE:
      os << "ATOMIC >=";
      break;
    case BOOL:
      os << "BOOL";
      break;
    case SUBLIST:
      os << "SUBLIST";
      break;
    case ASSIGN:
      os << "ASSIGN";
      break;
    case ABLEWAITINF:
      os << "ABLEWAITINF";
      break;
    case UNABLEWAITINF:
      os << "UNABLEWAITINF";
      break;
  }
  os << ")**";
}


/** Prints out the expression type (opType), for expressions
 * with placeholders, to the desired output stream.
 * The typical output stream is cout. This method is used for
 * expression types within proof subtrees with placehloders.
 * @param op (*) The expression type.
 * @param os (&) The type of output stream to print the output to.
 * @return none */
void print_ExprNodeTypePlace(const opType op, std::ostream& os)
{
  os << "**(";
  switch (op){
    case PREDICATE:
      os << "PREDICATE";
      break;
    case FORALL:
      os << "FORALL - P2";
      break;
    case EXISTS:
      os << "EXISTS - P2";
      break;
    case FORALL_REL:
      os << "FORALLREL - P2";
      break;
    case EXISTS_REL:
      os << "EXISTSREL - P2";
      break;
    case ALLACT:
      os << "ALLACT - B";
      break;
    case EXISTACT:
      os << "EXISTACT - B";
      break;
    case AND:
      os << "AND - B";
      break;
    case OR:
      os << "OR - B";
      break;
    case OR_SIMPLE:
      os << "OR_S - B";
      break;
    case IMPLY:
      os << "IMPLY";
      break;
    case RESET:
      os << "RESET - P2";
      break;
    case REPLACE:
      os << "REPLACE - B";
      break;
    case CONSTRAINT:
      os << "CONSTRAINT";
      break;
    case ATOMIC:
      os << "ATOMIC ==";
      break;
    case ATOMIC_NOT:
      os << "ATOMIC !=";
      break;
    case ATOMIC_LT:
      os << "ATOMIC <";
      break;
    case ATOMIC_GT:
      os << "ATOMIC >";
      break;
    case ATOMIC_LE:
      os << "ATOMIC <=";
      break;
    case ATOMIC_GE:
      os << "ATOMIC >=";
      break;
    case BOOL:
      os << "BOOL";
      break;
    case SUBLIST:
      os << "SUBLIST";
      break;
    case ASSIGN:
      os << "ASSIGN";
      break;
    case ABLEWAITINF:
      os << "ABLEWAITINF";
      break;
    case UNABLEWAITINF:
      os << "UNABLEWAITINF";
      break;
  }
  os << ")**";
}



/** Prints the contents of the SubstList.  -1 is considered
 * to be empty. 
 * @param os (&) The output stream to print the output to
 * @return none. */
void SubstList::print(std::ostream &os){ 
  bool end =false;
  os << "[";
  for(int i = 0; i < quantity; i++){
    if (this->operator[](i) != -1){
      if(end) os <<",";
      os << "p" << i;
      os <<"=" << this->operator[](i);
      end = true;
    }
  }
  os << "]";
}

/** Prints the specified integer (in base 10) in
 * its binary equivalent.
 * @param val The integer in base 10 to print.
 * @return none */
void printBinary(const int val) {
  for(int i = 15; i >=0; i--){
    if (val & (1 << i))
      std::cout <<"1";
    else std::cout <<"0";
  }   
}

/** Prints out the fed in expression node to the fed in
 * output stream with a specified indentation (which doesn't seem
 * to be used: used in printing of transitions. 
 * @param e (*) The ExprNode to print out.
 * @param os (&) The type of output stream to print the output to.
 * @return none */
void print_ExprNodeTrans(ExprNode * e, std::ostream& os)
{
  if(e != NULL) {
    switch (e->getOpType()){
      case PREDICATE:
        os << e->getPredicate() ; 
        break;
      case FORALL:
        os << "FORALL.[";
        print_ExprNodeTrans(e->getQuant(),os);
        os << "]";
        break;
      case EXISTS:
        os << "EXISTS.[";
        print_ExprNodeTrans(e->getQuant(), os); 
        os << "]";
        break;
      case FORALL_REL:
        os << "FORALLREL.(";
        print_ExprNodeTrans(e->getLeft(),os);
        os << ")[";
        print_ExprNodeTrans(e->getRight(),os);
        os << "]";
        break;
      case EXISTS_REL:
        os << "EXISTSREL.(";
        print_ExprNodeTrans(e->getLeft(),os);
        os << ")[";
        print_ExprNodeTrans(e->getRight(),os);
        os << "]";
        break;
      case ALLACT:
        os << "ALLACT.[";
        print_ExprNodeTrans(e->getQuant(),os);
        os << "]";
        break;
      case EXISTACT:
        os << "EXISTACT.[";
        print_ExprNodeTrans(e->getQuant(),os);
        os << "]";
        break;
      case AND:
        print_ExprNodeTrans(e->getLeft(), os); 
        os << " && ";
        print_ExprNodeTrans(e->getRight(), os); 
        break;
      case OR:
        cout << "(";
        print_ExprNodeTrans(e->getLeft(), os); 
        os << " OR ";
        print_ExprNodeTrans(e->getRight(), os); 
        cout << ")";
        break;
      case OR_SIMPLE:
        cout << "(";
        print_ExprNodeTrans(e->getLeft(), os); 
        os << " OR_S ";
        print_ExprNodeTrans(e->getRight(), os); 
        cout << ")";
        break;
      case IMPLY:
        print_ExprNodeTrans(e->getLeft(), os);
        os << " IMPLY ";
        print_ExprNodeTrans(e->getRight(), os);
        break;
      case RESET:
        print_ExprNodeTrans(e->getExpr(), os);
        e->getClockSet()->print(os);
        break;
      case REPLACE:
        print_ExprNodeTrans(e->getExpr(), os);
        os << "p" << (e->getAtomic());
        os << ":=";
        os << e->getIntVal();
        break;
      case CONSTRAINT:
        e->dbm()->print_constraint();
        break;
      case ATOMIC:
        os << "p" << (e->getAtomic());
        os << "==";
        os << e->getIntVal();
        break;
      case ATOMIC_NOT:
        os << "p" << (e->getAtomic());
        os << "!=";
        os << e->getIntVal();
        break;
      case ATOMIC_LT:
        os << "p" << (e->getAtomic());
        os << "<";
        os << e->getIntVal();
        break;
      case ATOMIC_GT:
        os << "p" << (e->getAtomic());
        os << ">";
        os << e->getIntVal();
        break;
      case ATOMIC_LE:
        os << "p" << (e->getAtomic());
        os << "<=";
        os << e->getIntVal();
        break;
      case ATOMIC_GE:
        os << "p" << (e->getAtomic());
        os << ">=";
        os << e->getIntVal();
        break;
      case BOOL:
        os << ((e->getBool())? "TRUE" : "FALSE");
        break;
      case SUBLIST:
        print_ExprNodeTrans(e->getExpr(), os);
        e->getSublist()->print(os);
        break;
      case ASSIGN:
        print_ExprNodeTrans(e->getExpr(), os);
        os << "[";
        os << "x" << (e->getcX());
        os << "==";
        os << "x" << (e->getcY());
        os << "]";
        break;
      case ABLEWAITINF:
        os << "AbleWaitInf";
        break;
      case UNABLEWAITINF:
        os << "UnableWaitInf";
        break;
    }
  }
}

/** Prints out the transition to the desired output stream.
 * The typical output stream is cout.
 * @param t (*) The transition to print.
 * @param os (&) The type of output stream to print the output to.
 * @return none */
void print_Transition(Transition * t, std::ostream& os)
{
  ExprNode * leftExpr = t->getLeftExpr();
  ExprNode * rightExpr = t->getRightExpr();
  if(leftExpr != NULL) {
    print_ExprNodeTrans(leftExpr, os);
  }
  os << "->";
  if(rightExpr != NULL) {
    print_ExprNodeTrans(rightExpr, os);
  }
}


