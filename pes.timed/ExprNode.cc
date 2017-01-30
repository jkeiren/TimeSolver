/** \file ExprNode.cc
 * Source file for proof classes: Sequents, Expressions and Transitions.
 * This file contains some additional methods not in the header file.
 * @author Peter Fontana, Dezhuang Zhang, and Rance Cleaveland. 
 * @note Many functions are inlined for better performance.
 * @version 1.21
 * @date November 8, 2013 */

#include <cassert>
#include <iostream>
#include <string>
#include <sstream>
#include <map>
#include "bidirectional_map.hh"
#include "ExprNode.hh"

using namespace std;

/** Assuming that e is a chain of ASSIGN expressions (possibly ending
 * with a BOOL expression, this converts that expression to an ordered
 * list of clock assignments. The innermost assignments are at the back
 * of the vector.
 * @param e (*) the pointer to the expression of clock assignments.
 * @param av (*) the pointer to the vector of clock assignments.
 * @return None. When finished, av is changed to be the vector of
 * clock assignments.  */
void makeAssignmentList(const ExprNode * const e, vector<pair<short int,short int> > * av) {
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

/** Lookup the name of the clock with id n */
const string& lookup_clock_name(const unsigned int n, const bidirectional_map <string, int>& declared_clocks)
{
  return declared_clocks.reverse_at(n);
}

/** Lookup the name of the atomic with id n */
const string& lookup_atomic_name(const unsigned int n, const bidirectional_map<std::string, int>& declared_atomic)
{
  return declared_atomic.reverse_at(n);
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
void print_sequent(std::ostream& os, const int step, const bool retVal, const DBM * const lhs,
                   const ExprNode * const rhs, const SubstList * const sub, const opType op){
  os << "seq#" << step << "  " <<retVal << "  ";
  if (lhs != NULL) {
    lhs->print_constraint(os) ;
  }
  if (sub != NULL) {
    os << ", ";
    sub->print(os);
  }
  os << "\t|-  " ;
  if (rhs != NULL) {
    print_ExprNode(rhs, os);
  }
  os << "\t";
  print_ExprNodeType(op, os);

  os << endl;
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
void print_sequentCheck(std::ostream& os, const int step, const bool retVal, const DBM * const lhs,
                        const DBMList * const rhsList, const SubstList * const sub, const opType op){
  os << "seq#" << step << "  " <<retVal << "  ";
  if (lhs != NULL) {
    lhs->print_constraint(os) ;
  }
  if (sub != NULL) {
    os << ", ";
    sub->print(os);
  }
  os << "\t|-  " ;
  if (rhsList != NULL) {
    rhsList->print_constraint(os);
  }
  os << "\t";
  print_ExprNodeType(op, os);

  os << endl;
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
void print_sequent_place(std::ostream& os, const int step, const bool retVal, const DBM * const lhs,
                         const DBMList * const place, const ExprNode * const rhs,
                         const SubstList * const sub, const opType op){
  os << "seq#" << step << "  " <<retVal << "  ";
  if (lhs != NULL) {
    lhs->print_constraint(os) ;
  }
  if (place != NULL) {
    os << " plhold: {";
    place->print_constraint(os);
    os << "}";
  }
  if (sub != NULL) {
    os << ", ";
    sub->print(os);
  }
  os << "\t|-  " ;
  if (rhs != NULL) {
    print_ExprNode(rhs, os);
  }
  os << "\t";
  print_ExprNodeTypePlace(op, os);
  os << endl;
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
void print_sequent_placeCheck(std::ostream& os, const int step, const bool retVal, const DBM * const lhs,
                              const DBMList * const place, const DBMList * const rhsList,
                              const SubstList * const sub, const opType op){
  os << "seq#" << step << "  " <<retVal << "  ";
  if (lhs != NULL) {
    lhs->print_constraint(os) ;
  }
  if (place != NULL) {
    os << " plhold: {";
    place->print_constraint(os);
    os << "}";
  }
  if (sub != NULL) {
    os << ", ";
    sub->print(os);
  }
  os << "\t|-  " ;
  if (rhsList != NULL) {
    rhsList->print_constraint(os);
  }
  os << "\t";
  print_ExprNodeTypePlace(op, os);
  os << endl;
}

/** Prints out the expression to the desired output stream, labeling
 * the expression with its opType. The typical output stream is os.
 * @param e (*) The expression to print out.
 * @param os (&) The type of output stream to print the output to.
 * @return None */
void print_ExprNode(const ExprNode * const e, std::ostream& os)
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
      os << "(";
      print_ExprNode(e->getLeft(), os);
      os << " OR ";
      print_ExprNode(e->getRight(), os);
      os << ")";
      break;
    case OR_SIMPLE:
      os << "(";
      print_ExprNode(e->getLeft(), os);
      os << " OR_S ";
      print_ExprNode(e->getRight(), os);
      os << ")";
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
      os << lookup_atomic_name(e->getAtomic(), e->declared_atomic);
      os << ":=";
      os << e->getIntVal();
      break;
    case CONSTRAINT:
      e->dbm()->print_constraint(os);
      break;
    case ATOMIC:
      os << lookup_atomic_name(e->getAtomic(), e->declared_atomic);
      os << "==";
      os << e->getIntVal();
      break;
    case ATOMIC_NOT:
      os << lookup_atomic_name(e->getAtomic(), e->declared_atomic);
      os << "!=";
      os << e->getIntVal();
      break;
    case ATOMIC_LT:
      os << lookup_atomic_name(e->getAtomic(), e->declared_atomic);
      os << "<";
      os << e->getIntVal();
      break;
    case ATOMIC_GT:
      os << lookup_atomic_name(e->getAtomic(), e->declared_atomic);
      os << ">";
      os << e->getIntVal();
      break;
    case ATOMIC_LE:
      os << lookup_atomic_name(e->getAtomic(), e->declared_atomic);
      os << "<=";
      os << e->getIntVal();
      break;
    case ATOMIC_GE:
      os << lookup_atomic_name(e->getAtomic(), e->declared_atomic);
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
      os << lookup_clock_name(e->getcX(), e->declared_clocks);
      os << "==";
      os << lookup_clock_name(e->getcY(), e->declared_clocks);
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
 * The typical output stream is os.
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
 * The typical output stream is os. This method is used for
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
void SubstList::print(std::ostream &os) const {
  bool end =false;
  os << "[";
  for(int i = 0; i < quantity; i++){
    if (this->at(i) != -1){
      if(end) os <<",";
      //os << "p" << i;
      os << lookup_atomic_name(i, declared_atomic);
      os <<"=" << this->at(i);
      end = true;
    }
  }
  os << "]";
}

/** Prints the specified integer (in base 10) in
 * its binary equivalent.
 * @param val The integer in base 10 to print.
 * @return none */
void printBinary(std::ostream& os, const int val) {
  for(int i = 15; i >=0; i--){
    if (val & (1 << i))
      os <<"1";
    else os <<"0";
  }
}

/** Prints out the fed in expression node to the fed in
 * output stream with a specified indentation (which doesn't seem
 * to be used: used in printing of transitions.
 * @param e (*) The ExprNode to print out.
 * @param os (&) The type of output stream to print the output to.
 * @return none */
void print_ExprNodeTrans(const ExprNode * const e, std::ostream& os)
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
        os << "(";
        print_ExprNodeTrans(e->getLeft(), os);
        os << " OR ";
        print_ExprNodeTrans(e->getRight(), os);
        os << ")";
        break;
      case OR_SIMPLE:
        os << "(";
        print_ExprNodeTrans(e->getLeft(), os);
        os << " OR_S ";
        print_ExprNodeTrans(e->getRight(), os);
        os << ")";
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
        os << lookup_atomic_name(e->getAtomic(), e->declared_atomic);
        os << ":=";
        os << e->getIntVal();
        break;
      case CONSTRAINT:
        e->dbm()->print_constraint(os);
        break;
      case ATOMIC:
        os << lookup_atomic_name(e->getAtomic(), e->declared_atomic);
        os << "==";
        os << e->getIntVal();
        break;
      case ATOMIC_NOT:
        os << lookup_atomic_name(e->getAtomic(), e->declared_atomic);
        os << "!=";
        os << e->getIntVal();
        break;
      case ATOMIC_LT:
        os << lookup_atomic_name(e->getAtomic(), e->declared_atomic);
        os << "<";
        os << e->getIntVal();
        break;
      case ATOMIC_GT:
        os << lookup_atomic_name(e->getAtomic(), e->declared_atomic);
        os << ">";
        os << e->getIntVal();
        break;
      case ATOMIC_LE:
        os << lookup_atomic_name(e->getAtomic(), e->declared_atomic);
        os << "<=";
        os << e->getIntVal();
        break;
      case ATOMIC_GE:
        os << lookup_atomic_name(e->getAtomic(), e->declared_atomic);
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
        os << lookup_clock_name(e->getcX(), e->declared_clocks);
        os << "==";
        os << lookup_clock_name(e->getcY(), e->declared_clocks);
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


