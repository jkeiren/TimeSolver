/** \file ExprNode.cc
 * Source file for proof classes: Sequents, Expressions and Transitions.
 * This file contains some additional methods not in the header file.
 * @author Peter Fontana
 * @author Dezhuang Zhang
 * @author Rance Cleaveland
 * @author Jeroen Keiren
 * @copyright MIT Licence, see the accompanying LICENCE.txt
 * @note Many functions are inlined for better performance.
 */

#include <cassert>
#include <iostream>
#include <string>
#include <sstream>
#include <map>
#include "bidirectional_map.h"
#include "ExprNode.h"

using namespace std;

/** Lookup the name of the clock with id n */
static inline const string& lookup_clock_name(
    const std::size_t n,
    const clock_name_to_index_t* declared_clocks) {
  return declared_clocks->reverse_at(n);
}

/** Lookup the name of the atomic with id n */
static inline const string& lookup_atomic_name(
    const std::size_t n,
    const atomic_name_to_index_t* declared_atomic) {
  return declared_atomic->reverse_at(n);
}

/** Prints out the expression to the desired output stream, labeling
 * the expression with its opType. The typical output stream is os.
 * @param e (*) The expression to print out.
 * @param os (&) The type of output stream to print the output to.
 * @return None */
void ExprNode::print(std::ostream& os) const {
  switch (getOpType()) {
    case PREDICATE:
      os << getPredicate();
      break;
    case FORALL:
      os << "FORALL.[";
      getQuant()->print(os);
      os << "]";
      break;
    case EXISTS:
      os << "EXISTS.[";
      getQuant()->print(os);
      os << "]";
      break;
    case FORALL_REL:
      os << "FORALLREL.(";
      getLeft()->print(os);
      os << ")[";
      getRight()->print(os);
      os << "]";
      break;
    case EXISTS_REL:
      os << "EXISTSREL.(";
      getLeft()->print(os);
      os << ")[";
      getRight()->print(os);
      os << "]";
      break;
    case ALLACT:
      os << "ALLACT.[";
      getQuant()->print(os);
      os << "]";
      break;
    case EXISTACT:
      os << "EXISTACT.[";
      getQuant()->print(os);
      os << "]";
      break;
    case AND:
      os << "(";
      getLeft()->print(os);
      os << " AND ";
      getRight()->print(os);
      os << ")";
      break;
    case OR:
      os << "(";
      getLeft()->print(os);
      os << " OR ";
      getRight()->print(os);
      os << ")";
      break;
    case OR_SIMPLE:
      os << "(";
      getLeft()->print(os);
      os << " OR_S ";
      getRight()->print(os);
      os << ")";
      break;
    case IMPLY:
      os << "-(-";
      getLeft()->print(os);
      os << " IMPLY ";
      getRight()->print(os);
      os << "-)-";
      break;
    case RESET:
      getExpr()->print(os);
      getClockSet()->print(os);
      break;
    case REPLACE:
      getExpr()->print(os);
      os << lookup_atomic_name(getAtomic(), declared_atomic);
      os << ":=";
      os << getIntVal();
      break;
    case CONSTRAINT:
      os << *(dbm());
      break;
    case ATOMIC:
      os << lookup_atomic_name(getAtomic(), declared_atomic);
      os << "==";
      os << getIntVal();
      break;
    case ATOMIC_NOT:
      os << lookup_atomic_name(getAtomic(), declared_atomic);
      os << "!=";
      os << getIntVal();
      break;
    case ATOMIC_LT:
      os << lookup_atomic_name(getAtomic(), declared_atomic);
      os << "<";
      os << getIntVal();
      break;
    case ATOMIC_GT:
      os << lookup_atomic_name(getAtomic(), declared_atomic);
      os << ">";
      os << getIntVal();
      break;
    case ATOMIC_LE:
      os << lookup_atomic_name(getAtomic(), declared_atomic);
      os << "<=";
      os << getIntVal();
      break;
    case ATOMIC_GE:
      os << lookup_atomic_name(getAtomic(), declared_atomic);
      os << ">=";
      os << getIntVal();
      break;
    case BOOL:
      os << ((getBool()) ? "TRUE" : "FALSE");
      break;
    case SUBLIST:
      getExpr()->print(os);
      getSublist()->print(os);
      break;
    case ASSIGN:
      getExpr()->print(os);
      os << "[";
      os << lookup_clock_name(getcX(), declared_clocks);
      os << "==";
      os << lookup_clock_name(getcY(), declared_clocks);
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
 * @param place If true, print for expressions with placeholders. Used for
 * expression types within proof subtrees with placeholders.
 * @return none */
void print_ExprNodeType(const opType op, std::ostream& os, bool place) {
  os << "**(";
  switch (op) {
    case PREDICATE:
      os << "PREDICATE";
      break;
    case FORALL:
      os << "FORALL" << (place ? " - P2" : "");
      break;
    case EXISTS:
      os << "EXISTS - P" << (place ? "2" : "");
      break;
    case FORALL_REL:
      os << "FORALLREL" << (place ? " - P2" : "");
      break;
    case EXISTS_REL:
      os << "EXISTSREL - P" << (place ? "2" : "");
      break;
    case ALLACT:
      os << "ALLACT" << (place ? " - B" : "");
      break;
    case EXISTACT:
      os << "EXISTACT" << (place ? " - B" : "");
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
      os << "RESET" << (place ? " - P2" : "");
      break;
    case REPLACE:
      os << "REPLACE" << (place ? " - B" : "");
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

/** Prints out the fed in expression node to the fed in
 * output stream: used in printing of transitions.
 * @param e (*) The ExprNode to print out.
 * @param os (&) The type of output stream to print the output to.
 * @return none */
void print_ExprNodeTrans(const ExprNode* const e, std::ostream& os) {
  if (e != nullptr) {
    switch (e->getOpType()) {
      case PREDICATE:
        os << e->getPredicate();
        break;
      case FORALL:
        os << "FORALL.[";
        print_ExprNodeTrans(e->getQuant(), os);
        os << "]";
        break;
      case EXISTS:
        os << "EXISTS.[";
        print_ExprNodeTrans(e->getQuant(), os);
        os << "]";
        break;
      case FORALL_REL:
        os << "FORALLREL.(";
        print_ExprNodeTrans(e->getLeft(), os);
        os << ")[";
        print_ExprNodeTrans(e->getRight(), os);
        os << "]";
        break;
      case EXISTS_REL:
        os << "EXISTSREL.(";
        print_ExprNodeTrans(e->getLeft(), os);
        os << ")[";
        print_ExprNodeTrans(e->getRight(), os);
        os << "]";
        break;
      case ALLACT:
        os << "ALLACT.[";
        print_ExprNodeTrans(e->getQuant(), os);
        os << "]";
        break;
      case EXISTACT:
        os << "EXISTACT.[";
        print_ExprNodeTrans(e->getQuant(), os);
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
        os << ((e->getBool()) ? "TRUE" : "FALSE");
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
