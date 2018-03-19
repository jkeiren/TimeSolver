/** \file ExprNode.hh
 * Header file for proof classes: Sequents, Expressions and Transitions.
 * @author Peter Fontana
 * @author Dezhuang Zhang
 * @author Rance Cleaveland
 * @author Jeroen Keiren
 * @copyright MIT Licence, see the accompanying LICENCE.txt
 */

#ifndef EXPR_NODE_H
#define EXPR_NODE_H

#include <cassert>
#include <cstdio>
#include <cstdlib>
#include <fstream>
#include <map>
#include <vector>
#include <deque>
#include <list>
#include <utility>
#include <string>
#include "DBM.hh"
#include "DBMList.hh"

/** The type that contains all of the logical constraints/connectives
 * needed. This covers all possible cases of an ExprNode expression.
 * Possible types: FORALL, EXISTS, FORALL_REL, EXISTS_REL,
 * OR, OR_SIMPLE, AND, IMPLY, CONSTRAINT,
 * BOOL, ATOMIC, PREDICATE, RESET, SUBLIST, ATOMIC_NOT, ATOMIC_LT, ATOMIC_GT,
 * ATOMIC_LE, ATOMIC_GE, ASSIGN, REPLACE, ALLACT, EXISTACT, ABLEWAITINF, and
 * UNABLEWAITINF. Note that
 * FORALL_REL is a derived operator. While supported, the parser eliminates
 * this operator from all expressions using its derivation. Its support is
 * included in case a faster way to check FORALL_REL is found. */
enum opType {
  FORALL,
  EXISTS,
  FORALL_REL,
  EXISTS_REL,
  OR,
  OR_SIMPLE,
  AND,
  IMPLY,
  CONSTRAINT,
  BOOL,
  ATOMIC,
  PREDICATE,
  RESET,
  SUBLIST,
  ATOMIC_NOT,
  ATOMIC_LT,
  ATOMIC_GT,
  ATOMIC_LE,
  ATOMIC_GE,
  ASSIGN,
  REPLACE,
  ALLACT,
  EXISTACT,
  ABLEWAITINF,
  UNABLEWAITINF
};

/** Prints out the expression type (opType) to the desired output stream.
 * The typical output stream is cout.
 * @param op (*) The expression type.
 * @param os (&) The type of output stream to print the output to.
 * @return none */
void print_ExprNodeType(const opType op, std::ostream& os, bool place = false);

inline std::ostream& operator<<(std::ostream& os, const opType& op) {
  print_ExprNodeType(op, os);
  return os;
}

/** A Substitution list, functioning as both the location component
 * of a sequent and a mechanism to change location (via variable assignments).
 * The SubstList stores the location (discrete state) using variable form,
 * representing a location as an integer assignment to each variable.
 * Each element of the SubstList is a variable. Any variable with
 * a value of -1 indicates that the variable is not restricted
 * (could be any value).
 * @author Peter Fontana, Dezhuang Zhang, and Rance Cleaveland.
 * @note Many functions are inlined for better performance.
 * @version 1.2
 * @date November 2, 2013 */
class SubstList : public OneDIntArray {
protected:
  const bidirectional_map<std::string, int>& declared_atomic;

public:
  /** Constructor. Initializes all variables to -1 except the specified
   * index, whose value is initialized to val.
   * @param index The location of the variable to initialize to a
   * user-specified value.
   * @param val The value to initialize the specified variable to.
   * @param numElements The number of variables (the size of the list).
   * @return [Constructor]. */
  SubstList(const size_type index, const element_type val, const size_type numElements,
            const bidirectional_map<std::string, int>& as)
      : OneDIntArray(numElements), declared_atomic(as) {
    for (size_type i = 0; i < numElements; i++) {
      this->operatorAccess(i) = -1;
    }
    this->operatorAccess(index) = val;
  }

  /** Constructor. Initializes all variables to 0, providing a specific initial
   * state.
   * @param numElements The number of variables (the size of the list).
   * @return [Constructor]. */
  SubstList(const size_type numElements,
            const bidirectional_map<std::string, int>& as)
      : OneDIntArray(numElements), declared_atomic(as) {
    for (size_type i = 0; i < numElements; i++) this->operatorAccess(i) = 0;
  }

  /** 2-list Copy Constructor. Creates a substitution list
   * by assigning the values in the first substitution list into the second.
   * This is meant as a layered substitution. This constructor copies
   * the values from st1 (first list) if they are not -1.  If they are -1, it
   * then copies the values from st2 (the second list).
   * @param st1 (*) The pointer to the first and primary
   * SubstList to get values from.
   * @param st2 (*) The pointer to the second SubstList to get values from.
   * @return [Constructor]. */
  SubstList(const SubstList* const st1, const SubstList* const st2)
      : OneDIntArray(st1->quantity), declared_atomic(st1->declared_atomic) {
    for (size_type i = 0; i < quantity; i++) {
      if (st1->operatorAccess(i) != -1)
        this->operatorAccess(i) = st1->operatorAccess(i);
      else
        this->operatorAccess(i) = st2->operatorAccess(i);
    }
  }

  /** Copy Constructor.
   * @param Y (&) The object to copy.
   * @return [Constructor]. */
  SubstList(const SubstList& Y)
      : OneDIntArray(Y), declared_atomic(Y.declared_atomic){}

  // Default move constructor.
  SubstList(SubstList&& other) = default;

  /** Destructor.  Does nothing.
   * @return [Destructor]. */
  ~SubstList() {}

  /** Deep-Copy equality of SubList structures: two SubstList objects are equal
   * if and only if they both are the same size and they have the same values
   * for each variable.
   * @param Y (&) The reference to the RHS SubstList.
   * @return true: the SubstList is equal to Y; false: otherwise. */
  bool operator==(const SubstList& Y) const {
    return (std::memcmp(storage, Y.storage, quantity * sizeof(element_type)) == 0);
  }

  /** Element-wise equality of SubList elements */
  bool equal_contents(const SubstList& Y) const {
    if (quantity != Y.quantity) {
      return false;
    }

    for (size_type j = 0; j < quantity; j++) {
      if (at(j) != Y.at(j)) {
        return false;
      }
    }
    return true;
  }

  /** Changes the list by changing the specified variable to
   * value val.  The SubstList calling this is changed.
   * @param index The location to change the value of
   * @param val The value to change the desired element to.
   * @return a pointer to the SubstList that was just changed. */
  SubstList* addst(const size_type index, const element_type val) {
    assert(index < quantity);
    this->operator[](index) = val;
    return this;
  }

  /** Returns the number of variables in this SubstList.
   * @return the number of variables in the SubstList. */
  size_type nElements() const { return quantity; }

  /** Prints the contents of the SubstList.  A variable with
   * value -1 is considered empty (the SubstList does not restrict
   * this variable).
   * @param os (&) The output stream to print the output to
   * @return none. */
  void print(std::ostream& os) const {
    bool end = false;
    os << "[";
    for (size_type i = 0; i < quantity; i++) {
      if (this->at(i) != -1) {
        if (end) os << ",";
        // os << "p" << i;
        os << declared_atomic.reverse_at(i);
        os << "=" << this->at(i);
        end = true;
      }
    }
    os << "]";
  }
};

/** Overload for substitution lists */
inline std::ostream& operator<<(std::ostream& os, const SubstList& s) {
  s.print(os);
  return os;
}

/** This class represents an expression tree, which is often rooted
 * as the right hand side of a PES Equation. These expressions are often
 * the right hand side of a Sequent.
 *
 * For performance reasons, this class is a "union-like" class: its variables
 * are overloaded for multiple purposes. To utilize different purposes, there
 * are different constructors that are used for different operation types
 * (see the comments for the constructors). Also, there are multiple
 * methods with different names that do the "same" thing; these methods
 * are named to suggest the kinds of expressions they are used with and
 * the purposes of the variables they interact with.
 *
 * Each node is a root of an expression tree that involves logical
 * operators and constraints.  Most trees are constructed by the
 * parser. In ExprNode, each constructor, classified
 * by operand type (specified by opType), corresponds to a different
 * expression type.
 *
 * For the constructors, giving an optype different from what is recommended
 * in each constructor may result in program errors.
 * @author Peter Fontana, Dezhuang Zhang, and Rance Cleaveland.
 * @note Many functions are inlined for better performance.
 * @note The ExprNode class's variables have multiple uses for different
 * expression types (for performance reasons). See above comments.
 * @version 1.2
 * @date November 2, 2013 */
class ExprNode {
public:
  /** Constructor for one-child expressions with
   * opType = {FORALL, EXISTS, ALLACT, EXISTACT}.
   * @param o The logical operator/constraint type.
   * @param q (*) The left (single) child expression.
   * @note Using this constructor with an opType value other than one of
   * the values given above may result in program errors.
   * @return [Constructor]. */
  ExprNode(const opType o, ExprNode* q,
           const bidirectional_map<std::string, int>& cs,
           const bidirectional_map<std::string, int>& as)
      : left(q), op(o), declared_clocks(cs), declared_atomic(as) {
    right = nullptr;
    constraint = nullptr;
    cset = nullptr;
    predicate = nullptr;
    subst = nullptr;
    assert(q != nullptr);
  }

  /** Constructor for two-children expressions with
   * opType = {FORALL_REL, EXISTS_REL, OR, AND, IMPLY}.
   * @param o The logical operator/constraint type.
   * @param l (*) The left child ExprNode
   * @param r (*) The right child ExprNode
   * @note Using this constructor with an opType value other than one of
   * the values given above may result in program errors.
   * @return [Constructor]. */
  ExprNode(const opType o, ExprNode* l, ExprNode* r,
           const bidirectional_map<std::string, int>& cs,
           const bidirectional_map<std::string, int>& as)
      : left(l), right(r), op(o), declared_clocks(cs), declared_atomic(as) {
    constraint = nullptr;
    predicate = nullptr;
    cset = nullptr;
    subst = nullptr;
    assert(l != nullptr);
    assert(r != nullptr);
  }

  /** Constructor for a clock constraint expression with optype = {CONSTRAINT}.
   * Clock constraints are represented as DBMs.
   * @param o The logical operator/constraint type.
   * @param c (*) The DBM representing the clock constraints.
   * @note Using this constructor with an opType value other than one of
   * the values given above may result in program errors.
   * @return [Constructor]. */
  ExprNode(const opType o, DBM* c,
           const bidirectional_map<std::string, int>& cs,
           const bidirectional_map<std::string, int>& as)
      : op(o), declared_clocks(cs), declared_atomic(as) {
    assert(c != nullptr);
    left = nullptr;
    right = nullptr;
    predicate = nullptr;
    constraint = c;
    cset = nullptr;
    subst = nullptr;
  }

  /** Constructor for a boolean expression of true or false
   * with optype = {BOOL, ABLEWAITINF, UNABLEWAITINF}.
   * For optype = {ABLEWAITINF, UNABLEWAITINF}, the boolean
   * assigned does not matter. These tokens are used to give
   * faster implementations of a common formula.
   * @param o The logical operator/constraint type.
   * @param bv The boolean value of TRUE or FALSE.
   * @note Using this constructor with an opType value other than one of
   * the values given above may result in program errors.
   * @return [Constructor]. */
  ExprNode(const opType o, const bool bv,
           const bidirectional_map<std::string, int>& cs,
           const bidirectional_map<std::string, int>& as)
      : op(o), b(bv), declared_clocks(cs), declared_atomic(as) {
    left = nullptr;
    right = nullptr;
    predicate = nullptr;
    constraint = nullptr;
    cset = nullptr;
    subst = nullptr;
  }

  /** Constructor for atomic (state value) expressions with
   * optype = {ATOMIC, ATOMIC_NOT, ATOMIC_LT, ATOMIC_GT, ATOMIC_LE, ATOMIC_GE}.
   * Each expression represents
   * a constraint on one discrete state variable. Multi-variable expressions
   * are formed by combining these expressions with AND
   * and OR ExprNode expressions. The int is the integer constant for the
   * constraint specified by the opType. The opType ATOMIC represents the
   * constraint = (equals).
   * @param o The logical operator/constraint type.
   * @param a The id label of the atomic (predicate/logical) variable
   * @param i The int value representing what the atomic variable's value
   * should be constrained to. The constraint is specified by the opType.
   * @note Using this constructor with an opType value other than one of
   * the values given above may result in program errors.
   * @return [Constructor]. */
  ExprNode(const opType o, const short a, const short i,
           const bidirectional_map<std::string, int>& cs,
           const bidirectional_map<std::string, int>& as)
      : op(o), atomic(a), intVal(i), declared_clocks(cs), declared_atomic(as) {
    left = nullptr;
    right = nullptr;
    predicate = nullptr;
    subst = nullptr;
    cset = nullptr;
    constraint = nullptr;
  }

  /** Constructor for invariant sub-expressions with opType = {ATOMIC}.
   * This expression represents a state (combined discrete and clock) such that
   * the variable specified by a has integer value i and the clock state
   * satisfies the specified clock constraints.

   * For such expressions, any discrete
   * state satisfying the atomic constraint must specify
   * the clock constraint. (Note: these expressions be used in other
   * ways; this is how our tool uses them.)
   * @param o The logical operator/constraint type.
   * @param a The id label of the atomic (predicate/logical) variable
   * @param i The integer value representing what the atomic variable's value
   * should be equal to.
   * @param c (*) The DBM containing the clock constraints.
   * @note Using this constructor with an opType value other than one of
   * the values given above may result in program errors.
   * @return [Constructor]. */
  ExprNode(const opType o, const short a, const short i, DBM* c,
           const bidirectional_map<std::string, int>& cs,
           const bidirectional_map<std::string, int>& as)
      : constraint(c),
        op(o),
        atomic(a),
        intVal(i),
        declared_clocks(cs),
        declared_atomic(as) {
    left = nullptr;
    right = nullptr;
    predicate = nullptr;
    cset = nullptr;
    subst = nullptr;
  }

  /** Constructor for predicate variable expressions with opType = {PREDICATE}.
   * @param o The logical operator/constraint type.
   * @param a (*) The string label of the predicate (predicate variable name).
   * @param i The index of the predicate to use for hashing.
   * @note Using this constructor with an opType value other than one of
   * the values given above may result in program errors.
   * @return [Constructor]. */
  ExprNode(const opType o, const char* a, const short i,
           const bidirectional_map<std::string, int>& cs,
           const bidirectional_map<std::string, int>& as)
      : predicate(a),
        op(o),
        intVal(i),
        declared_clocks(cs),
        declared_atomic(as) {
    left = nullptr;
    right = nullptr;
    cset = nullptr;
    subst = nullptr;
    constraint = nullptr;
  }

  /** Constructor for clock set expressions with opType = {RESET}. These
   * expressions are used to reset a set of clocks (specified by the
   * ClockSet) to 0.
   * @param o The logical operator/constraint type.
   * @param l (*) The single (left) child expression.
   * @param s (*) The set of clocks (to reset to 0).
   * @note Using this constructor with an opType value other than one of
   * the values given above may result in program errors.
   * @return [Constructor]. */
  ExprNode(const opType o, ExprNode* l, ClockSet* s,
           const bidirectional_map<std::string, int>& cs,
           const bidirectional_map<std::string, int>& as)
      : left(l), cset(s), op(o), declared_clocks(cs), declared_atomic(as) {
    right = nullptr;
    predicate = nullptr;
    constraint = nullptr;
    subst = nullptr;
  }

  /** Constructor for sublist expressions, representing a change of
   * discrete state, with opType = {SUBLIST}. These expressions
   * are used to change the discrete state by applying the assignment
   * dictated by the SubstList. In the SubstList, any variable with value -1
   * leaves the current state variable unchanged.
   * @param o The logical operator/constraint type.
   * @param l (*) The reference to the (single) child expression.
   * @param s (*) The (discrete) variable assignment to apply within the
   * child expression (specified by parameter l).
   * @note Using this constructor with an opType value other than one of
   * the values given above may result in program errors.
   * @return [Constructor]. */
  ExprNode(const opType o, ExprNode* l, SubstList* s,
           const bidirectional_map<std::string, int>& cs,
           const bidirectional_map<std::string, int>& as)
      : left(l), subst(s), op(o), declared_clocks(cs), declared_atomic(as) {
    right = nullptr;
    predicate = nullptr;
    cset = nullptr;
    constraint = nullptr;
  }

  /** Constructor for assignment and replacement expressions with
   * opType = {ASSIGN, REPLACE}. If
   * opType = ASSIGN, assign a clock variable's value to the current
   * value of another clock. If opType = REPLACE,
   * change an atomic variable's (discrete state) value to the specified
   * value. Using expressions with these operators results in sequential,
   * not simultaneous, assignment.
   * @param o The logical operator/constraint type.
   * @param l (*) The (single, left) child expression.
   * @param cx The int id of the variable (discrete or clock) to
   * assign a new value to
   * @param cy The value to assign the variable to within the child expression.
   * @note Using this constructor with an opType value other than one of
   * the values given above may result in program errors.
   * @return [Constructor]. */
  ExprNode(const opType o, ExprNode* l, const short int cx, const short int cy,
           const bidirectional_map<std::string, int>& cs,
           const bidirectional_map<std::string, int>& as)
      : left(l),
        op(o),
        atomic(cx),
        intVal(cy),
        declared_clocks(cs),
        declared_atomic(as) {
    right = nullptr;
    predicate = nullptr;
    cset = nullptr;
    constraint = nullptr;
    subst = nullptr;
  }

  /** Copy Constructor. This is used when an expression needs to be duplicated
   * in the parser. Because this makes a deep copy of every item, use sparingly,
   * and aim to make shallow copies when possible. This makes a deep copy of all
   * descendants of the ExprNode E
   * @param E (&) The ExprNode object to make a deep copy of
   * @return [Constructor]. */
  ExprNode(const ExprNode& other)
      : predicate(other.predicate), // shallow copy good enough
        op(other.op),
        atomic(other.atomic),
        intVal(other.intVal),
        b(other.b),
        declared_clocks(other.declared_clocks),
        declared_atomic(other.declared_atomic) {
    if (other.constraint != nullptr) {
      constraint = new DBM(*(other.constraint));
    }
    if (other.cset != nullptr) {
      cset = new ClockSet(*(other.cset));
    }
    if (other.subst != nullptr) {
      subst = new SubstList(*(other.subst));
    }
    if (other.left != nullptr) {
      left = new ExprNode(*(other.left));
    }
    if (other.right != nullptr) {
      right = new ExprNode(*(other.right));
    }
  }

  /** Destructor. Since predicates are allocated differently,
   * the destructor works with them differently. Based on how the tool
   * works, the predicate variables are freed when the predicates are deleted.
   * This methodology allows a predicate variable expression to be referred to
   * by multiple ExprNode expressions.
   * @return [Destructor]. */
  ~ExprNode() {
    if (left != nullptr && left->op != PREDICATE) {
      delete left;
    }
    if (right != nullptr && right->op != PREDICATE) {
      delete right;
    }

    delete constraint;
    delete subst;
    delete cset;
    /* Note: since predicates are shallow-copied, they are not deleted
     * here. */
  }

  /** Method that deletes the predicate string. Since predicate strings are
   * assigned as shallow copies (multiple ExprNode objects are given the same
   * predicate for performance reasons), the user should call this method
   * sparingly to delete predicate strings in order to prevent memory leaks.
   * @return [None]. */
  void deletePredicate() { delete predicate; }

  /** Returns the opType of the expression, which labels/categorizes
   * the expression.
   * @return The opType which tells what kind of expression that node is.
   * @see The Constructor(s) comments for more information. */
  opType getOpType() const { return op; }

  /** Returns the left child of the expression. Used for
   * quantified expressions, which have only one child. (In an ExprNode,
   * the single child is assigned as the left child with a nullptr right child.)
   * @return The reference to the left (or single) child of that expression.
   * @see The Constructor(s) comments for more information. */
  ExprNode* getQuant() const { return left; }

  /** Returns the left child of the ExprNode.
   * @note This does the same thing as getQuant(), but tends to be used
   * for expressions with two (left and right) children.
   * @return The reference to the left (or single) child of that expression.
   * @see The Constructor(s) comments for more information. */
  const ExprNode* getLeft() const { return left; }

  /** Returns the right (or second) child of the expression.
   * @return The reference to the right (or second) child of that expression.
   * @see The Constructor(s) comments for more information. */
  const ExprNode* getRight() const { return right; }

  /** Returns the clock constraint (DBM representation) of the expression.
   * @return The reference to the DBM representing the clock constraints.
   * @see The Constructor(s) comments for more information. */
  const DBM* dbm() const { return constraint; }

  /** Sets the constraint of the ExprNode to the specified DBM reference.
   * This method assigns the DBM with a shallow copy (copies the address).
   * @param dbm (*) the DBM reference to assign to the ExprNode.
   * @return none. */
  void setDBM(DBM* dbm) { constraint = dbm; }

  /** Returns the boolean value (TRUE or FALSE) of the expression if stored
   * used to get the true/false value of the expression.
   * @return The boolean value (TRUE or FALSE) of the expression if stored.
   * @see The Constructor(s) comments for more information. */
  bool getBool() const { return b; }

  /** Returns the variable (location, or clock) id stored
   * in the expression.
   * @return The id of the atomic (location, or clock)
   * variable stored in the expression.
   * @see The Constructor(s) comments for more information. */
  short int getAtomic() const { return atomic; }

  /** Returns the value (name) of the predicate variable in
   * the expression.
   * @return The expression's predicate variable's name.
   * @see The Constructor(s) comments for more information. */
  const char* getPredicate() const { return predicate; }

  /** Returns the value representing constant with which to compare the variable
   * stored in atomic.
   * @return The value of the variable relevant to the atomic variable.
   * @see The Constructor(s) comments for more information. */
  short int getIntVal() const { return intVal; }

  /** Returns the left (or single) child of the ExprNode.
   * @note This does the same thing as getQuant() and getLeft(), and is
   * used for other single-child ExprNode expressions.
   * @return The reference to the left (or single) child of that expression.
   * @see The Constructor(s) comments for more information. */
  ExprNode* getExpr() const { return left; }

  /** Returns the set of clocks stored in the ExprNode.
   * @return The set of clocks stored in the Expression.
   * @see The Constructor(s) comments for more information. */
  const ClockSet* getClockSet() const { return cset; }

  /** Returns the assignment of control variables stored in the expression.
   * @return The assignment of (discrete) variables.
   * @see The Constructor(s) comments for more information. */
  const SubstList* getSublist() const { return subst; }

  /** Returns the clock id of the clock to reset or to give a
   * different variable. While this can be used for other
   * expression types, it is intended to get a clock id.
   * @return The id of the atomic (location or clock) variable stored in
   * the expression.
   * @note This does the same thing as getAtomic().
   * @see The Constructor(s) comments for more information. */
  short int getcX() const { return atomic; }

  /** Returns the value to assign a clock to. For this method,
   * the value is intended to be the index of the clock to take its
   * value and assign to another clock.
   * @return the value of the variable relevant to the atomic variable.
   * @note This does the same thing as getIntVal().
   * @see The Constructor(s) comments for more information. */
  short int getcY() const { return intVal; }

  /** Sets the parity of the expression, using true = gfp and false = lfp.
   * @param parity The desired parity: true = gfp and false = lfp.
   * @return None. */
  void set_Parity(const bool parity) { b = parity; }

  /** Sets the block (equation block) the expression represents
   * by changing the value of intVal. Used for PREDICATE (equation) expressions.
   * @param block The block number (integer) to set intVal to, which gives
   * the block of the expression.
   * @note The integer storing the block can be used for other purposes.
   * @return None.*/
  void set_Block(const short block) { intVal = block; }

  /** Returns the parity of the expression: true = gfp, false = lfp.
   * @return The parity (as a boolean) of the
   * expression: true = gfp, false = lfp.
   * @note This does the same thing as getBool(). It is used differently.
   * @see The Constructor(s) comments for more information. */
  bool get_Parity() const { return b; }

  /** Returns the integer representing the block number of the expression.
   * This function is used for PREDICATE expressions.
   * @return The integer value; in this case, it corresponds to the
   * expression's block.
   * @note This function does the same thing as getIntVal() and getcY().
   * @see The Constructor(s) comments for more information. */
  short int get_Block() const { return intVal; }

  /** Checks if atomic (usually location variable) a has value b; this
   * method is used when checking invariants.  This method
   * checks if the assignment
   * stored in ExprNode mathces the specified label and assignment value.
   * @param a The candidate atomic value.
   * @param b The candidate intVal value.
   * @returns true: if a is the atomic id in the expression and b is the intVal
   * value in the expression; false: otherwise. */
  bool inv_loc(const int a, const int b) {
    return ((a == atomic) && (b == intVal));
  }

  /** Negates all the atomic propositions in the expression. The negation
   * works by switching the atomic proposition types of all nodes (including
   * children nodes of the expression. This includes atomic propositions,
   * booleans, and the AbleWaitInf and UnableWaitInf opTypes.
   * If the expression just involves
   * comparisons to atomic propositions, then this negates the expression.
   * @return [None] */
  void negateAtomicExpr() {
    switch (op) {
      case ATOMIC:
        op = ATOMIC_NOT;
        break;
      case ATOMIC_NOT:
        op = ATOMIC;
        break;
      case ATOMIC_LT:
        op = ATOMIC_GE;
        break;
      case ATOMIC_GT:
        op = ATOMIC_LE;
        break;
      case ATOMIC_LE:
        op = ATOMIC_GT;
        break;
      case ATOMIC_GE:
        op = ATOMIC_LT;
        break;
      case BOOL:
        // In this case, negate the boolean.
        b = !b;
        break;
      case ABLEWAITINF:
        op = UNABLEWAITINF;
        break;
      case UNABLEWAITINF:
        op = ABLEWAITINF;
        break;
      default: // do nothing for other cases
        break;
    }
    if (left != nullptr) {
      left->negateAtomicExpr();
    }
    if (right != nullptr) {
      right->negateAtomicExpr();
    }
  }

  /** Set the left child destination to a shallow copy of the
   * specified expression.
   * @param destL (*) the (left) child expression
   * @return None. */
  void setExprDestLeft(ExprNode* destL) { left = destL; }

  /** Set the right child destination to a shallow copy of the
   * specified expression.
   * @param destR (*) the (right) child expression
   * @return None. */
  void setExprDestRight(ExprNode* destR) { right = destR; }

protected:
  /* Note: The data variables here are used as a "quasi-union",
   * where the same variable can have different uses for different
   * expressions.  Hence, different expressions call different methods
   * and use different constructors to take advantage of the
   * performance from this.
   * The method names give some indication of what the different uses
   * are. */

  /** The string label of a predicate variable in an expression. */
  const char* predicate;

  /** The left child of an ExprNode in an expression tree.
   * Possibly empty. */
  ExprNode* left;
  /** The right child of an ExprNode in an expression tree.
   * Possibly empty. */
  ExprNode* right;

  /** The clock constraint of an ExprNode.
   * Possibly empty. */
  DBM* constraint;

  /** Represents the set of clocks (a subset of the set of
   * specified clocks) in an ExprNode, currently used
   * to specify the set of clocks to reset to 0.  */
  ClockSet* cset;
  /** Represents a list of (usually control or atomic) variables and
   * what values should be substituted into them.
   * Used in an expression to represent a substitution of variables in a
   * child expression. The SubstList is often the "state",
   * giving values to propositions (or control values).  Possibly empty. */
  SubstList* subst;

  /** The "opcode" or Type ID of the Expression Node.
   * This type determines
   * which fields are empty or non-empty and the shape of
   * the expression node. */
  opType op;

  /** The label for the atomic (location or clock variable)
   * of the expression, depending on the opType.
   * For opTypes ATOMIC, ATOMIC_NOT, ATOMIC_LT, ATOMIC_GT, and REPLACE:
   * the atomic represents a location variable.
   * For opTypes RESET, and ASSIGN:
   * the atomic variable represents the clock variable (clock index)
   * The parser converts variable names into integer indexes.*/
  short int atomic;
  /** Used to store an integer value that corresponds to different
   * meanings, depending on the opType.
   * For opTypes ATOMIC, ATOMIC_NOT, ATOMIC_LT, ATOMIC_GT, and REPLACE:
   * intVal is an integer constant representing a location variable constant.
   * The expression represents a constraint comparison (specified by the opType,
   * with ATOMIC and REPLACE corresponding to =) to the intVal.
   * For opType ASSIGN: intVal is the integer of the clock index
   * to assign to the clock stored in int atomic.*/
  short int intVal;

  /** Used as the boolean value of an expression or its parity.
   * For opType BOOL: b is the truth of the expression. For
   * opType PREDICATE: b is the parity of the expression, with
   * true = gfp and false = lfp. */
  bool b;

  // FIXME
public:
  /** Pointer to the globally declared clocks */
  const bidirectional_map<std::string, int>& declared_clocks;

  /** Pointer to the globally declared atomics*/
  const bidirectional_map<std::string, int>& declared_atomic;

  /** Prints out the expression to the desired output stream, labeling
   * the expression with its opType. The typical output stream is cout.
   * @param e (*) The expression to print out.
   * @param os (&) The type of output stream to print the output to.
   * @return None */
  void print(std::ostream& os) const;
};

/** Overload for streaming ExprNode to output stream */
inline std::ostream& operator<<(std::ostream& os, const ExprNode& e) {
  e.print(os);
  return os;
}

/* These next set of functions are global and
 * used in demo.cc to keep track of the clocks, equations,
 * blocks and predicate variables of the PES read in by
 * the parser. */

/** Assuming that e is a chain of ASSIGN expressions (possibly ending
 * with a BOOL expression, this converts that expression to an ordered
 * list of clock assignments. The innermost assignments are at the back
 * of the vector.
 * @param e (*) the pointer to the expression of clock assignments.
 * @param av (*) the pointer to the vector of clock assignments.
 * @return None. When finished, av is changed to be the vector of
 * clock assignments.  */
inline
void makeAssignmentList(const ExprNode& e,
                        std::vector<std::pair<short int, short int>>* av) {
  if (e.getOpType() == ASSIGN) {
    av->push_back(std::make_pair(e.getAtomic(), e.getIntVal()));
    makeAssignmentList(*e.getExpr(), av);
  }
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
inline void print_sequent(std::ostream& os, const size_t step, const bool retVal,
                          const DBM& lhs, const ExprNode& rhs,
                          const SubstList& sub, const opType op) {
  os << "seq#" << step << "  " << retVal << "  " << lhs << ", " << sub
     << "\t|-  " << rhs << "\t" << op << std::endl;
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
inline void print_sequentCheck(std::ostream& os, const size_t step,
                               const bool retVal, const DBM& lhs,
                               const DBMList& rhsList,
                               const SubstList& sub, const opType op) {
  os << "seq#" << step << "  " << retVal << "  " << lhs << ", " << sub
     << "\t|-  " << rhsList << "\t" << op << std::endl;
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
inline void print_sequent_place(std::ostream& os, const size_t step,
                                const bool retVal, const DBM& lhs,
                                const DBMList& place, const ExprNode& rhs,
                                const SubstList& sub, const opType op) {
  os << "seq#" << step << "  " << retVal << "  " << lhs << " plhold: {"
     << place << "}" << ", " << sub << "\t|-  " << rhs << "\t";
  print_ExprNodeType(op, os, true);
  os << std::endl;
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
inline void print_sequent_placeCheck(std::ostream& os, const size_t step,
                                     const bool retVal, const DBM& lhs,
                                     const DBMList& place,
                                     const DBMList& rhsList,
                                     const SubstList& sub,
                                     const opType op) {
  os << "seq#" << step << "  " << retVal << "  " << lhs << " plhold: {"
     << place << "}" << ", " << sub << "\t|-  " << rhsList << "\t";
  print_ExprNodeType(op, os, true);
  os << std::endl;
}

void print_ExprNodeTrans(const ExprNode* const e, std::ostream& os);

#endif
