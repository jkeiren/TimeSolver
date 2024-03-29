/** Data structures for transitions of timed automata.
  *
  * @author Peter Fontana
  * @author Dezhuang Zhang
  * @author Rance Cleaveland
  * @author Jeroen Keiren
  * @copyright MIT Licence, see the accompanying LICENCE.txt
  */
#ifndef TRANSITION_HH
#define TRANSITION_HH

#include <ostream>
#include "ExprNode.h"

/** Class used to represent transitions of a timed automaton. This
 * class allows for ease of parsing and storage of transitions during
 * the model checking process.
 * @author Peter Fontana, Dezhuang Zhang, and Rance Cleaveland.
 * @note Many functions are inlined for better performance.
 * @version 1.2
 * @date November 2, 2013 */
class Transition {
public:
  /** Constructor for transitions. This is used in the parser
   * to form transition objects
   * @param destParent (*) a reference for the expression that is the
   * parent of the destination expression that follows the transition
   * in a proof.
   * @param leftExprIn (*) The ExprNode representing the left
   * (enabling conditions) of the transition.
   * @param rightExprIn (*) The ExprNode representing the right
   * (transition destination and state changes) of the transition.
   * @param isDestOnLeft true: destination expression should be a
   * left child of destParent; false: otherwise (the destination expression of a
   * proof should be the right child of destParent).
   * @param dest (*) The partial substitution list for the change in discrete
   * state. If there is no assignment, dest will be nullptr.
   * @param reset (*) The set of clocks the transition resets. This will be nullptr
   * if no clocks are reset.
   * @return [Constructor]. */
  Transition(ExprNode* const destParent, const ExprNode* const leftExprIn,
             ExprNode* const rightExprIn, const bool isDestOnLeft,
             const SubstList* const dest, const clock_set* const reset,
             const std::vector<std::pair<DBM::size_type, clock_value_t>>* const
                 clockAssignments)
      : destPar(destParent),
        isDestLeft(isDestOnLeft),
        clockAssignmentList(
            clockAssignments == nullptr
                ? nullptr
                : new std::vector<std::pair<DBM::size_type, clock_value_t>>(
                      *clockAssignments)),
        leftExpr(leftExprIn),
        rightExpr(rightExprIn),
        destList(dest),
        resetList(reset){}

  /** Destructor. Given the referencing of different
   * destination expressions from multiple sources,
   * this destructor deletes all of the expressions
   * save the destination expression pointed to by destPar's
   * child. This expression is deleted when the proof deletes
   * the proof expression tree.
   * @return [Destructor]. */
  ~Transition() {
    /* First set destExpr to nullptr to not double delete */
    if (destPar == nullptr && rightExpr != nullptr) {
      rightExpr = nullptr;
    } else if (isDestLeft && destPar != nullptr) {
      destPar->setExprDestLeft(nullptr);
    } else if (destPar != nullptr) {
      destPar->setExprDestRight(nullptr);
    }
    /* should be superfluous
    if(clockAssignmentList != nullptr) {
      clockAssignmentList->clear();
    }
     */
    delete clockAssignmentList;
    delete leftExpr;
    delete rightExpr;
    /* Due to how the transitions sets destList and resetList,
     * they are deleted when the expression is deleted. Hence,
     * destList and resetList do not need to be deleted here. */
  }

  /** Retrieve the expression that specifies
   * the enabling condition of the transition.
   * @return The ExprNode describing the enabling conditions of the
   * transition. */
  const ExprNode* guard() const { return leftExpr; }

  /** Retrieve the expression that specifies
   * the destination (state change) of the transition.
   * @return The ExprNode describing the destination (state change) of the
   * transition. */
  const ExprNode* getRightExpr() const { return rightExpr; }

  /** Retrieve the list of clock assignments stored by this transition.
   * @return the vector containing the ordered list of clock assignments
   * that occur on the edge of this transition. */
  const std::vector<std::pair<DBM::size_type, clock_value_t >>* clock_assignments()
      const {
    return clockAssignmentList;
  }

  /** Takes a specified destination and tacks it on as an
   * expression at the end of the transition. This method
   * is used by the proof to provide an O(1) assignment of
   * what expression needs to be true after the transition.
   * These pointers allow us to store the transitions and
   * easily change what expression should be true after the
   * transition.
   * @param destExpr (*) the expression that needs to be proven
   * after the transition is executed.
   * @return None. */
  void getNewTrans(ExprNode* const destExpr) {
    if (destPar == nullptr) {
      rightExpr = destExpr;
    } else {
      if (isDestLeft) {
        destPar->setExprDestLeft(destExpr);
      } else {
        destPar->setExprDestRight(destExpr);
        rightExpr = destExpr;
      }
    }
  }

  /** Returns the clock set of the clocks reset by this transition.
   * @return the clocks reset by this transition. */
  const clock_set* reset_clocks() const { return resetList; }

  /** Given the location of a state that satisfies the
   * location constraints of the transition, this gives
   * the destination location after the transition. This method
   * helps augment a guard to ensure that the entering location's
   * invariant is satisfied.
   * @param source (*) The leaving location (the discrete state component).
   * @return The location entered after the transition has been executed from the source location. */
  const SubstList destination_location(const SubstList* const source_location) const {
    // Since a new substList is created, delete it when finished.
    if (destList == nullptr) {
      return *source_location;
    } else {
      return SubstList(destList, source_location);
    }
  }

  /** Prints out the transition to the desired output stream.
   * The typical output stream is cout.
   * @param t (*) The transition to print.
   * @param os (&) The type of output stream to print the output to.
   * @return none */
  inline void print(std::ostream& os) const {
    if (leftExpr != nullptr) {
      print_ExprNodeTrans(leftExpr, os);
    }
    os << "->";
    if (rightExpr != nullptr) {
      print_ExprNodeTrans(rightExpr, os);
    }
  }

private:
  /** parent pointer to destination to allow for easy modification
   * of expression for destination sequent. */
  ExprNode* destPar;
  /** if false, we have an imply node with the destination at the right.
   * otherwise, true means the destination expression is the left child
   * of destPar. */
  const bool isDestLeft;
  /** List of clock assignments in the edge. An empty list
   * means that there are no clock assignments on the edge.
   * Since assignments are executed
   * sequentially, the list is assumed to have no clock swaps
   * (i.e. no conflicts in clock assignments). By construction,
   * the innermost assignments are at the back. */
  const std::vector<std::pair<DBM::size_type, clock_value_t>>* clockAssignmentList;

  /** The enabling conditions of the transition. */
  const ExprNode* leftExpr;
  /** The destination (state change) of the transition. */
  ExprNode* rightExpr;

  /** A reference to the subList of the transition.
   * If there is no change in location, destList will be nullptr. */
  const SubstList* destList;

  /** The set of clocks to reset on the transition. This is nullptr
   * if there are no clocks to reset */
  const clock_set* resetList;
};

inline std::ostream& operator<<(std::ostream& os, const Transition* const t) {
  t->print(os);
  return os;
}

inline std::ostream& operator<<(std::ostream& os, const Transition& t) {
  t.print(os);
  return os;
}

#endif // TRANSITION_HH
