/** \file comp_ph.hh
 * Internal provers specialized to implications and transition guards.
 * @author Peter Fontana
 * @author Dezhuang Zhang
 * @author Rance Cleaveland
 * @author Jeroen Keiren
 * @copyright MIT Licence, see the accompanying LICENCE.txt
 */

#ifndef COMP_PH_HH
#define COMP_PH_HH

#include "ExprNode.hh"
#include "DBM.hh"
#include "DBMList.hh"

/** Internal prover to evaluate Boolean- and atomic expressions.
 * @param e The formula to evaluate
 * @param sublist The discrete state in which to evaluate e.
 * @return true if e is satisfied in the discreate state, false otherwise.
 */
inline bool eval_atomic(const ExprNode& e, const SubstList& discrete_state)
{
  switch (e.getOpType()) {
    case BOOL: {
      return (e.getBool());
    }
    case ATOMIC: {
      return (discrete_state.at(e.getAtomic()) == e.getIntVal());
    }
    case ATOMIC_NOT: {
      return (discrete_state.at(e.getAtomic()) != e.getIntVal());
    }
    case ATOMIC_LT: {
      return (discrete_state.at(e.getAtomic()) < e.getIntVal());
    }
    case ATOMIC_GT: {
      return (discrete_state.at(e.getAtomic()) > e.getIntVal());
    }
    case ATOMIC_LE: {
      return (discrete_state.at(e.getAtomic()) <= e.getIntVal());
    }
    case ATOMIC_GE: {
      return (discrete_state.at(e.getAtomic()) >= e.getIntVal());
    }
    default: {
      throw std::runtime_error("Not a valid condition");
    }
  }
}

/** Internal prover for evaluating if the sublist satisfies
 * the atomic proposition expression as the invariant precondition
 * for each invariant conjunct.
 * @param e The expression to evaluate; assumed to be the left hand side
 * of the invariant implication.
 * @param sublist The discrete location of the left hand side.
 * @return true: the expression evaluates to true, false: otherwise (if
 * the set of discrete and clock states satisfying the premise is empty).*/
inline bool comp_ph_invs(const ExprNode& e, const SubstList& discrete_state) {
  switch (e.getOpType()) {
    case OR:
    case OR_SIMPLE: {
      /* We only have atomic booleans so this simplified rule works. */
      return (comp_ph_invs(*(e.getLeft()), discrete_state) ||
              comp_ph_invs(*(e.getRight()), discrete_state));
    }
    case AND: {
      return (comp_ph_invs(*(e.getLeft()), discrete_state) &&
              comp_ph_invs(*(e.getRight()), discrete_state));
    }
    default: {
      return eval_atomic(e, discrete_state);
    }
  }
}

/** Takes in the specified DBM and tightens it
 * to satisfy the invariants required of the specified
 * discrete state. When finished, any nonempty DBM now satisfies
 * the invariants. This method is used when executing transitions
 * after a time successor (FORALL operator); If DBM lhs is the
 * time successor of zone z, after this method lhs will be the
 * time successor zone of z in location sub.
 * Remember:  The INVARIANT is assumed to be a list of clauses of:
 *		Prop = Val -> DBM Constraints.
 * @param invs A list of invariants.
 * @param lhs (*) The DBM to alter.
 * @param sub The discrete state (location variable assignment)
 * of the sequent.
 * @return true: the model has a non-vacuous invariant; false: otherwise. */
inline bool restrict_to_invariant(const std::vector<const ExprNode*>& invs,
                                  DBM& dbm, const SubstList& discrete_state) {
  bool has_nonvacuous_invariant = false;
  for (const ExprNode* invariant: invs) {
    if (comp_ph_invs(*invariant, discrete_state)) {
      dbm.intersect(*invariant->dbm());
      has_nonvacuous_invariant = true;
    }
  }
  return has_nonvacuous_invariant;
}

/** Takes in the specified DBMList and tightens it
 * to satisfy the invariants required of the specified
 * discrete state. When finished, any nonempty DBMList now satisfies
 * the invariants. This method is used when executing transitions
 * after a time successor (FORALL operator); If DBMList lhs is the
 * time successor of set of valuations z, after this method lhs will be the
 * time successor the set of valuations z in location sub.
 * Remember:  The INVARIANT is assumed to be a list of clauses of:
 *		Prop = Val -> DBM Constraints. (all constraints are clock zones)
 * @param invs A list of invariants.
 * @param lhs (*) The DBMList to alter.
 * @param discrete_state The discrete state (location variable assignment)
 * of the sequent.
 * @return true: the DBMList is changed, so there is an invariant that is not vacuously satisfied in the context of the dbmlist. */
inline bool restrict_to_invariant(const std::vector<const ExprNode*>& invs,
                                  DBMList& dbms, const SubstList& discrete_state) {
  bool has_nonvacuous_invariant = false;
  if(!invs.empty()) {
    for(DBM* dbm: dbms) {
      has_nonvacuous_invariant = restrict_to_invariant(invs, *dbm, discrete_state) || has_nonvacuous_invariant; // order is important
    }
  }
  if (has_nonvacuous_invariant) {
    dbms.setIsCfFalse(false);
  }
  return has_nonvacuous_invariant;
}

/** Simplified and performance-optimized proof engine for (AllAct) transitions
 * and IMPLY nodes. This method assumes that the expression e
 * is either the left hand side of an IMPLY node or the conditions
 * of a transition. Given the assumption that it is working on the left
 * hand implication of a possible transition (potentially with an invariant),
 * it utilizes a simpler proof-rule scheme. Using comp_ph(...) instead
 * of do_proof(...) (or do_proof_place(...)) results in faster performance
 * since it can be specialized for this specific subset of PES. This prover
 * evaluates the fed in expression to true or false.
 * Since the comp_ph(...) constraints are often guards and the DBM
 * is a clock zone, to find the set of clock valuations that can execute
 * this transition from the fed in DBM, comp_ph(...)
 * tightens the DBM to satisfy the constraints (assumed to be in the left
 * hand-side of an implication). It returns false if the set of constraints
 * is empty.
 * @param zone (*) The DBM representing the clock constraints.
 * @param e (*) The expression to evaluate; assumed to be the left hand side
 * of an implication or the conditions of a transition.
 * @param discrete_state (*) The discrete location of the left hand side.
 * @return true: the expression evaluates to true (and ph is
 * tightened to make the expression true), false: otherwise (if
 * the set of discrete and clock states satisfying the premise is empty).
 * @post ph is in canonical form if it was already in canonical form before. */
inline bool comp_ph(DBM& zone, const ExprNode& e,
                    const SubstList& discrete_state) {
  switch (e.getOpType()) {
    case OR:
    case OR_SIMPLE: {
      /* This OR rule only works when there is at most one constraint.
       * By definition of its input, we have a discrete state (with
       * && and || nodes) conjuncted with an intersection of constraints.
       * By construction of the fed input to this function, the above
       * bad case will never occur. */
      return (comp_ph(zone, *(e.getLeft()), discrete_state) ||
              comp_ph(zone, *(e.getRight()), discrete_state));
    }
    case AND: {
      return (comp_ph(zone, *(e.getLeft()), discrete_state) &&
              comp_ph(zone, *(e.getRight()), discrete_state));
    }
    case CONSTRAINT: {
      zone.intersect(*(e.dbm()));
      zone.cf(); // Calls Canonical Form Here.
      return !(zone.emptiness());
    }
    default: {
      return eval_atomic(e, discrete_state);
    }
  }
}

/** Simplified and performance-optimized proof engine for (ExistAct) transitions
 * and AND nodes within placeholders. This method assumes that the expression e
 * is either the left hand side of an AND node or the conditions
 * of a transition. In both cases, there is a placeholder DBM.
 * Given the assumption that its is working on the left
 * hand implication of a possible transition (potentially with an invariant),
 * it utilizes a simpler proof-rule scheme. Using comp_ph(...) instead
 * of do_proof(...) (or do_proof_place(...)) results in faster performance
 * since it can be specialized for this specific subset of PES. This prover
 * evaluates the fed in expression to true or false.
 * For this method, the placeholder is tightened to satisfy the constraints.
 * @param zone (*) The DBM representing the clock constraints.
 * @param place (*) The DBMList placeholder.
 * @param e The expression to evaluate; assumed to be the left hand side
 * of an implication or the conditions of a transition.
 * @param discrete_state The discrete location of the left hand side.
 * @return true: the expression evaluates to true (and ph is
 * tightened to make the expression true), false: otherwise (if
 * the set of discrete and clock states satisfying the premise is empty).*/
inline bool comp_ph_exist_place(DBM& zone, DBMList& place,
                                const ExprNode& e, const SubstList& discrete_state) {
  switch (e.getOpType()) {
    case OR:
    case OR_SIMPLE: {
      /* This OR rule only works when there is at most one constraint.
       * By definition of its input, we have a discrete state (with
       * && and || notes) conjuncted with an intersection of constraints.
       * By construction of the fed input to this function, the above
       * bad case will never occur. */
      return (comp_ph_exist_place(zone, place, *(e.getLeft()), discrete_state) ||
              comp_ph_exist_place(zone, place, *(e.getRight()), discrete_state));
    }
    case AND: {
      return (comp_ph_exist_place(zone, place, *(e.getLeft()), discrete_state) &&
              comp_ph_exist_place(zone, place, *(e.getRight()), discrete_state));
    }
    case CONSTRAINT: {
      zone.cf();
      if (zone <= (*e.dbm())) {
        return true;
      } else {
      zone.intersect(*e.dbm());
      zone.cf(); // Calls Canonical Form Here.
        if (zone.emptiness()) {
        // We can only tighten if the constraint is not empty
        return false;
      } else {
        /* For now, assume that the placeholder
         * becomes the entire constraint.
         * It may be necessary to make placeholder looser than
         * the constraint to not have inequalities that ph satisfies. */
        place.intersect(*e.dbm());
        place.cf();
        return !place.emptiness();
      }
    }
    }
    default: {
      return eval_atomic(e, discrete_state);
    }
  }
}

/** Simplified and performance-optimized proof engine for (AllAct) transitions
 * and IMPLY nodes within placeholders. To handle potential complexities later
 * in the proof (when getting a final placeholder), this method takes the guard
 * and tightens the LHS and the placeholder, so the placeholder can be altered
 * if needed.
 * @param zone (*) The DBM representing the clock constraints.
 * @param place (*) The DBMList placeholder to tighten with the guard.
 * @param e The expression to evaluate; assumed to be the left hand side
 * of an implication or the conditions of a transition.
 * @param discrete_state The discrete location of the left hand side.
 * @return true: the expression evaluates to true (and ph is
 * tightened to make the expression true), false: otherwise (if
 * the set of discrete and clock states satisfying the premise is empty).*/
inline bool comp_ph_all_place(DBM& zone, DBMList& place,
                              const ExprNode& e, const SubstList& discrete_state) {
  switch (e.getOpType()) {
    case OR:
    case OR_SIMPLE: {
      /* This OR rule only works when there is at most one constraint.
       * By definition of its input, we have a discrete state (with
       * && and || notes) conjuncted with an intersection of constraints.
       * By construction of the fed input to this function, the above
       * bad case will never occur. */
      return (comp_ph_all_place(zone, place, *(e.getLeft()), discrete_state) ||
              comp_ph_all_place(zone, place, *(e.getRight()), discrete_state));
    }
    case AND: {
      return (comp_ph_all_place(zone, place, *(e.getLeft()), discrete_state) &&
              comp_ph_all_place(zone, place, *(e.getRight()), discrete_state));
    }
    case CONSTRAINT: {
      zone.intersect(*e.dbm());
      zone.cf(); // Calls Canonical Form Here.
      if (zone.emptiness()) {
        return false;
      } else {
      place.intersect(*e.dbm());
      place.cf();
      return !place.emptiness();
    }
    }
    default: {
      return eval_atomic(e, discrete_state);
    }
  }
}

#endif // COMP_PH_HH
