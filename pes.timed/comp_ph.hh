#ifndef COMP_PH_HH
#define COMP_PH_HH

#include "ExprNode.hh"
#include "DBM.hh"
#include "DBMList.hh"

/** Internal prover for evaluating if the sublist satisfies
 * the atomic proposition expression as the invariant precondition
 * for each invariant conjunct.
 * @param e (*) The expression to evaluate; assumed to be the left hand side
 * of the invariant implication.
 * @param sublist (*) The discrete location of the left hand side.
 * @return true: the expression evaluates to true, false: otherwise (if
 * the set of discrete and clock states satisfying the premise is empty).*/
inline bool comp_ph_invs(const ExprNode& e, const SubstList &sublist)
{
  switch (e.getOpType())
  {
    case ATOMIC : {
      return (sublist.at(e.getAtomic()) == e.getIntVal());
      break; }
    case ATOMIC_NOT : {
      return (sublist.at(e.getAtomic()) != e.getIntVal());
      break; }
    case ATOMIC_LT : {
      return (sublist.at(e.getAtomic()) < e.getIntVal());
      break; }
    case ATOMIC_GT : {
      return (sublist.at(e.getAtomic()) > e.getIntVal());
      break; }
    case ATOMIC_LE : {
      return (sublist.at(e.getAtomic()) <= e.getIntVal());
      break; }
    case ATOMIC_GE : {
      return (sublist.at(e.getAtomic()) >= e.getIntVal());
      break; }
    case AND : {
      return (comp_ph_invs(*(e.getLeft()), sublist)
              &&
              comp_ph_invs(*(e.getRight()), sublist));
      break; }
    case OR :
    case OR_SIMPLE : {
      /* We only have atomic booleans so this simplified rule works. */
      return (comp_ph_invs(*(e.getLeft()), sublist)
              ||
              comp_ph_invs(*(e.getRight()), sublist));
      break; }
    default: {
      cerr << "Not a valid condition" <<endl;
      exit(1); }
  }
  return false;
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
 * @param lhs (*) The DBM to alter.
 * @param sub (*) The discrete state (location variable assignment)
 * of the sequent.
 * @return true: the model has a non-vacuous invariant; false: otherwise. */
inline bool invs_chk(const vector<ExprNode *>& invs, DBM * const lhs, const SubstList& sub){
  bool outRes = false;
  if (invs.empty()) return false;
  for (int i=0; i < sub.nElements(); i++){
    for (vector<ExprNode*>::const_iterator it = invs.begin(); it != invs.end(); ++it){
      if (comp_ph_invs(*(*it), sub)) {
        (*lhs) & (*(*it)->dbm()) ;
        outRes = true;
      }
    }
  }
  return outRes;
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
 * @param lhs (*) The DBMList to alter.
 * @param sub (*) The discrete state (location variable assignment)
 * of the sequent.
 * @return true: the DBMList is changed; false: otherwise. */
inline bool invs_chk(const vector<ExprNode *>& invs, DBMList * const lhs, const SubstList& sub){
  bool outRes = false;
  if (invs.empty()) return false;
  vector<DBM *> * lList = lhs->getDBMList();
  for(unsigned int i = 0; i < lList->size(); i++) {
    bool temp = invs_chk(invs, (*lList)[i], sub);
    outRes = temp || outRes;
  }
  return outRes;
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
 * @param ph (*) The DBM representing the clock constraints.
 * @param e (*) The expression to evaluate; assumed to be the left hand side
 * of an implication or the conditions of a transition.
 * @param sublist (*) The discrete location of the left hand side.
 * @return true: the expression evaluates to true (and ph is
 * tightened to make the expression true), false: otherwise (if
 * the set of discrete and clock states satisfying the premise is empty).*/
inline bool comp_ph(DBM * const ph, const ExprNode& e, const SubstList& sublist)
{
  switch (e.getOpType())
  {
    case CONSTRAINT : {
      (*ph) & (*(e.dbm()));
      ph->cf(); // Calls Canonical Form Here.
      return (!(ph->emptiness()));
      break; }
    case BOOL : {
      return (e.getBool());
      break; }
    case ATOMIC : {
      return (sublist.at(e.getAtomic()) == e.getIntVal());
      break; }
    case ATOMIC_NOT : {
      return (sublist.at(e.getAtomic()) != e.getIntVal());
      break; }
    case ATOMIC_LT : {
      return (sublist.at(e.getAtomic()) < e.getIntVal());
      break; }
    case ATOMIC_GT : {
      return (sublist.at(e.getAtomic()) > e.getIntVal());
      break; }
    case ATOMIC_LE : {
      return (sublist.at(e.getAtomic()) <= e.getIntVal());
      break; }
    case ATOMIC_GE : {
      return (sublist.at(e.getAtomic()) >= e.getIntVal());
      break; }
    case AND : {
      return (comp_ph(ph, *(e.getLeft()), sublist)
              &&
              comp_ph(ph, *(e.getRight()), sublist));
      break; }
    case OR :
    case OR_SIMPLE : {
      /* This OR rule only works when there is at most one constraint.
       * By definition of its input, we have a discrete state (with
       * && and || notes) conjuncted with an intersection of constraints.
       * By construction of the fed input to this function, the above
       * bad case will never occur. */
      return (comp_ph(ph, *(e.getLeft()), sublist)
              ||
              comp_ph(ph, *(e.getRight()), sublist));
      break; }
    default: {
      cerr << "Not a valid condition" <<endl;
      exit(1); }
  }
  return false;
}


/** Simplified and performance-optimized proof engine for (ExistAct) transitions
 * and AND nodes. This method assumes that the expression e
 * is either the left hand side of an AND node or the conditions
 * of a transition. Given the assumption that its is working on the left
 * hand implication of a possible transition (potentially with an invariant),
 * it utilizes a simpler proof-rule scheme. Using comp_ph(...) instead
 * of do_proof(...) (or do_proof_place(...)) results in faster performance
 * since it can be specialized for this specific subset of PES. This prover
 * evaluates the fed in expression to true or false.
 * For this method, the DBM must completely satisfy all clock constraints;
 * it is not tightened by the prover.
 * @param ph (*) The DBM representing the clock constraints.
 * @param e (*) The expression to evaluate; assumed to be the left hand side
 * of an implication or the conditions of a transition.
 * @param sublist (*) The discrete location of the left hand side.
 * @return true: the expression evaluates to true (and ph is
 * tightened to make the expression true), false: otherwise (if
 * the set of discrete and clock states satisfying the premise is empty).*/
inline bool comp_ph_exist(DBM * const ph, const ExprNode& e, const SubstList& sublist)
{
  switch (e.getOpType())
  {
    case CONSTRAINT : {
      ph->cf();
      return (*ph) <= (*(e.dbm()));
      break; }
    case BOOL : {
      return (e.getBool());
      break; }
    case ATOMIC : {
      return (sublist.at(e.getAtomic()) == e.getIntVal());
      break; }
    case ATOMIC_NOT : {
      return (sublist.at(e.getAtomic()) != e.getIntVal());
      break; }
    case ATOMIC_LT : {
      return (sublist.at(e.getAtomic()) < e.getIntVal());
      break; }
    case ATOMIC_GT : {
      return (sublist.at(e.getAtomic()) > e.getIntVal());
      break; }
    case ATOMIC_LE : {
      return (sublist.at(e.getAtomic()) <= e.getIntVal());
      break; }
    case ATOMIC_GE : {
      return (sublist.at(e.getAtomic()) >= e.getIntVal());
      break; }
    case AND : {
      return (comp_ph_exist(ph, *(e.getLeft()), sublist)
              &&
              comp_ph_exist(ph, *(e.getRight()), sublist));
      break; }
    case OR :
    case OR_SIMPLE : {
      /* This OR rule only works when there is at most one constraint.
       * By definition of its input, we have a discrete state (with
       * && and || notes) conjuncted with an intersection of constraints.
       * By construction of the fed input to this function, the above
       * bad case will never occur. */
      return (comp_ph_exist(ph, *(e.getLeft()), sublist)
              ||
              comp_ph_exist(ph, *(e.getRight()), sublist));
      break; }
    default: {
      cerr << "Not a valid condition" <<endl;
      exit(1); }
  }
  return false;
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
 * @param ph (*) The DBM representing the clock constraints.
 * @param place (*) The DBMList placeholder.
 * @param e (*) The expression to evaluate; assumed to be the left hand side
 * of an implication or the conditions of a transition.
 * @param sublist (*) The discrete location of the left hand side.
 * @return true: the expression evaluates to true (and ph is
 * tightened to make the expression true), false: otherwise (if
 * the set of discrete and clock states satisfying the premise is empty).*/
inline bool comp_ph_exist_place(DBM * const ph, DBMList * const place,
                                const ExprNode& e, const SubstList& sublist)
{
  switch (e.getOpType())
  {
    case CONSTRAINT : {
      ph->cf();
      const DBM * eDBM = e.dbm();
      bool res = (*ph) <= (*eDBM);
      (*ph) & (*eDBM);
      ph->cf(); // Calls Canonical Form Here.
      if(res) {
        return true;
      }
      // We can only tighten if the constraint is not empty
      if(ph->emptiness()) {
        return false;
      }
      /* For now, assume that the placeholder
       * becomes the entire constraint.
       * It may be necessary to make placeholder looser than
       * the constraint to not have inequalities that ph satisfies. */
      *place & (*(e.dbm()));
      place->cf();
      return !(place->emptiness());
      break; }
    case BOOL : {
      return (e.getBool());
      break; }
    case ATOMIC : {
      return (sublist.at(e.getAtomic()) == e.getIntVal());
      break; }
    case ATOMIC_NOT : {
      return (sublist.at(e.getAtomic()) != e.getIntVal());
      break; }
    case ATOMIC_LT : {
      return (sublist.at(e.getAtomic()) < e.getIntVal());
      break; }
    case ATOMIC_GT : {
      return (sublist.at(e.getAtomic()) > e.getIntVal());
      break; }
    case ATOMIC_LE : {
      return (sublist.at(e.getAtomic()) <= e.getIntVal());
      break; }
    case ATOMIC_GE : {
      return (sublist.at(e.getAtomic()) >= e.getIntVal());
      break; }
    case AND : {
      return (comp_ph_exist_place(ph, place, *(e.getLeft()), sublist)
              &&
              comp_ph_exist_place(ph, place, *(e.getRight()), sublist));
      break; }
    case OR :
    case OR_SIMPLE : {
      /* This OR rule only works when there is at most one constraint.
       * By definition of its input, we have a discrete state (with
       * && and || notes) conjuncted with an intersection of constraints.
       * By construction of the fed input to this function, the above
       * bad case will never occur. */
      return (comp_ph_exist_place(ph, place, *(e.getLeft()), sublist)
              ||
              comp_ph_exist_place(ph, place, *(e.getRight()), sublist));
      break; }
    default: {
      cerr << "Not a valid condition" <<endl;
      exit(1); }
  }
  return false;
}

/** Simplified and performance-optimized proof engine for (AllAct) transitions
 * and IMPLY nodes within placeholders. To handle potential complexities later
 * in the proof (when getting a final placeholder), this method takes the guard
 * and tightens the LHS and the placeholder, so the placeholder can be altered
 * if needed.
 * @param ph (*) The DBM representing the clock constraints.
 * @param place (*) The DBMList placeholder to tighten with the guard.
 * @param e (*) The expression to evaluate; assumed to be the left hand side
 * of an implication or the conditions of a transition.
 * @param sublist (*) The discrete location of the left hand side.
 * @return true: the expression evaluates to true (and ph is
 * tightened to make the expression true), false: otherwise (if
 * the set of discrete and clock states satisfying the premise is empty).*/
inline bool comp_ph_all_place(DBM * const ph, DBMList * const place,
                              const ExprNode& e, const SubstList& sublist)
{
  switch (e.getOpType())
  {
    case CONSTRAINT : {
      (*ph) & (*(e.dbm()));
      ph->cf(); // Calls Canonical Form Here.
      bool lhEmpty;
      lhEmpty = ph->emptiness();
      if(lhEmpty) {
        return false;
      }
      *place & (*(e.dbm()));
      place->cf();
      if(place->emptiness()) {
        return false;
      }
      return true;
      break; }
    case BOOL : {
      return (e.getBool());
      break; }
    case ATOMIC : {
      return (sublist.at(e.getAtomic()) == e.getIntVal());
      break; }
    case ATOMIC_NOT : {
      return (sublist.at(e.getAtomic()) != e.getIntVal());
      break; }
    case ATOMIC_LT : {
      return (sublist.at(e.getAtomic()) < e.getIntVal());
      break; }
    case ATOMIC_GT : {
      return (sublist.at(e.getAtomic()) > e.getIntVal());
      break; }
    case ATOMIC_LE : {
      return (sublist.at(e.getAtomic()) <= e.getIntVal());
      break; }
    case ATOMIC_GE : {
      return (sublist.at(e.getAtomic()) >= e.getIntVal());
      break; }
    case AND : {
      return (comp_ph_all_place(ph, place, *(e.getLeft()), sublist)
              &&
              comp_ph_all_place(ph, place, *(e.getRight()), sublist));
      break; }
    case OR :
    case OR_SIMPLE : {
      /* This OR rule only works when there is at most one constraint.
       * By definition of its input, we have a discrete state (with
       * && and || notes) conjuncted with an intersection of constraints.
       * By construction of the fed input to this function, the above
       * bad case will never occur. */
      return (comp_ph_all_place(ph, place, *(e.getLeft()), sublist)
              ||
              comp_ph_all_place(ph, place, *(e.getRight()), sublist));
      break; }
    default: {
      cerr << "Not a valid condition" <<endl;
      exit(1); }
  }
  return false;
}

#endif // COMP_PH_HH