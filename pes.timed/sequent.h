/** The internal representation of a proof sequent with
 * a (potential) union of clock zones for the clock state.
 * A sequent with a placeholder is a
 * DBM, DBMList [SubstList] |- RHS. For storage efficiency, the Sequent class
 * is set of sequents a DBM', DBMList' [SubstList] |- RHS, with ds
 * the vector representing the list of DBM' DBMList' pairs.
 * For performance purposes, the implementation confines
 * unions of clock zones to the placeholder DBMList. (This is sufficient
 * to guarantee that the model checker is sound and complete).
 * This storage is used
 * to store multiple sequents, not a sequent consisting of a union of DBMs.
 * The SubstList represents the discrete location state (as variables). This
 * method of storing sequents improves the efficiency of sequent caching.
 *
 * This SequentPlace Class representation is closely utilized in
 * locate_sequentPlace(), update_sequentPlace() and tabled_sequentPlace()
 * in the demo.cc implementation.
 *
 *
 * @author Peter Fontana
 * @author Dezhuang Zhang
 * @author Rance Cleaveland
 * @author Jeroen Keiren
 * @copyright MIT Licence, see the accompanying LICENCE.txt
 * @note Many functions are inlined for better performance.
 */

#ifndef SEQUENT_HH
#define SEQUENT_HH

#include "cpplogging/logger.h"
#include "ExprNode.h"

class Sequent;
class SequentPlace; // forward declaration for parent scope

/** This defines a DBMset as a vector of DBM
 * arrays (DBM Arrays). */
typedef std::vector<DBM*> DBMset;

std::ostream& operator<<(std::ostream& os, const Sequent& s);
std::ostream& operator<<(std::ostream& os, const SequentPlace& s);

std::ostream& operator<<(std::ostream& os, const DBMset& dbms) {
  os << "{ ";
  for(DBMset::const_iterator i = dbms.begin(); i != dbms.end(); ++i) {
    if(std::distance(dbms.begin(), i) > 0) {
      os << ", ";
    }
    os << **i;
  }
  os << " }";
  return os;
}

/** The internal representation of a proof sequent with
 * a clock zone for the clock state. A sequent is a
 * DBM, [SubstList] |- RHS. For storage efficiency, the Sequent class
 * is set of sequents a DBM' [SubstList] |- RHS, with ds
 * the vector representing the list of DBMs DBM'. This storage is used
 * to store multiple sequents, not a sequent consisting of a union of DBMs.
 * The SubstList represents the discrete location state (as variables).This
 * method of storing sequents improves the efficiency of sequent caching.
 *
 * @author Peter Fontana, Dezhuang Zhang, and Rance Cleaveland.
 * @version 1.2
 * @date November 2, 2013 */
class Sequent {
public:
  /** Constructor to make an Sequent = (ExprNode, SubstList) object,
   * with an empty set of DBMs. Until a DBM is specified as a clock
   * state, the sequent is empty.
   * @param rhs (*) The right hand expression of the sequent.
   * @param sub (*) The discrete state component of the left side
   * of the sequent.
   * @return [Constructor]. */
  Sequent(const ExprNode *const rhs, const SubstList *const discrete_state)
      : m_rhs(rhs),
        m_discrete_state(new SubstList(*discrete_state))
  {}

  /* A default Copy Constructor is implemented by the
   * compiler which performs a member-wise deep copy. */

  /** Destructor. It does not delete the right hand expression rhs
   * because rhs may be used in multiple sequents. The expression tree
   * storing rhs will delete it when the proof finishes. Likewise,
   * since each parent sequent (with or without a placeholder) can
   * delete itself, the destructor does not delete parent sequents.
   * @return [Destructor] */
  ~Sequent() {
    delete m_discrete_state;
    // Iterate Through and Delete every element of ds
    delete_vector_elements(m_dbms);
    m_dbms.clear();
    // Do not delete e since it is a pointer to the overall ExprNode.
    // Do not delete parent sequent upon deletion
    // Do not delete parent placeholder sequent
    // Clearing vectors is enough
    m_parent_sequents.clear();
  }

  /** Returns the ExprNode element (rhs or consequent) of the Sequent.
   * @return the rhs expression of the ExprNode element of the Sequent. */
  const ExprNode *rhs() const { return m_rhs; }

  /** Returns the discrete state of the sequent's left (the SubstList).
   * @return the discrete state of the sequent's left (the SubstList). */
  const SubstList *discrete_state() const { return m_discrete_state; }

  /** Add a parent sequent */
  void addParent(Sequent *s) {
    cpplog(cpplogging::debug1, "sequent") << "Adding " << *s << " as parent of " << *this << std::endl;
    m_parent_sequents.push_back(s);
  }

  /** Get parent sequents */
  const std::vector<Sequent *> &parents() const { return m_parent_sequents; }

  const DBMset &dbm_set() const { return m_dbms; }

  DBMset &dbm_set() { return m_dbms; }

  /** Adds a sequent (better: the left hand side of the sequent), to the set of
   * sequents represented by this Sequent object */
  void push_sequent(DBM *lhs) { m_dbms.push_back(lhs); }

  /** Removes the last added sequent from the set of sequents represented by
   * this object */
  void pop_sequent() {
    delete m_dbms.back();
    m_dbms.pop_back();
  }

  /** Delete sequents and clear the vector */
  void delete_sequents() {
    delete_vector_elements(m_dbms);
    m_dbms.clear();
  }

  /** Using that a Sequent object is a set of sequents with matching rhs and
   *  discrete states with different clock states, determines if the specified
   * DBM is contained within one of the sequents. This is used for greatest
   * fixpoint circularity (or known true sequents), since by definition
   * of sequents, if sequent B is true and A <= B (the right hand side matches
   * and the left hand state of A is a subset of the states in B), A is also
   * true. For this method, each B *(*it) is a known sequent and lhs is the
   * clock state of A. This method assumes that the right hand side and discrete
   * states match (and is often called after locate_sequent() or
   * look_for_sequent()); hence, it only needs to compare clock states.
   * @param lhs (*) The DBM to compare the sequent's DBMs to.
   * @return true: lhs <= some sequent in s
   * (consequently, the sequent is true), false: otherwise.*/
  bool tabled_sequent(const DBM& lhs) const {
    return std::any_of(m_dbms.begin(), m_dbms.end(), [&lhs](const DBM* x) { return *x >= lhs; });
  }

  /** Using that a Sequent object is a set of sequents with matching rhs and
   *  discrete states with different clock states, determines if the specified
   * DBM is contains one of the sequents. This is used for known false
   * sequents, since by definition
   * of sequents, if sequent B is false and B <= A (the right hand side matches
   * and the left hand state of B is a subset of the states in A), A is false.
   * For this method, each B *(*it) is a known sequent and lhs is the clock
   * state of A. This method assumes that the right hand side and discrete
   * states match (and is often called after locate_sequent() or
   * look_for_sequent()); hence, it only needs to compare clock states.
   * @param s (*) The sequent that contains a set of DBMs.
   * @param lhs (*) The DBM to compare the sequent's DBMs to.
   * @return true: lhs >= some sequent in s
   * (consequently, the sequent is false), false: otherwise.*/
  bool tabled_false_sequent(const DBM& lhs) const {
    return std::any_of(m_dbms.begin(), m_dbms.end(), [&lhs](const DBM* x) { return *x <= lhs; });
  }

  /** Using that a Sequent object is a set of sequents with matching rhs and
   *  discrete states with different clock states, determines if the specified
   * DBM equals one of the sequents. This is used for least fixpoint
   * sequents and checks for sequent equality. For least fixpoint circularity,
   * if an equal sequent is found then this sequent is false.
   * This method assumes that the right hand side and discrete states match
   * (and is often called after locate_sequent() or look_for_sequent()); hence,
   * it only needs to compare clock states.
   * @param s (*) The sequent that contains a set of DBMs.
   * @param lhs (*) The DBM to compare the sequent's DBMs to.
   * @return true: lhs <= some sequent in s, false: otherwise.*/
  bool tabled_sequent_lfp(const DBM& lhs) {
    return tabled_sequent(lhs);
  }

  /** Takes in set of known true sequents (s) with a newly
   * established true clock state (lhs) and adds clock state (lhs)
   * to the set of sequents in s. In the update, the
   * DBM lhs is copied. By definition, a sequent B is true
   * if and only if all of its states satisfy the right hand side. Hence,
   * if any known clock state is contained in lhs (B <= lhs),
   * we can enlarge that clock
   * state (enlarge B). This is more efficient (for searching) than just adding
   * an additional sequent.
   * @param s (*) The set of known sequents to update.
   * @param lhs (*) The DBM of the newly-established clock state. */
  void update_sequent(const DBM& lhs) {
    DBMset::iterator it = std::find_if(m_dbms.begin(), m_dbms.end(), [&lhs](const DBM*x) {
      return *x <= lhs;
    });
    if(it == m_dbms.end()) {
      m_dbms.emplace_back(new DBM(lhs));
    } else {
      **it = lhs;
    }
  }

  /** Takes in set of known false sequents (s) with a newly
   * established false clock state (lhs) and adds clock state (lhs)
   * to the set of sequents in s. In the update, the
   * DBM lhs is copied. By definition, a sequent B is false
   * if and only if it has a clocks state that does not satisfy the right
   * side. Hence,
   * if any known clock state is contains (B >= lhs),
   * we can refine that clock
   * state (shrink B). This is more efficient (for searching) than just adding
   * an additional sequent.
   * @param s (*) The set of known sequents to update.
   * @param lhs (*) The DBM of the newly-established clock state. */
  void update_false_sequent(const DBM& lhs) {
    DBMset::iterator it = std::find_if(m_dbms.begin(), m_dbms.end(), [&lhs](const DBM*x) {
      return *x >= lhs;
    });
    if(it == m_dbms.end()) {
      m_dbms.emplace_back(new DBM(lhs));
    } else {
      **it = lhs;
    }
  }


  void print(std::ostream& os) const {
    os << "(" << *m_discrete_state << ", " << m_dbms << " |- " << *m_rhs;
  }

protected:
  /** The right hand side expression of the sequent. */
  const ExprNode *m_rhs;
  /** The discrete state of the left of a sequent, represented
   * as a SubstList. */
  const SubstList *m_discrete_state;
  /** A list of DBMs stored in the sequent, used to store a set of sequents
   * in a method for easy access during sequent caching. This vector
   * stores the clock state part of the left hand side of each sequent.
   * Each element in ds is combined with the location state (st)
   * and the right hand expression (e) to form a proof sequent
   * in the proof tree. */
  DBMset m_dbms;

  /** The sequent parent to this sequent in the proof tree; this is used
   * to quickly access backpointers. A sequent either has a parent
   * with a placeholder (parSequentPlace) or a parent without a
   * placeholder (parSequent). */
  std::vector<Sequent *> m_parent_sequents;
};

/** Defines a vector of (DBM, DBMList) pairs. Used for lists
 * of placeholder proofs, since (for faster performance) the union
 * of clock zones is restricted to placeholders. */
typedef std::vector<std::pair<DBM *, DBMList *> > DBMPlaceSet;

std::ostream& operator<<(std::ostream& os, const DBMPlaceSet& dbms) {
  os << "{ ";
  for(DBMPlaceSet::const_iterator i = dbms.begin(); i != dbms.end(); ++i) {
    if(std::distance(dbms.begin(), i) > 0) {
      os << ", ";
    }
    os << "(" << *(i->first) << ", " << *(i->second);
  }
  os << " }";
  return os;
}

/** The internal representation of a proof sequent with
 * a (potential) union of clock zones for the clock state.
 * A sequent with a placeholder is a
 * DBM, DBMList [SubstList] |- RHS. For storage efficiency, the Sequent class
 * is set of sequents a DBM', DBMList' [SubstList] |- RHS, with ds
 * the vector representing the list of DBM' DBMList' pairs.
 * For performance purposes, the implementation confines
 * unions of clock zones to the placeholder DBMList. (This is sufficient
 * to guarantee that the model checker is sound and complete).
 * This storage is used
 * to store multiple sequents, not a sequent consisting of a union of DBMs.
 * The SubstList represents the discrete location state (as variables). This
 * method of storing sequents improves the efficiency of sequent caching.
 *
 * This SequentPlace Class representation is closely utilized in
 * locate_sequentPlace(), update_sequentPlace() and tabled_sequentPlace()
 * in the demo.cc implementation.
 *
 * @author Peter Fontana, Dezhuang Zhang, and Rance Cleaveland.
 * @note Many functions are inlined for better performance.
 * @version 1.2
 * @date November 2, 2013 */
class SequentPlace {
public:
  /** Constructor to make an Sequent = (ExprNode, SubstList) object,
   * with an empty set of (DBM, DBMList) pairs. Until a
   * (DBM, DBMList) pair is specified as a clock
   * state, the sequent is empty.
   * @param rhs (*) The right hand expression of the sequent.
   * @param sub (*) The discrete state component of the left side
   * of the sequent.
   * @return [Constructor]. */
  SequentPlace(const ExprNode *const rhs, const SubstList *const discrete_state)
      : m_rhs(rhs), m_discrete_state(new SubstList(*discrete_state)) {}

  /* A default Copy Constructor is implemented by the
   * compiler which performs a member-wise deep copy.
   * Note: this copy copies pointers to the objects
   * in the vectors. Thus, consider avoiding. */

  /** Destructor. It does not delete the right hand expression e
   * because e may be used in multiple sequents. The expression tree
   * storing e will delete it when the proof finishes. Likewise,
   * since each parent sequent (with or without a placeholder) can
   * delete itself, the destructor does not delete parent sequents.
   * @return [Destructor] */
  ~SequentPlace() {
    delete m_discrete_state;
    // Iterate Through and Delete every element of ds
    for (std::pair<DBM*, DBMList*> p: m_dbms) {
      delete p.first;
      delete p.second;
    }
    m_dbms.clear();
    // Do not delete e since it is a pointer to the overall ExprNode.

    // Do not delete parent sequent parSequentPlace
    // Do not delete parent sequent parSequent
    // Clearing vectors is enough
    m_parent_sequents.clear();
    m_parent_sequents_placeholder.clear();
  }

  /** Returns the ExprNode element (rhs or consequent) of the Sequent.
   * @return the rhs expression of the ExprNode element of the Sequent. */
  const ExprNode* rhs() const { return m_rhs; }

  /** Returns the discrete state of the sequent's left (the SubstList).
   * @return the discrete state of the sequent's left (the SubstList). */
  const SubstList* discrete_state() const { return m_discrete_state; }

  const DBMPlaceSet& dbm_set() const { return m_dbms; }

  DBMPlaceSet& dbm_set() { return m_dbms; }

  /** Adds a sequent (better: the left hand side of the sequent), to the set of
   * sequents represented by this Sequent object */
  void push_sequent(const std::pair<DBM *, DBMList *>& s) {
    assert((s.second)->isInCf());
    m_dbms.push_back(s);
  }

  /** Removes the last added sequent from the set of sequents represented by
   * this object */
  void pop_sequent() {
    std::pair<DBM *, DBMList *> b = m_dbms.back();
    delete b.first;
    delete b.second;
    m_dbms.pop_back();
  }

  /** Delete sequents and clear the vector */
  void delete_sequents() {
    for (std::pair<DBM*, DBMList*> p: m_dbms) {
      delete p.first;
      delete p.second;
    }
    m_dbms.clear();
  }

  /** Add a parent sequent */
  void addParent(Sequent *s) {
    cpplog(cpplogging::debug1, "sequent") << "Adding " << *s << " as parent of " << *this << std::endl;
    m_parent_sequents.push_back(s);
  }

  /** Add a parent sequent (with placeholder) */
  void addParent(SequentPlace *s) {
    cpplog(cpplogging::debug1, "sequent") << "Adding " << *s << " as parent of " << *this << std::endl;
    m_parent_sequents_placeholder.push_back(s);
  }

  /** Get parent sequents */
  const std::vector<Sequent *> &parents() const { return m_parent_sequents; }

  /** Get parent sequents (with placeholders) */
  const std::vector<SequentPlace *> &parents_with_placeholders() const {
    return m_parent_sequents_placeholder;
  }

  /** Using that a Sequent object is a set of sequents with matching rhs and
   *  discrete states with different clock states, determines if the specified
   * clock state is contained within one of the sequents. For performance
   * reasons, if the sequent is found in here, its placeholder is restricted
   * to be the largest placeholder possible.
   * This is used for known true sequents, since by definition
   * of sequents, if sequent B is true and A <= B (the right hand side matches
   * and the left hand state of A is a subset of the states in B), A is also
   * true. For this method, each B *(*it) is a known sequent and (lhs, lhsPlace)
   * is the clock state of A. This method assumes that the right hand side and
   * discrete states match (and is often called after locate_sequentPlace() or
   * look_for_sequentPlace()); hence,
   * it only needs to compare clock states.
   * @param s (*) The placeholder sequent that
   * contains a set of (DBM, DBMList) pairs.
   * @param lhs (*) The DBM of the clock state to compare the sequent's DBMs to.
   * @param lhsPlace (*) The placeholder DBMList of the clock state.
   * @return true: (lhs, lhsPlace) <= some sequent in s
   * (consequently, the sequent is true), false: otherwise.*/
  bool tabled_sequent(const DBM& lhs, DBMList* const lhsPlace) const {
    auto p = [&](const std::pair<const DBM *, DBMList *> x) {
      if (*(x.first) == lhs) {
        lhsPlace->intersect(*(x.second));
        lhsPlace->cf();
        return true;
      }
      return false;
    };

    return std::find_if(m_dbms.begin(), m_dbms.end(), p) != m_dbms.end();
  }

  /** Using that a Sequent object is a set of sequents with matching rhs and
   *  discrete states with different clock states, determines if the specified
   * clock state contains one of the sequents.
   * This is used for known false sequents, since by definition
   * of sequents, if sequent B is false and B <= A (the right hand side matches
   * and the left hand state of B is a subset of the states in A), A is false.
   * For this method, each B *(*it) is a known sequent
   * and (lhs, lhsPlace) is the clock state
   * of A. This method assumes that the right hand side and discrete states
   * match (and is often called after locate_sequentPlace() or
   * look_for_sequentPlace()); hence,
   * it only needs to compare clock states.
   * @param s (*) The placeholder sequent that
   * contains a set of (DBM, DBMList) pairs.
   * @param lhs (*) The DBM of the clock state to compare the sequent's DBMs to.
   * @param lhsPlace (*) The placeholder DBMList of the clock state.
   * @return true: (lhs, lhsPlace) >= some sequent in s
   * (consequently, the sequent is false), false: otherwise.*/
  bool tabled_false_sequent(const DBM& lhs) {
    return std::find_if(m_dbms.begin(), m_dbms.end(),
                        [&](const std::pair<const DBM *, const DBMList *> x) {
                          return *(x.first) <= lhs;
                        }) != m_dbms.end();
  }

  /** Using that a Sequent object is a set of sequents with matching rhs and
   *  discrete states with different clock states, determines if the specified
   * DBM equals one of the sequents. This is used for least fixpoint
   * sequents and checks for sequent equality. For least fixpoint circularity,
   * if an equal sequent is found then this sequent is false.
   * This method assumes that the right hand side and discrete states match
   * (and is often called after locate_sequentPlace() or
   * look_for_sequentPlace()); hence,
   * it only needs to compare clock states.
   * @param s (*) The placeholder sequent that
   * contains a set of (DBM, DBMList) pairs.
   * @param lhs (*) The DBM of the clock state to compare the sequent's DBMs to.
   * @param lhsPlace (*) The placeholder DBMList of the clock state.
   * @return true: (lhs, lhsPlace) == some sequent in s, false: otherwise.*/
  bool tabled_sequent_lfp(const DBM& lhs,
                                 const DBMList *const lhsPlace) {
    return std::find_if(m_dbms.begin(), m_dbms.end(),
                        [&](const std::pair<const DBM *, const DBMList *> x) {
                          return *(x.first) == lhs && *(x.second) == *lhsPlace;
                        }) != m_dbms.end();
  }

  /** Using that a Sequent object is a set of sequents with matching rhs and
   *  discrete states with different clock states, determines if the specified
   * clock state is contained within one of the sequents.
   * This is used for greatest
   * fixpoint circularity, since by definition
   * of sequents, if sequent B is true and A <= B (the right hand side matches
   * and the left hand state of A is a subset of the states in B), A is also
   * true. For this method, each B *(*it) is a known sequent and (lhs, lhsPlace)
   * is the clock state of A. This method assumes that the right hand side and
   * discrete states match (and is often called after locate_sequentPlace() or
   * look_for_sequentPlace()); hence,
   * it only needs to compare clock states.
   * @param s (*) The placeholder sequent that
   * contains a set of (DBM, DBMList) pairs.
   * @param lhs (*) The DBM of the clock state to compare the sequent's DBMs to.
   * @param lhsPlace (*) The placeholder DBMList of the clock state.
   * @return true: (lhs, lhsPlace) <= some sequent in s
   * (consequently, the sequent is true), false: otherwise.*/
  bool tabled_sequent_gfp(const DBM& lhs,
                          const DBMList *const lhsPlace) {
    return std::find_if(m_dbms.begin(), m_dbms.end(),
                        [&](const std::pair<const DBM *, const DBMList *> x) {
                          return *(x.first) == lhs && *(x.second) >= *lhsPlace;
                        }) != m_dbms.end();
  }

  /** Assumes the current sequent is known to be true, and updates it with a
   * newly established true clock state (lhs, lhsPlace) and adds clock state
   * (lhs, lhsPlace) to the set of sequents. In the update, the DBM lhs and the
   * DBMList lhsPlace are copied. By definition, a sequent B is true if and only
   * if all of its states satisfy the right hand side. Hence, if any known clock
   * state is contained in lhs (B <= lhs), we can enlarge that clock state
   * (enlarge B). This is more efficient (for searching) than just adding an
   * additional sequent.
   * @param lhs (*) The DBM of the newly-established clock state.
   * @param lhsPlace (*) The DBMList of the newly-established clock state. */
  void update_sequent(const DBM& lhs,
                      const DBMList& lhsPlace) {
    assert(lhsPlace.isInCf());
    for (std::pair<DBM *, DBMList *> pair: m_dbms) {
      /* Extra work for placeholders. For now,
       * force equality on LHS sequent and use tabling logic
       * for placeholders. */
      if (*pair.first == lhs && *pair.second <= lhsPlace) {
        *pair.second = lhsPlace;
        return;
      }
    }
    m_dbms.emplace_back(new DBM(lhs), new DBMList(lhsPlace));
  }

  /** Assumes the current sequent is known to be true, and updates it with a
   * newly established false clock state (lhs, lhsPlace) and adds clock state
   * (lhs, lhsPlace) to the set of sequents. In the update, the DBM lhs and the
   * DBMList lhsPlace are copied. By definition, a sequent B is false if and
   * only if it has a clocks state that does not satisfy the right side. Hence,
   * if any known clock state contains lhs (B >= lhs),
   * we can refine that clock
   * state (shrink B). This is more efficient (for searching) than just adding
   * an additional sequent.
   * @param lhs (*) The DBM of the newly-established clock state.
   * @param lhsPlace (*) The DBMList of the newly-established clock state.
   * @return true: the clock state was incorporated into one of s's
   * sequents; false: otherwise (a new sequent was added to s). */
  void update_false_sequent(const DBM& lhs) {
    for (std::pair<DBM *, DBMList *> pair: m_dbms) {
      if (*pair.first >= lhs) {
        *pair.first = lhs;
        return;
      }
    }
    /* I would like this to be nullptr, but it is checked in the program */

    /** This DBM is used as a DBM with
     * the proper number of clocks and initialized
     * so that it represents the empty region
     * (for all clocks x_i, 0 <= x_i <= 0). */
    DBM EMPTY(lhs.declared_clocks());
    EMPTY.makeEmpty();

    m_dbms.emplace_back(new DBM(lhs), new DBMList(EMPTY));
  }

  void print(std::ostream& os) const {
    os << "(" << *m_discrete_state << ", " << m_dbms << " |- " << *m_rhs;
  }

protected:


  /** The right hand side expression of the sequent. */
  const ExprNode *m_rhs;
  /** The discrete state of the left of a sequent, represented
   * as a SubstList. */
  const SubstList *m_discrete_state;
  /** A list of (DBM, DBMList) pairs stored in the sequent,
   * used to store a set of sequents
   * in a method for easy access during sequent caching. This vector
   * stores the clock state part of the left hand side of each sequent.
   * Each element in ds is combined with the location state (st)
   * and the right hand expression (e) to form a proof sequent
   * in the proof tree. */
  DBMPlaceSet m_dbms;

  /** The placeholder sequent parent to this sequent in the proof tree;
   * this is used  to quickly access backpointers. A sequent either has a parent
   * with a placeholder (parSequentPlace) or a parent without a
   * placeholder (parSequent). */
  std::vector<SequentPlace *> m_parent_sequents_placeholder;

  /** The sequent parent to this sequent in the proof tree; this is used
   * to quickly access backpointers. A sequent either has a parent
   * with a placeholder (parSequentPlace) or a parent without a
   * placeholder (parSequent). */
  std::vector<Sequent *> m_parent_sequents;
};

inline std::ostream& operator<<(std::ostream& os, const Sequent& s) {
  s.print(os);
  return os;
}

inline std::ostream& operator<<(std::ostream& os, const SequentPlace& s) {
  s.print(os);
  return os;
}

#endif // SEQUENT_HH
