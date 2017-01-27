#ifndef SEQUENT_HH
#define SEQUENT_HH

#include "ExprNode.hh"

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
 * @author Peter Fontana, Dezhuang Zhang, and Rance Cleaveland.
 * @note Many functions are inlined for better performance.
 * @version 1.2
 * @date November 2, 2013 */
class SequentPlace; // forward declaration for parent scope

/** The internal representation of a proof sequent with
 * a clock zone for the clock state. A sequent is a
 * DBM, [SubstList] |- RHS. For storage efficiency, the Sequent class
 * is set of sequents a DBM' [SubstList] |- RHS, with ds
 * the vector representing the list of DBMs DBM'. This storage is used
 * to store multiple sequents, not a sequent consisting of a union of DBMs.
 * The SubstList represents the discrete location state (as variables).This
 * method of storing sequents improves the efficiency of sequent caching.
 *
 * This Sequent Class representation is closely utilized in
 * locate_sequent(), update_sequent() and tabled_sequent()
 * in the demo.cc implementation.
 *
 * @author Peter Fontana, Dezhuang Zhang, and Rance Cleaveland.
 * @note Many functions are inlined for better performance.
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
  Sequent(const ExprNode * const rhs, const SubstList * const sub)
  : e(rhs),
    st(new SubstList(*sub)){
  };


  /* A default Copy Constructor is implemented by the
   * compiler which performs a member-wise deep copy. */

  /** Destructor. It does not delete the right hand expression e
   * because e may be used in multiple sequents. The expression tree
   * storing e will delete it when the proof finishes. Likewise,
   * since each parent sequent (with or without a placeholder) can
   * delete itself, the destructor does not delete parent sequents.
   * @return [Destructor] */
  ~Sequent(){
    delete st;
    // Iterate Through and Delete every element of ds
    for(std::vector<DBM *>::iterator it = ds.begin();
        it != ds.end(); it++) {
      DBM *ls = (*it);
      delete ls;
    }
    ds.clear();
    // Do not delete e since it is a pointer to the overall ExprNode.
    // Do not delete parent sequent upon deletion
    // Do not delete parent placeholder sequent
    // Clearing vectors is enough
    parSequent.clear();
    parSequentPlace.clear();
  };


  /** Returns the ExprNode element (rhs or consequent) of the Sequent.
   * @return the rhs expression of the ExprNode element of the Sequent. */
  const ExprNode * rhs() const {return e ; };

  /** Returns the discrete state of the sequent's left (the SubstList).
   * @return the discrete state of the sequent's left (the SubstList). */
  const SubstList * sub() const {return st ; };



  /** A list of DBMs stored in the sequent, used to store a set of sequents
   * in a method for easy access during sequent caching. This vector
   * stores the clock state part of the left hand side of each sequent.
   * Each element in ds is combined with the location state (st)
   * and the right hand expression (e) to form a proof sequent
   * in the proof tree. */
  std::vector<DBM*> ds;

  /** The placeholder sequent parent to this sequent in the proof tree;
   * this is used  to quickly access backpointers. A sequent either has a parent
   * with a placeholder (parSequentPlace) or a parent without a
   * placeholder (parSequent). */
  std::vector<SequentPlace *> parSequentPlace;
  /** The sequent parent to this sequent in the proof tree; this is used
   * to quickly access backpointers. A sequent either has a parent
   * with a placeholder (parSequentPlace) or a parent without a
   * placeholder (parSequent). */
  std::vector<Sequent *> parSequent;


protected:

  /** The right hand side expression of the sequent. */
  const ExprNode *e;
  /** The discrete state of the left of a sequent, represented
   * as a SubstList. */
  const SubstList *st;
};


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
  SequentPlace(const ExprNode * const rhs, const SubstList * const sub)
  : e(rhs),
    st(new SubstList(*sub)) {
  };


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
  ~SequentPlace(){
    delete st;
    // Iterate Through and Delete every element of ds
    for(std::vector<std::pair<DBM*, DBMList *> >::iterator it = ds.begin();
        it != ds.end(); it++) {
      DBM *ls = (*it).first;
      DBMList * lsList = (*it).second;
      delete ls;
      delete lsList;
    }
    ds.clear();
    // Do not delete e since it is a pointer to the overall ExprNode.

    // Do not delete parent sequent parSequentPlace
    // Do not delete parent sequent parSequent
    // Clearing vectors is enough
    parSequent.clear();
    parSequentPlace.clear();
  };


  /** Returns the ExprNode element (rhs or consequent) of the Sequent.
   * @return the rhs expression of the ExprNode element of the Sequent. */
  const ExprNode * rhs() const {return e ; };

  /** Returns the discrete state of the sequent's left (the SubstList).
   * @return the discrete state of the sequent's left (the SubstList). */
  const SubstList * sub() const {return st ; };



  /** A list of (DBM, DBMList) pairs stored in the sequent,
   * used to store a set of sequents
   * in a method for easy access during sequent caching. This vector
   * stores the clock state part of the left hand side of each sequent.
   * Each element in ds is combined with the location state (st)
   * and the right hand expression (e) to form a proof sequent
   * in the proof tree. */
  std::vector<std::pair<DBM*, DBMList* > > ds;

  /** The placeholder sequent parent to this sequent in the proof tree;
   * this is used  to quickly access backpointers. A sequent either has a parent
   * with a placeholder (parSequentPlace) or a parent without a
   * placeholder (parSequent). */
  std::vector<SequentPlace *> parSequentPlace;
  /** The sequent parent to this sequent in the proof tree; this is used
   * to quickly access backpointers. A sequent either has a parent
   * with a placeholder (parSequentPlace) or a parent without a
   * placeholder (parSequent). */
  std::vector<Sequent *> parSequent;


protected:

  /** The right hand side expression of the sequent. */
  const ExprNode *e;
  /** The discrete state of the left of a sequent, represented
   * as a SubstList. */
  const SubstList *st;
};

#endif // SEQUENT_HH
