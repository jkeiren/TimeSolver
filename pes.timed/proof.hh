/** \file proof.hh
 * Header file for proof
 * @author Jeroen Keiren
 * @version 1.21
 * @date June 21, 2016 */

#ifndef PROOF_HH
#define PROOF_HH

#include "DBM.hh"
#include "ExprNode.hh"
#include "comp_ph.hh"

class prover
{
protected:
  /** First we declare variables for the timed automaton that we are proving
   * things about.
   */
  const vector<ExprNode *>& invs;
  /** This is the list of transitions of the state machine
   * from the automata/PES description. */
  const vector<Transition *> * const transList;


  bool currParityGfp;
  bool prevParityGfp;
  bool useCaching;

  /** Variable for the predicate
   * index to represent a counter on the number
   * of predicates to allow for hashing of sequents
   * to bin by predicate label/index.
   * By the time it reaches the demo.cc file, predicateInd's
   * value is the number of predicate variables. */
  int predicateInd;

  /* The size of the Hash table of Sequents: nBits + 1 */
  int  nHash;

  /** True if debug mode is on, and
   * False if debug mode is off. Running the
   * program with -d sets it to true. */
  bool debug;

  long int numLocations;

  /** This parameter is the size of the maximum
   * constant (in the clock constraints).  There
   * is one constant for all of the clocks
   * This is modified by the program and the parser. */
  int MAXC;

  /** The maximum number of bits used in the hashing function
   * when storing discrete states. */
  int nbits;

  /** Public variable that stores the number of hashing bins.
   * used for ease of locating the proper bin for each sequent,
   * especially when multiple predicate variables exist. */
  int seqStSize;

  /** XList_pGFP (XList) is an array of stacks, where each stack
   * is an array of sequents that
   * keeps track of all possible GFP Sequents
   * used for circularity (valid proofs). */
  sequentStack Xlist_pGFP;
  /** XList_pLFP is an array of stacks of sequents that
   * keeps track of all possible LFP Sequents
   * used for circularity (invalid proofs). */
  sequentStack Xlist_pLFP;
  /** XList_true is an array of stacks of sequents that
   * keeps track of all previously proven true sequents. */
  sequentStack Xlist_true;
  /** XList_false is an array stacks of sequents that
   * keeps track of all previously proven false sequents. */
  sequentStack Xlist_false;
  /** XList_pGFP_ph (XList) is an array of stacks, where each stack
   * is an array of sequents that
   * keeps track of all possible GFP Sequents
   * used for circularity (valid proofs) when placeholders are involved. */
  sequentStackPlace Xlist_pGFP_ph;
  /** XList_pLFP_ph is an array of stacks of sequents that
   * keeps track of all possible LFP Sequents
   * used for circularity (invalid proofs)
   * when placeholders are involved. */
  sequentStackPlace Xlist_pLFP_ph;
  /** XList_true_ph is an array of stacks of sequents that
   * keeps track of all previously proven true sequents
   * where placeholders are involved. */
  sequentStackPlace Xlist_true_ph;
  /** XList_false_ph is an array of stacks of sequents that
   * keeps track of all previously proven false sequents
   * where placeholders are involved. Because a false sequent
   * means that no such placeholder is possible (the placeholder
   * is empty), this structure does not need the overhead of
   * placeholders. */
  sequentStackPlace Xlist_false_ph;

  /** This DBM is used as a DBM with
   * the proper number of clocks and initialized
   * so that it represents the empty region
   * (for all clocks x_i, 0 <= x_i <= 0). */
  DBM *EMPTY;

  /** This DBM is a copy of a DBM initially
   * that represents the unconstrained DBM in
   * canonical form. */
  DBM *INFTYDBM;

  /** DBMList used as the value of the returned placeholder.
   * this is initialized outside of do_proof_place() to prevent
   * multiple re-initializations of it. */
  DBMList * retPlaceDBM;

  /** Global variable that keeps track of the parent sequent
   * of the current sequent in the proof tree. Used for sequents
   * without placeholder parents, and used to help generate backpointers
   * in the proof tree. */
  Sequent * parentRef;
  /** Global variable that keeps track of the parent placeholder sequent
   * of the current sequent in the proof tree. Used for sequents
   * with placeholder parents, and used to help generate backpointers
   * in the proof tree. */
  SequentPlace * parentPlaceRef;

  /** A boolean used to tell if the located sequent was
   * newly-added to the cache. If it is true, then that sequent
   * has no left-hand clock states, and is empty; hence, it need
   * not be examined by table-sequent.*/
  bool newSequent;

public:
  prover(const vector<ExprNode *>& a_invs,
         const vector<Transition *> * const a_transList,
         bool a_currParityGfp, bool a_prevParityGfp, bool a_useCaching,
         int a_predicateInd, int a_nHash, bool debug, int MAXC,
         int nbits, int seqStSize, int aSize) :
  invs(a_invs),
  transList(a_transList),
  currParityGfp(a_currParityGfp),
  prevParityGfp(a_prevParityGfp),
  useCaching(a_useCaching),
  predicateInd(a_predicateInd),
  nHash(a_nHash),
  debug(debug),
  MAXC(MAXC),
  nbits(nbits),
  seqStSize(seqStSize),
  Xlist_pGFP(aSize, nbits, predicateInd*nHash, seqStSize, predicateInd, newSequent),
  Xlist_pLFP(aSize, nbits, predicateInd*nHash, seqStSize, predicateInd, newSequent),
  Xlist_true(aSize, nbits, predicateInd*nHash, seqStSize, predicateInd, newSequent),
  Xlist_false(aSize, nbits, predicateInd*nHash, seqStSize, predicateInd, newSequent),
  Xlist_pGFP_ph(aSize, nbits, predicateInd*nHash, seqStSize, predicateInd, newSequent),
  Xlist_pLFP_ph(aSize, nbits, predicateInd*nHash, seqStSize, predicateInd, newSequent),
  Xlist_true_ph(aSize, nbits, predicateInd*nHash, seqStSize, predicateInd, newSequent),
  Xlist_false_ph(aSize, nbits, predicateInd*nHash, seqStSize, predicateInd, newSequent)

  {
    /* Initialize DBMs. The initial constructor
     * indicates that the DBM is not in canonical form.
     * We also make it so reference DBMs are in
     * canonical form (low performance cost now,
     * ease of comparisons later). */

    EMPTY = new DBM(spaceDimension);
    for (int i=1; i<spaceDimension; i++){
      EMPTY->addConstraint(i,0, 0);
      EMPTY->addConstraint(0,i, 0);
    }
    EMPTY->cf();

    /* This is initialized to be the largest (loosest)
     * possible DBM
     * @see DBM Constructor (Default Constructor). */
    INFTYDBM = new DBM(spaceDimension);
    INFTYDBM->cf();

    retPlaceDBM = new DBMList(*INFTYDBM);

    /* Initialize parent sequents to NULL */
    parentRef = NULL;
    parentPlaceRef = NULL;

    newSequent = true;
  };

  ~prover()
  {
    delete EMPTY;
    delete INFTYDBM;
    delete retPlaceDBM;
  };

  /** The prover function to prove whether a sequent is true or false.
   * @param step The "tree level" of the sequent in the proof tree.
   * A lower number is closer to the root, and a higher level is close
   * to "leaf" sequents. The main() method
   * that calls this feeds in 0.
   * @param lhs (*) The initial DBM of clock constraints (Sequent Premise)
   * @param rhs (*) The Expression/Consequent (root of the Expression Tree)
   * that the prover
   * needs to determine if it is true or false.
   * @param sub (*) The current substitution list of variables and their
   * substituted values, used to represent the current
   * atomic "state" of the Sequent.
   * @return True if the expression evaluates to True given the other parameters
   * and False otherwise (if the expression evaluates to False).*/
  bool do_proof(int step, DBM * const lhs, const ExprNode * const rhs, SubstList * const sub);

  /** The prover function that handles placeholders.
   * @param step The "tree level" of the sequent in the proof tree.
   * A lower number is closer to the root, and a higher level is close
   * to "leaf" sequents. The main() method
   * that calls this feeds in 0.
   * @param lhs (*) The initial DBM of clock constraints (Sequent Premise)
   * @param place (*) The current zone union of the Placeholder DBM.
   * @param rhs (*) The Expression/Consequent (root of the Expression Tree)
   * that the prover
   * needs to determine if it is true or false.
   * @param sub (*) The current substitution list of variables and their
   * substituted values, used to represent the current
   * atomic "state" of the Sequent.
   * @return The DBM Value of the placeholder constraint or an empty DBM if
   * no valid value for the placeholder exists (thus proof is Invalid). */
  DBMList * do_proof_place(int step, DBM * const lhs, DBMList * const place,
                                   const ExprNode * const rhs, SubstList * const sub);

  void printTabledSequents() const
  {
    /* If in DEBUG Mode, print out list of Tabled Sequents */
    cout << endl;
    cout << "##--Debug Info: Tabled Sequents===============" << endl;
    cout << "----GFP Cached Sequents---------" << endl;
    Xlist_pGFP.print_Xlist();
    // cout << "Number of GFP Sequents Tabled: " endl;
    cout << endl;
    cout << "----LFP Cached Sequents---------" << endl;
    Xlist_pLFP.print_Xlist();
    cout << endl;
    cout << "----Known False Cached Sequents---------" << endl;
    Xlist_false.print_Xlist();
    cout << endl;
    cout << "----Known True Cached Sequents---------" << endl;
    Xlist_true.print_Xlist();
    cout << endl;
    cout << "##--Debug Info: Tabled Placeholder Sequents==========" << endl;
    cout << "----GFP Placeholder Cached Sequents---------" << endl;
    Xlist_pGFP_ph.print_Xlist();
    // cout << "Number of GFP Sequents Tabled: " endl;
    cout << endl;
    cout << "----LFP Placeholder Cached Sequents---------" << endl;
    Xlist_pLFP_ph.print_Xlist();
    cout << endl;
    cout << "----Known False (Placeholder) Cached Sequents---------" << endl;
    Xlist_false_ph.print_Xlist();
    cout << endl;
    cout << "----Known True (Placeholder) Cached Sequents---------" << endl;
    Xlist_true_ph.print_Xlist();
  }

protected:
  /** Using that a Sequent object is a set of sequents with matching rhs and
   *  discrete states with different clock states, determines if the specified
   * DBM is contained within one of the sequents. This is used for greatest
   * fixpoint circularity (or known true sequents), since by definition
   * of sequents, if sequent B is true and A <= B (the right hand side matches
   * and the left hand state of A is a subset of the states in B), A is also true.
   * For this method, each B *(*it) is a known sequent and lhs is the clock state
   * of A. This method assumes that the right hand side and discrete states match
   * (and is often called after locate_sequent() or look_for_sequent()); hence,
   * it only needs to compare clock states.
   * @param s (*) The sequent that contains a set of DBMs.
   * @param lhs (*) The DBM to compare the sequent's DBMs to.
   * @return true: lhs <= some sequent in s
   * (consequently, the sequent is true), false: otherwise.*/
  bool tabled_sequent(const Sequent * const s, const DBM * const lhs){
    for(DBMset::const_iterator it = s->ds.begin(); it != s->ds.end(); it++) {
      if (*(*it) >= *lhs) {
        return true;
      }
    }
    return false;

  }

  /** Using that a Sequent object is a set of sequents with matching rhs and
   *  discrete states with different clock states, determines if the specified
   * clock state is contained within one of the sequents. For performance
   * reasons, if the sequent is found in here, its placeholder is restricted
   * to be the largest placeholder possible.
   * This is used for known true sequents, since by definition
   * of sequents, if sequent B is true and A <= B (the right hand side matches
   * and the left hand state of A is a subset of the states in B), A is also true.
   * For this method, each B *(*it) is a known sequent
   * and (lhs, lhsPlace) is the clock state
   * of A. This method assumes that the right hand side and discrete states match
   * (and is often called after locate_sequentPlace() or
   * look_for_sequentPlace()); hence,
   * it only needs to compare clock states.
   * @param s (*) The placeholder sequent that
   * contains a set of (DBM, DBMList) pairs.
   * @param lhs (*) The DBM of the clock state to compare the sequent's DBMs to.
   * @param lhsPlace (*) The placeholder DBMList of the clock state.
   * @return true: (lhs, lhsPlace) <= some sequent in s
   * (consequently, the sequent is true), false: otherwise.*/
  bool tabled_sequentPlace(const SequentPlace * const s, const DBM * const lhs,
                           DBMList * const lhsPlace){
    for(DBMPlaceSet::const_iterator it = s->dsp.begin(); it != s->dsp.end(); it++) {
      if (*((*it).first) == *lhs) {
        // Since in the cache, we have the largest placeholder where this is true
        *lhsPlace & *((*it).second);
        lhsPlace->cf();
        return true;
      }
    }
    return false;
  }

  /** Using that a Sequent object is a set of sequents with matching rhs and
   *  discrete states with different clock states, determines if the specified
   * DBM is contains one of the sequents. This is used for known false
   * sequents, since by definition
   * of sequents, if sequent B is false and B <= A (the right hand side matches
   * and the left hand state of B is a subset of the states in A), A is false.
   * For this method, each B *(*it) is a known sequent and lhs is the clock state
   * of A. This method assumes that the right hand side and discrete states match
   * (and is often called after locate_sequent() or look_for_sequent()); hence,
   * it only needs to compare clock states.
   * @param s (*) The sequent that contains a set of DBMs.
   * @param lhs (*) The DBM to compare the sequent's DBMs to.
   * @return true: lhs >= some sequent in s
   * (consequently, the sequent is false), false: otherwise.*/
  bool tabled_false_sequent(const Sequent * const s, const DBM * const lhs){
    for(DBMset::const_iterator it = s->ds.begin(); it != s->ds.end(); it++) {
      if (*(*it) <= *lhs) {
        return true;
      }
    }
    return false;
  }

  /** Using that a Sequent object is a set of sequents with matching rhs and
   *  discrete states with different clock states, determines if the specified
   * clock state contains one of the sequents.
   * This is used for known false sequents, since by definition
   * of sequents, if sequent B is false and B <= A (the right hand side matches
   * and the left hand state of B is a subset of the states in A), A is false.
   * For this method, each B *(*it) is a known sequent
   * and (lhs, lhsPlace) is the clock state
   * of A. This method assumes that the right hand side and discrete states match
   * (and is often called after locate_sequentPlace() or
   * look_for_sequentPlace()); hence,
   * it only needs to compare clock states.
   * @param s (*) The placeholder sequent that
   * contains a set of (DBM, DBMList) pairs.
   * @param lhs (*) The DBM of the clock state to compare the sequent's DBMs to.
   * @param lhsPlace (*) The placeholder DBMList of the clock state.
   * @return true: (lhs, lhsPlace) >= some sequent in s
   * (consequently, the sequent is false), false: otherwise.*/
  bool tabled_false_sequentPlace(const SequentPlace * const s, const DBM * const lhs,
                                 const DBMList * const lhsPlace){
    for(DBMPlaceSet::const_iterator it = s->dsp.begin(); it != s->dsp.end(); it++) {
      // if (*((*it).first) == *lhs && *((*it).second) <= *lhsPlace) {
      if (*((*it).first) <= *lhs) {
        return true;
      }
    }
    return false;
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
   * @return true: lhs == some sequent in s, false: otherwise.*/
  bool tabled_sequent_lfp(const Sequent * const s, const DBM * const lhs){
    for(DBMset::const_iterator it = s->ds.begin(); it != s->ds.end(); it++) {
      if (*(*it) == *lhs) {
        return true;
      }
    }
    return false;
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
  bool tabled_sequent_lfpPlace(const SequentPlace * const s, const DBM * const lhs,
                               const DBMList * const lhsPlace){
    for(DBMPlaceSet::const_iterator it = s->dsp.begin(); it != s->dsp.end(); it++) {
      /* Extra work for placeholders. For now,
       * force equality on LHS sequent and use tabling logic
       * for placeholders. */
      if ( *(it->first) == *lhs && *(it->second) == *lhsPlace) {
        return true;
      }
    }
    return false;
  }

  /** Using that a Sequent object is a set of sequents with matching rhs and
   *  discrete states with different clock states, determines if the specified
   * clock state is contained within one of the sequents.
   * This is used for greatest
   * fixpoint circularity, since by definition
   * of sequents, if sequent B is true and A <= B (the right hand side matches
   * and the left hand state of A is a subset of the states in B), A is also true.
   * For this method, each B *(*it) is a known sequent
   * and (lhs, lhsPlace) is the clock state
   * of A. This method assumes that the right hand side and discrete states match
   * (and is often called after locate_sequentPlace() or
   * look_for_sequentPlace()); hence,
   * it only needs to compare clock states.
   * @param s (*) The placeholder sequent that
   * contains a set of (DBM, DBMList) pairs.
   * @param lhs (*) The DBM of the clock state to compare the sequent's DBMs to.
   * @param lhsPlace (*) The placeholder DBMList of the clock state.
   * @return true: (lhs, lhsPlace) <= some sequent in s
   * (consequently, the sequent is true), false: otherwise.*/
  bool tabled_sequent_gfpPlace(const SequentPlace * const s, const DBM * const lhs,
                               const DBMList * const lhsPlace){
    for(DBMPlaceSet::const_iterator it = s->dsp.begin(); it != s->dsp.end(); it++) {
      /* Extra work for placeholders. For now,
       * force equality on LHS sequent and use tabling logic
       * for placeholders. */
      if (*((*it).first) == *lhs && *((*it).second) >= *lhsPlace) {
        return true;
      }
    }
    return false;
  }

  /** Takes in set of known true sequents (s) with a newly
   * established true clock state (lhs) and adds clock state (lhs)
   * to the set of sequents in s. In the update, the
   * DBM lhs is copied. By definition, a sequent B is true
   * if and only if all of its states satisfy the right hand side. Hence,
   * if any known clock state is contained in lhs (B <= lhs),
   * we can enlarge that clock
   * state (enlarge B). This is more efficient (for searching) than just adding an
   * additional sequent.
   * @param s (*) The set of known sequents to update.
   * @param lhs (*) The DBM of the newly-established clock state.
   * @return true: the clock state was incorporated into one of s's
   * sequents; false: otherwise (a new sequent was added to s). */
  bool update_sequent(Sequent * const s, const DBM * const lhs){
    for(DBMset::const_iterator it = s->ds.begin(); it != s->ds.end(); it++) {
      if (*(*it) <= *lhs) {
        *(*it) = *lhs;
        return true;
      }
    }
    DBM *m = new DBM(*lhs);
    s->ds.push_back(m);
    return false;
  }

  /** Takes in set of known true sequents (s) with a newly
   * established true clock state (lhs, lhsPlace) and adds
   * clock state (lhs, lhsPlace)
   * to the set of sequents in s. In the update, the
   * DBM lhs and the DBMList lhsPlace are copied.
   * By definition, a sequent B is true
   * if and only if all of its states satisfy the right hand side. Hence,
   * if any known clock state is contained in lhs (B <= lhs),
   * we can enlarge that clock
   * state (enlarge B). This is more efficient (for searching) than just adding an
   * additional sequent.
   * @param s (*) The set of known placeholder sequents to update.
   * @param lhs (*) The DBM of the newly-established clock state.
   * @param lhsPlace (*) The DBMList of the newly-established clock state.
   * @return true: the clock state was incorporated into one of s's
   * sequents; false: otherwise (a new sequent was added to s). */
  bool update_sequentPlace(SequentPlace * const s, const DBM * const lhs,
                           const DBMList * const lhsPlace){
    for(DBMPlaceSet::iterator it = s->dsp.begin(); it != s->dsp.end(); it++) {
      /* Extra work for placeholders. For now,
       * force equality on LHS sequent and use tabling logic
       * for placeholders. */
      if (*((*it).first) == *lhs && *((*it).second) <= *lhsPlace) {
        *((*it).second) = *lhsPlace;
        return true;
      }
    }
    DBM *m = new DBM(*lhs);
    DBMList *mp = new DBMList(*lhsPlace);
    pair <DBM *, DBMList *> p (m, mp);
    s->dsp.push_back(p);
    return false;
  }

  /** Takes in set of known false sequents (s) with a newly
   * established false clock state (lhs) and adds clock state (lhs)
   * to the set of sequents in s. In the update, the
   * DBM lhs is copied. By definition, a sequent B is false
   * if and only if it has a clocks state that does not satisfy the right
   * side. Hence,
   * if any known clock state is contains (B >= lhs),
   * we can refine that clock
   * state (shrink B). This is more efficient (for searching) than just adding an
   * additional sequent.
   * @param s (*) The set of known sequents to update.
   * @param lhs (*) The DBM of the newly-established clock state.
   * @return true: the clock state was incorporated into one of s's
   * sequents; false: otherwise (a new sequent was added to s). */
  bool update_false_sequent(Sequent * const s, const DBM * const lhs){
    for(DBMset::iterator it = s->ds.begin(); it != s->ds.end(); it++) {
      if (*(*it) >= *lhs) {
        *(*it) = *lhs;
        return true;
      }
    }
    DBM *m = new DBM(*lhs);
    s->ds.push_back(m);
    return false;
  }

  /** Takes in set of known false sequents (s) with a newly
   * established false clock state (lhs, lhsPlace) and adds
   * clock state (lhs, lhsPlace)
   * to the set of sequents in s. In the update, the
   * DBM lhs and the DBMList lhsPlace are copied.
   * By definition, a sequent B is false
   * if and only if it has a clocks state that does not satisfy the right
   * side. Hence,
   * if any known clock state is contains (B >= lhs),
   * we can refine that clock
   * state (shrink B). This is more efficient (for searching) than just adding an
   * additional sequent.
   * @param s (*) The set of known placeholder sequents to update.
   * @param lhs (*) The DBM of the newly-established clock state.
   * @param lhsPlace (*) The DBMList of the newly-established clock state.
   * @return true: the clock state was incorporated into one of s's
   * sequents; false: otherwise (a new sequent was added to s). */
  bool update_false_sequentPlace(SequentPlace * const s, const DBM * const lhs,
                                 const DBMList * const lhsPlace){
    for(DBMPlaceSet::iterator it = s->dsp.begin(); it != s->dsp.end(); it++) {
      if (*((*it).first) >= *lhs) {
        *((*it).first) = *lhs;
        return true;
      }
    }
    DBM *m = new DBM(*lhs);
    /* I would like this to be NULL, but it is checked in the program */
    DBMList *mp = new DBMList(*EMPTY);
    pair <DBM *, DBMList *> p (m,mp);
    s->dsp.push_back(p);
    return false;
  }


  /** Purge backpointers from all caches. Purging occurrs
   * until no sequent was purged (not purging a sequent indicates that
   * no further sequents needs to be purged). For performance For
   * performance efficiency, this method passes pointers to vectors.
   * Furthermore, for performance reasons, backpointers do not examine
   * clock states and conservatively purge. This method handles
   * both placeholder and non-placeholder sequents. Feed in an empty
   * list for one of the parameters if only one type of sequent
   * needs to be purged. We utilize one method so that non-placeholder
   * sequents that are parents of placeholder sequents can be purged.
   * @param initialPtr (*) The vector of initial
   * non-placeholder sequents to purge.
   * @param initialPlacePtr (*) The vector of initial
   * placeholder sequents to purge.
   * @return true: something was purged; false: otherwise (nothing was
   * purged).*/
  bool look_for_and_purge_rhs_backStack(const vector<Sequent *> * const initialPtr,
                                        const vector<SequentPlace *> * const initialPlacePtr)
  {
    bool madeChange = false;

    /* Store a vector of stateBackList, where each sequent only has one DBM */

    /* Now iterate until the vector sequentQueue is empty,
     * purging backpointers and adding relevant ones in the queue */
    /* For now, implement purging with deques instead of vectors */
    deque <Sequent *> purgeSeqQueue(initialPtr->begin(), initialPtr->end());
    deque <SequentPlace *> purgeSeqPlaceQueue(initialPlacePtr->begin(), initialPlacePtr->end());

    while(!(purgeSeqPlaceQueue.empty())) {


      SequentPlace * tp = purgeSeqPlaceQueue.front();
      int pInd;
      bool b2 = false;
      bool b2b = false;

      pInd = (lookup_predicate(tp->rhs()->getPredicate()))->getIntVal() - 1;
      /* Note: Purging parent sequents still ignores clock states. */

      /* Now purge the sequent and the DBM from all lists.
       * Circularity caches are correctly maintained; therefore,
       * they are not purged. */

      /* If found, Purge Sequent from its cache */
      b2 = Xlist_false_ph.look_for_and_purge_rhs_sequentPlace_state(tp, pInd, false);

      b2b = Xlist_true_ph.look_for_and_purge_rhs_sequentPlace_state(tp, pInd, false);

      /* Now find its backpointers to add to the queue
       * Only add backpointers to queue if something is purged. */
      if( b2 || b2b) {
        madeChange = true;
        // Now add sequents
        for(vector<Sequent *>::iterator it = tp->parSequent.begin();
            it != tp->parSequent.end(); it++) {
          purgeSeqQueue.push_back(*it);

        }
        for(vector<SequentPlace *>::iterator it = tp->parSequentPlace.begin();
            it != tp->parSequentPlace.end(); it++) {
          purgeSeqPlaceQueue.push_back(*it);

        }
      }

      purgeSeqPlaceQueue.pop_front();


    }

    /* Now purge the original Sequents */
    while(!(purgeSeqQueue.empty())) {

      Sequent * t = purgeSeqQueue.front();
      int pInd;
      bool b1 = false;
      bool b1b = false;

      pInd = (lookup_predicate(t->rhs()->getPredicate()))->getIntVal() - 1;
      /* Note: Purging parent sequents still ignores clock states */

      /* Now purge the sequent and the DBM from all lists.
       * Circularity caches are correctly maintained; therefore,
       * they are not purged. */
      b1 = Xlist_false.look_for_and_purge_rhs_sequent_state(t, pInd, false);

      /* If found, Purge Sequent from its cache */
      b1b = Xlist_true.look_for_and_purge_rhs_sequent_state(t, pInd, false);

      /* Now find its backpointers to add to the queue
       * Only add backpointers to queue if something is purged. */
      if(b1 || b1b) {
        madeChange = true;
        // Now add sequents
        for(vector<Sequent *>::iterator it = t->parSequent.begin();
            it != t->parSequent.end(); it++) {
          purgeSeqQueue.push_back(*it);

        }
        for(vector<SequentPlace *>::iterator it = t->parSequentPlace.begin();
            it != t->parSequentPlace.end(); it++) {
          purgeSeqPlaceQueue.push_back(*it);

        }
      }

      purgeSeqQueue.pop_front();

    }
    // For now, do not remove backpointers from backList
    // This may be too conservative.

    return madeChange;

  }

  /** Method to compute the predecessor check of relativized exists operators.
   * This method is inlined for performance reasons.
   * @param lhs (*) the left-hand clock set
   * @param lhsSucc (*) the sucessor of the left-hand clock constraint, after
   * applying invariants.
   * @param origPlace (*) a reference to the DBMList placeholder or NULL if
   * there is no placeholder.
   * @param phi1Place (*) the set of clock valuations that satisfy phi1, the
   * left hand formula (the relativized formula).
   * @param phi2Place (*) the set of clock valuations that satisfy phi2, the
   * right hand formula.
   * @param phi2PredPlace (*) the time predecessor of phi2Place; this predecessor
   * may by <= or <, depending on the proof rule that calls this method.
   * @return the output placeholder, which is also retPlaceDBM. */
  inline DBMList * predCheckRule(const DBM * const lhs, const DBM * const lhsSucc,
                                 const DBMList * const origPlace, const DBMList * const phi1Place,
                                 const DBMList * const phi2Place, const DBMList * const phi2PredPlace ) {

    retPlaceDBM->makeEmpty();
    /* Iterate through each DBM of phi2Place and union the results. */
    vector<DBM *> * phi2PlaceList = phi2Place->getDBMList();
    DBMList compPhi1(*phi1Place);
    !compPhi1;
    compPhi1.cf();
    bool previouslyUpdated = false;
    for(unsigned int i = 0; i < phi2PlaceList->size(); i++) {
      DBM * currPhi2 = (*phi2PlaceList)[i];
      DBM predPhi2(*currPhi2);
      predPhi2.pre();
      predPhi2.cf();

      DBMList currDBMList(compPhi1);
      currDBMList & predPhi2;
      currDBMList & *lhsSucc;  // Intersect with the successor of the lhs


      DBMList compPhi2(*currPhi2);
      !compPhi2;
      compPhi2.cf();

      currDBMList & compPhi2;
      currDBMList.cf();
      currDBMList.pre();
      currDBMList & *lhsSucc;
      currDBMList.cf();
      // currDBMList currently is the set of bad times; LHS must have
      // no such times in this.
      if(currDBMList.emptiness()) { // no bad times, so no shrinkage
        *retPlaceDBM = *phi1Place;
        break;
      }
      /* If this is nonempty, then we have something to deal with */
      // Also, the placeholder cannot be completely contained in this
      if(origPlace == NULL) {
        currDBMList & *lhs;
        currDBMList.cf();
        if(!(currDBMList.emptiness())) {
          if(previouslyUpdated == false) {
            previouslyUpdated = true;
            *retPlaceDBM = currDBMList;
          }
          else{
            retPlaceDBM->addDBMList(currDBMList);
          }
        }
        else {
          if(previouslyUpdated == false) {
            previouslyUpdated = true;
            retPlaceDBM->makeEmpty();
          }
        }
      }
      else { /* This is the section if we have a placeholder */
        currDBMList & *origPlace;
        currDBMList.cf();
        if(currDBMList.emptiness()) {
          if(previouslyUpdated == false) {
            previouslyUpdated = true;
            retPlaceDBM->makeEmpty();
          }
        }
        else if (currDBMList >= *lhs) {
          if(previouslyUpdated == false) {
            previouslyUpdated = true;
            *retPlaceDBM = currDBMList;
          }
          else{
            retPlaceDBM->addDBMList(currDBMList);
          }
        }
        else { // this is the same as the emptiness case
          if(previouslyUpdated == false) {
            previouslyUpdated = true;
            retPlaceDBM->makeEmpty();
          }
        }
      }


    }

    /* We also need to make another placeholder check: that the phi1Place,
     * which is now retPlaceDBM, is a placeholder that can be formed
     * by taking the predecessor
     * and intersecting it with succ(\Gamma). We need phi1Place to be
     * the entire predecessor, and not just the upper part of it. */
    if(!(*retPlaceDBM >= *lhs)) {
      // simple empty case
      retPlaceDBM->makeEmpty();
    }
    else {
      // here, we just need to check for gaps in the DBM and eliminate them.
      // does this case come up due to how pred check works?
    }


    return retPlaceDBM;
  }

  /** Performs the succCheck rule of FORALL (and FORALL_REL) rules, including
   * the computing of the premise, the consequent, and the tightening of the
   * placeholder currPlace.
   * @param lhs (*) the reference to the left hand sequent
   * @param currPlace (*) the reference to the current placeholder.
   * @return the tightened placeholder that satisfies the succCheck, or an
   * empty placeholder if no such placeholder is possible. */
  inline DBMList * succCheckRule(const DBM * const lhs, const DBMList * const currPlace) {

    DBM succLHS(*lhs);
    succLHS.suc();
    // intersect with new placeholder
    DBMList conseq(*retPlaceDBM);
    conseq & succLHS;

    /* Computing Premise of Right part of proof */
    /* Compute Succ(Premise and First Placeholder) */
    // succLHS is the successor of the left-hand side, so do not repeat the work
    DBMList succPrem(*lhs);
    succPrem & *retPlaceDBM;
    succPrem.cf();
    succPrem.suc();

    // First start by setting the place holder to the value of the new placeholder
    /* Per our algorithm, initialize place as retPlaceDBM. */
    // Do we need to intersect succLHS with retPlaceDBM somewhere?
    conseq.cf(); // The consequent
    succLHS.cf(); // The succprem
    succPrem.cf();

    if(conseq >= succPrem) {
      *retPlaceDBM = *currPlace;
      return retPlaceDBM;
    }

    /* If we are here, then we have one of two cases:
     * 1. The succCheck fails (since it is not possible)
     * 2. THe placeholder needs to be tightened so it can pass.
     * Invariants make this tricky */
    // Find the bad zones;
    DBMList badVals(*currPlace);
    !badVals;
    badVals.cf();
    badVals & succPrem;
    badVals & succLHS;
    badVals.cf();
    badVals.pre();
    badVals.cf();
    // At this point, we have the bad valuations. Now intersect their 
    // complement
    !badVals;
    badVals.cf();
    // Good values must be after succLHS
    badVals & succLHS;
    badVals.cf();
    *retPlaceDBM & badVals;
    retPlaceDBM->cf();
    if(retPlaceDBM->emptiness()) {
      return retPlaceDBM;
    }
    // Do one more containmnet check. If this does not work, 
    // then the placeholder is empty
    succLHS = *lhs;
    succLHS.suc();
    
    // leave conseq unchanged, since that placeholder did not shrink
    succPrem = *lhs;
    succPrem & *retPlaceDBM;
    succPrem.cf();
    succPrem.suc();
    
    succLHS.cf(); 
    succPrem.cf();
    // use previously solved place, not new one for right hand side
    if(conseq >= succPrem) {
      return retPlaceDBM;
    } 
    retPlaceDBM->makeEmpty();
    return retPlaceDBM;
  }

};

#endif /* PROOF_HH */
