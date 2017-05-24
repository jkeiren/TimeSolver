/** \file proof.hh
 * Header file for proof
 * @author Jeroen Keiren
 * @version 1.21
 * @date June 21, 2016 */

#ifndef PROOF_HH
#define PROOF_HH

#include "cpplogging/logger.h"
#include "pes.hh"
#include "DBM.hh"
#include "ExprNode.hh"
#include "transition.hh"
#include "comp_ph.hh"
#include "sequent_cache.hh"

class prover {
protected:
  const pes& input_pes;

  bool currParityGfp;
  bool prevParityGfp;
  bool useCaching;

  /** The current step in the proof; initially 0 */
  size_t step;

  size_t numLocations;

  /** This DBM is a copy of a DBM initially
   * that represents the unconstrained DBM in
   * canonical form. */
  DBM* INFTYDBM;

  /** Global variable that keeps track of the parent sequent
   * of the current sequent in the proof tree. Used for sequents
   * without placeholder parents, and used to help generate backpointers
   * in the proof tree. */
  Sequent* parentRef;

  /** Global variable that keeps track of the parent placeholder sequent
   * of the current sequent in the proof tree. Used for sequents
   * with placeholder parents, and used to help generate backpointers
   * in the proof tree. */
  SequentPlace* parentPlaceRef;

  /** A boolean used to tell if the located sequent was
   * newly-added to the cache. If it is true, then that sequent
   * has no left-hand clock states, and is empty; hence, it need
   * not be examined by table-sequent.*/
  bool newSequent;

  /** Cache for storing sequents. This incorporates true and false sequents, as
   * well as sequents for predicate variables in order to detect cycles.
   */
  sequent_cache cache;

public:
  prover(const pes& input_pes, bool useCaching, int nHash, int nbits)
      : input_pes(input_pes),
        currParityGfp(false),
        prevParityGfp(false),
        useCaching(useCaching),
        step(0),
        numLocations(1),
        parentRef(nullptr),
        parentPlaceRef(nullptr),
        newSequent(true),
        cache(input_pes, nbits, input_pes.predicates().size() * nHash, nHash,
              newSequent) {
    /* This is initialized to be the largest (loosest)
     * possible DBM
     * @see DBM Constructor (Default Constructor). */
    INFTYDBM = new DBM(input_pes.spaceDimension(), input_pes.clocks());
    INFTYDBM->cf();
  }

  ~prover() {
    delete INFTYDBM;
  }

  size_t getNumLocations() const { return numLocations; }

  /** Prove a given property for the provided PES. */
  bool do_proof_init(pes& p)
  {
    const ExprNode* start_pred = p.lookup_predicate(p.start_predicate());

    /* A Placeholder to remember the current parity;
     * false = lfp parity, true = gfp parity. */
    currParityGfp = start_pred->get_Parity();
    /* A Placeholder to remember the previous parity;
     * false = lfp parity, true = gfp parity. */
    prevParityGfp = currParityGfp;

   return  do_proof(p.initial_state(), *p.initial_clock_zone(), *start_pred);
  }

  void printTabledSequents(std::ostream& os) const {
    cache.printTabledSequents(os);
  }

protected:
  /** The prover function to prove whether a sequent is true or false.
   * @param step The "tree level" of the sequent in the proof tree.
   * A lower number is closer to the root, and a higher level is close
   * to "leaf" sequents. The main() method
   * that calls this feeds in 0.
   * @param zone (*) The initial DBM of clock constraints (Sequent Premise)
   * @param formula (*) The Expression/Consequent (root of the Expression Tree)
   * that the prover
   * needs to determine if it is true or false.
   * @param discrete_state (*) The current substitution list of variables and their
   * substituted values, used to represent the current
   * atomic "state" of the Sequent.
   * @return True if the expression evaluates to True given the other parameters
   * and False otherwise (if the expression evaluates to False).*/
  __attribute__((flatten)) bool do_proof(const SubstList& discrete_state,
                                         const DBM& zone,
                                         const ExprNode& formula) {
    assert(zone.isInCf());
    bool result = false;
    if (cpplogEnabled(cpplogging::debug)) {
      print_sequent(std::cerr, step, result, zone, formula, discrete_state, formula.getOpType());
    }
    ++step;

    switch (formula.getOpType()) {
      case PREDICATE: {
        result = do_proof_predicate(discrete_state, zone, formula);
        break;
      }
      case AND: {
        result = do_proof_and(discrete_state, zone, formula);
        break;
      }
      case OR: {
        result = do_proof_or(discrete_state, zone, formula);
        break;
      }
      case OR_SIMPLE: {
        result = do_proof_or_simple(discrete_state, zone, formula);
        break;
      }
      case FORALL: {
        result = do_proof_forall(discrete_state, zone, formula);
        break;
      }
      case FORALL_REL: {
        result = do_proof_forall_rel(discrete_state, zone, formula);
        break;
      }
      case EXISTS: {
        result = do_proof_exists(discrete_state, zone, formula);
        break;
      }
      case EXISTS_REL: {
        result = do_proof_exists_rel(discrete_state, zone, formula);
        break;
      }
      case ALLACT: {
        result = do_proof_allact(discrete_state, zone, formula);
        break;
      }
      case EXISTACT: {
        result = do_proof_existact(discrete_state, zone, formula);
        break;
      }
      case IMPLY: {
        result = do_proof_imply(discrete_state, zone, formula);
        break;
      }
      case CONSTRAINT: {
        result = do_proof_constraint(zone, formula);
        break;
      }
      case BOOL: {
        result = do_proof_bool(formula);
        break;
      }
      case ATOMIC: {
        result = do_proof_atomic(discrete_state, formula);
        break;
      }
      case ATOMIC_NOT: {
        result = do_proof_atomic_not(discrete_state, formula);
        break;
      }
      case ATOMIC_LT: {
        result = do_proof_atomic_lt(discrete_state, formula);
        break;
      }
      case ATOMIC_GT: {
        result = do_proof_atomic_gt(discrete_state, formula);
        break;
      }
      case ATOMIC_LE: {
        result = do_proof_atomic_le(discrete_state, formula);
        break;
      }
      case ATOMIC_GE: {
        result = do_proof_atomic_ge(discrete_state, formula);
        break;
      }
      case SUBLIST: {
        result = do_proof_sublist(discrete_state, zone, formula);
        break;
      }
      case RESET: {
        result = do_proof_reset(discrete_state, zone, formula);
        break;
      }
      case ASSIGN: {
        result = do_proof_assign(discrete_state, zone, formula);
        break;
      }
      case REPLACE: {
        result = do_proof_replace(discrete_state, zone, formula);
        break;
      }
      case ABLEWAITINF: {
        result = do_proof_ablewaitinf(discrete_state, zone);
        break;
      }
      case UNABLEWAITINF: {
        result = do_proof_unablewaitinf(discrete_state, zone);
        break;
      }
    }
    --step;
    return result;
  }

  /** The prover function that handles placeholders.
   * @param step The "tree level" of the sequent in the proof tree.
   * A lower number is closer to the root, and a higher level is close
   * to "leaf" sequents. The main() method
   * that calls this feeds in 0.
   * @param zone (*) The initial DBM of clock constraints (Sequent Premise)
   * @param place (*) The current zone union of the Placeholder DBM.
   * @param formula (*) The Expression/Consequent (root of the Expression Tree)
   * that the prover
   * needs to determine if it is true or false.
   * @param discrete_state (*) The current substitution list of variables and their
   * substituted values, used to represent the current
   * atomic "state" of the Sequent.
   * @return The DBM Value of the placeholder constraint or an empty DBM if
   * no valid value for the placeholder exists (thus proof is Invalid).
   * The sequent is valid for the clock valuations in the intersection of zone
   * and the return value. */
  __attribute__((flatten)) void do_proof_place(const SubstList& discrete_state,
                                               const DBM& zone, DBMList* place,
                                               const ExprNode& formula) {
    /* do_proof_place() written by Peter Fontana, needed for support
     * of EXISTS Quantifiers. */
    assert(zone.isInCf());

    if (cpplogEnabled(cpplogging::debug)) {
      print_sequent_place(std::cerr, step, false, zone, *place, formula,
                          discrete_state, formula.getOpType());
    }

    ++step;
    switch (formula.getOpType()) {
      case PREDICATE: {
        do_proof_place_predicate(discrete_state, zone, place, formula);
        break;
      }
      case AND: {
        do_proof_place_and(discrete_state, zone, place, formula);
        break;
      }
      case OR: {
        do_proof_place_or(discrete_state, zone, place, formula);
        break;
      }
      case OR_SIMPLE: {
        do_proof_place_or_simple(discrete_state, zone, place, formula);
        break;
      }
      case FORALL: {
        do_proof_place_forall(discrete_state, zone, place, formula);
        break;
      }
      case FORALL_REL: {
        do_proof_place_forall_rel(discrete_state, zone, place, formula);
        break;
      }
      case EXISTS: {
        do_proof_place_exists(discrete_state, zone, place, formula);
        break;
      }
      case EXISTS_REL: {
        do_proof_place_exists_rel(discrete_state, zone, place, formula);
        break;
      }
      case ALLACT: {
        do_proof_place_allact(discrete_state, zone, place, formula);
        break;
      }
      case EXISTACT: {
        do_proof_place_existact(discrete_state, zone, place, formula);
        break;
      }
      case IMPLY: {
        do_proof_place_imply(discrete_state, zone, place, formula);
        break;
      }
      case CONSTRAINT: {
        do_proof_place_constraint(zone, place, formula);
        break;
      }
      case BOOL: {
        do_proof_place_bool(place, formula);
        break;
      }
      case ATOMIC: {
        do_proof_place_atomic(discrete_state, place, formula);
        break;
      }
      case ATOMIC_NOT: {
        do_proof_place_atomic_not(discrete_state, place, formula);
        break;
      }
      case ATOMIC_LT: {
        do_proof_place_atomic_lt(discrete_state, place, formula);
        break;
      }
      case ATOMIC_GT: {
        do_proof_place_atomic_gt(discrete_state, place, formula);
        break;
      }
      case ATOMIC_LE: {
        do_proof_place_atomic_le(discrete_state, place, formula);
        break;
      }
      case ATOMIC_GE: {
        do_proof_place_atomic_ge(discrete_state, place, formula);
        break;
      }
      case SUBLIST: {
        do_proof_place_sublist(discrete_state, zone, place, formula);
        break;
      }
      case RESET: {
        do_proof_place_reset(discrete_state, zone, place, formula);
        break;
      }
      case ASSIGN: {
        do_proof_place_assign(discrete_state, zone, place, formula);
        break;
      }
      case REPLACE: {
        do_proof_place_replace(discrete_state, zone, place, formula);
        break;
      }
      case ABLEWAITINF: {
        do_proof_place_ablewaitinf(discrete_state, zone, place);
        break;
      }
      case UNABLEWAITINF: {
        do_proof_place_unablewaitinf(discrete_state, zone, place);
        break;
      }
    }

    --step;
  }

  bool do_proof_predicate(const SubstList& discrete_state, const DBM& zone,
                          const ExprNode& formula);
  bool do_proof_and(const SubstList& discrete_state, const DBM& zone,
                    const ExprNode& formula);
  bool do_proof_or(const SubstList& discrete_state, const DBM& zone,
                   const ExprNode& formula);
  bool do_proof_or_simple(const SubstList& discrete_state, const DBM& zone,
                          const ExprNode& formula);
  bool do_proof_forall(const SubstList& discrete_state, const DBM& zone,
                       const ExprNode& formula);
  bool do_proof_forall_rel(const SubstList& discrete_state, const DBM& zone,
                           const ExprNode& formula);
  bool do_proof_exists(const SubstList& discrete_state, const DBM& zone,
                       const ExprNode& formula);
  bool do_proof_exists_rel(const SubstList& discrete_state, const DBM& zone,
                           const ExprNode& formula);
  bool do_proof_allact(const SubstList& discrete_state, const DBM& zone,
                       const ExprNode& formula);
  bool do_proof_existact(const SubstList& discrete_state, const DBM& zone,
                         const ExprNode& formula);
  bool do_proof_imply(const SubstList& discrete_state, const DBM& zone,
                      const ExprNode& formula);
  bool do_proof_constraint(const DBM& zone, const ExprNode& formula);
  bool do_proof_bool(const ExprNode& formula);
  bool do_proof_atomic(const SubstList& discrete_state,
                       const ExprNode& formula);
  bool do_proof_atomic_not(const SubstList& discrete_state,
                           const ExprNode& formula);
  bool do_proof_atomic_lt(const SubstList& discrete_state,
                          const ExprNode& formula);
  bool do_proof_atomic_gt(const SubstList& discrete_state,
                          const ExprNode& formula);
  bool do_proof_atomic_le(const SubstList& discrete_state,
                          const ExprNode& formula);
  bool do_proof_atomic_ge(const SubstList& discrete_state,
                          const ExprNode& formula);
  bool do_proof_sublist(const SubstList& discrete_state, const DBM& zone,
                        const ExprNode& formula);
  bool do_proof_reset(const SubstList& discrete_state, const DBM& zone,
                      const ExprNode& formula);
  bool do_proof_assign(const SubstList& discrete_state, const DBM& zone,
                       const ExprNode& formula);
  bool do_proof_replace(const SubstList& discrete_state, const DBM& zone,
                        const ExprNode& formula);
  bool do_proof_ablewaitinf(const SubstList& discrete_state, const DBM& zone);
  bool do_proof_unablewaitinf(const SubstList& discrete_state, const DBM& zone);

  void do_proof_place_predicate(const SubstList& discrete_state,
                                    const DBM& zone, DBMList* place,
                                    const ExprNode& formula);
  void do_proof_place_and(const SubstList& discrete_state,
                              const DBM& zone, DBMList* place,
                              const ExprNode& formula);
  void do_proof_place_or(const SubstList& discrete_state,
                             const DBM& zone, DBMList* place,
                             const ExprNode& formula);
  void do_proof_place_or_simple(const SubstList& discrete_state,
                                    const DBM& zone, DBMList* place,
                                    const ExprNode& formula);
  void do_proof_place_forall(const SubstList& discrete_state,
                                 const DBM& zone, DBMList* place,
                                 const ExprNode& formula);
  void do_proof_place_forall_rel(const SubstList& discrete_state,
                                     const DBM& zone, DBMList* place,
                                     const ExprNode& formula);
  void do_proof_place_exists(const SubstList& discrete_state,
                                 const DBM& zone, DBMList* place,
                                 const ExprNode& formula);
  void do_proof_place_exists_rel(const SubstList& discrete_state,
                                     const DBM& zone, DBMList* place,
                                     const ExprNode& formula);
  void do_proof_place_allact(const SubstList& discrete_state,
                                 const DBM& zone, DBMList* place,
                                 const ExprNode& formula);
  void do_proof_place_existact(const SubstList& discrete_state,
                                   const DBM& zone, DBMList* place,
                                   const ExprNode& formula);
  void do_proof_place_imply(const SubstList& discrete_state,
                                const DBM& zone, DBMList* place,
                                const ExprNode& formula);
  void do_proof_place_constraint(const DBM& zone, DBMList* place,
                                     const ExprNode& formula);
  void do_proof_place_bool(DBMList* place, const ExprNode& formula);
  void do_proof_place_atomic(const SubstList& discrete_state,
                                 DBMList* place,
                                 const ExprNode& formula);
  void do_proof_place_atomic_not(const SubstList& discrete_state,
                                     DBMList* place,
                                     const ExprNode& formula);
  void do_proof_place_atomic_lt(const SubstList& discrete_state,
                                    DBMList* place,
                                    const ExprNode& formula);
  void do_proof_place_atomic_gt(const SubstList& discrete_state,
                                    DBMList* place,
                                    const ExprNode& formula);
  void do_proof_place_atomic_le(const SubstList& discrete_state,
                                    DBMList* place,
                                    const ExprNode& formula);
  void do_proof_place_atomic_ge(const SubstList& discrete_state,
                                    DBMList* place,
                                    const ExprNode& formula);
  void do_proof_place_sublist(const SubstList& discrete_state,
                                  const DBM& zone, DBMList* place,
                                  const ExprNode& formula);
  void do_proof_place_reset(const SubstList& discrete_state,
                                const DBM& zone, DBMList* place,
                                const ExprNode& formula);
  void do_proof_place_assign(const SubstList& discrete_state,
                                 const DBM& zone, DBMList* place,
                                 const ExprNode& formula);
  void do_proof_place_replace(const SubstList& discrete_state,
                                  const DBM& zone, DBMList* place,
                                  const ExprNode& formula);
  void do_proof_place_ablewaitinf(const SubstList& discrete_state,
                                      const DBM& zone, DBMList* place);
  void do_proof_place_unablewaitinf(const SubstList& discrete_state,
                                        const DBM& zone, DBMList* place);

  /** Method to compute the predecessor check of relativized exists operators.
   * This method is inlined for performance reasons.
   * @param zone (*) the left-hand clock set
   * @param lhsSucc (*) the successor of the left-hand clock constraint, after
   * applying invariants.
   * @param phi1Place (*) the set of clock valuations that satisfy phi1, the
   * left hand formula (the relativized formula).
   * @param phi2Place (*) the set of clock valuations that satisfy phi2, the
   * right hand formula.
   * @param phi2PredPlace (*) the time predecessor of phi2Place; this
   * predecessor may by <= or <, depending on the proof rule that calls this
   * method. */
  inline void predCheckRule(DBMList* result,
                            const DBM& zone,
                            const DBM* const lhs_succ,
                            const DBMList* placeholder1,
                            const DBMList* placeholder2,
                            const DBMList* placeholder2_predecessor) {
    result->makeEmpty();

    DBMList placeholder1_complement(*placeholder1);
    !placeholder1_complement; // all values outside placeholder1
    placeholder1_complement.cf();
    bool previouslyUpdated = false;
    /* Iterate through each DBM of phi2Place and union the results. */
    const std::vector<DBM*>* placeholder2_dbms = placeholder2->getDBMList();

    for (std::vector<DBM*>::const_iterator i = placeholder2_dbms->begin();
         i != placeholder2_dbms->end(); ++i) {
      DBM placeholder2_dbm_pred(**i);
      placeholder2_dbm_pred.pre();
      placeholder2_dbm_pred.cf();

      DBMList currDBMList(placeholder1_complement);
      currDBMList.intersect(placeholder2_dbm_pred);
      currDBMList.intersect(*lhs_succ); // Intersect with the successor of the zone;
      // So currDBMList now contains all states that are not in placeholder1,
      // from which placeholder2 can be reached, and which can be reached from
      // zone.

      DBMList placeholder2_dbm_complement(**i);
      !placeholder2_dbm_complement;
      placeholder2_dbm_complement.cf();

      currDBMList.intersect(placeholder2_dbm_complement);
      // We restrict this to states that furthermore are not in placeholder2.
      // So currDBMList now contains all states that are not in placeholder1,
      // from which placeholder2 can be reached, but which are themselves not in
      // placeholder2, and which can be reached from zone.
      currDBMList.cf();
      currDBMList.pre();
      currDBMList.intersect(*lhs_succ);
      currDBMList.cf();
      // currDBMList currently is the set of bad times; LHS must have
      // no such times in this.
      if (currDBMList.emptiness()) { // no bad times, so no shrinkage
        *result = *placeholder1;
        break;
      }
      /* If this is nonempty, then we have something to deal with */
      // Also, the placeholder cannot be completely contained in this
      currDBMList.intersect(zone);
      currDBMList.cf();
      if (!previouslyUpdated) {
        previouslyUpdated = true;
      }

      if (!currDBMList.emptiness()) {
        result->addDBMList(currDBMList);
      }
    }

    /* We also need to make another placeholder check: that the phi1Place
     * is a placeholder that can be formed
     * by taking the predecessor
     * and intersecting it with succ(\Gamma). We need phi1Place to be
     * the entire predecessor, and not just the upper part of it. */
    if (!(*result >= zone)) {
      // simple empty case
      result->makeEmpty();
    }
    // else, we just need to check for gaps in the DBM and eliminate them.
    // does this case come up due to how pred check works?
  }

  /** Performs the succCheck rule of FORALL (and FORALL_REL) rules, including
   * the computing of the premise, the consequent, and the tightening of the
   * placeholder placeholder_forall.
   * @param discrete_state (*) reference to the discrete state for which we are
   * proving
   * @param zone (*) the reference to the left hand side of the sequent
   * @param placeholder (*) the reference to the current placeholder.
   * @param placeholder_forall (*) the placeholder that is tightened such that
   *        the side condition on the successors holds. It is the empty
   * placeholder if no such placeholder can be found. */
  inline void succCheckRule(const SubstList* const discrete_state,
                            const DBM& zone, const DBM* const lhs_succ,
                            const DBMList* placeholder,
                            DBMList* placeholder_forall) {
    // Initially guess that the resulting placeholder is the placeholder that
    // was precomputed, extended with the complement of the invariant of the
    // current discrete state. The intuition is that we compute the implication:
    // if the invariant holds, then the placeholder is satisfied.
    *placeholder_forall = *placeholder;

    DBMList invariant_region(*INFTYDBM);
    bool nonempty_invariant = restrict_to_invariant(
        input_pes.invariants(), &invariant_region, *discrete_state);
    if (nonempty_invariant) {
      !invariant_region;
      invariant_region.cf();
      placeholder_forall->addDBMList(invariant_region);
      placeholder_forall->cf();
    }

    // intersect with new placeholder
    DBMList lhs_succ_and_placeholder(*placeholder_forall);
    lhs_succ_and_placeholder.intersect(*lhs_succ);
    lhs_succ_and_placeholder.cf(); // The consequent

    /* Computing Premise of Right part of proof */
    /* Compute Succ(Premise and First Placeholder) */
    // succLHS is the successor of the left-hand side, so do not repeat the work
    DBMList premise_and_placeholder_succ(zone);
    premise_and_placeholder_succ.intersect(*placeholder_forall);
    premise_and_placeholder_succ.cf();
    premise_and_placeholder_succ.suc();
    premise_and_placeholder_succ.cf();

    // First start by setting the place holder to the value of the new
    // placeholder
    if (!(lhs_succ_and_placeholder >= premise_and_placeholder_succ)) {
      /* If we are here, then we have one of two cases:
       * 1. The succCheck fails (since it is not possible)
       * 2. THe placeholder needs to be tightened so it can pass.
       * Invariants make this tricky */
      // Find the bad zones;
      DBMList badVals(*placeholder_forall);
      // !(badVals || !succPrem || !succLHS) == !badVals && succPrem && succLHS
      !badVals; // All states outside currPlace
      badVals.cf();
      badVals.intersect(premise_and_placeholder_succ); // that can be reached from zone &
                                             // currPlace
      badVals.intersect(*lhs_succ);          // *and* that can be reached from zone -- this should be
                                             // superfluous
      badVals.cf();
      badVals.pre();
      // all states with a delay into those states outside currPlace that can be
      // reached from zone & currPlace
      badVals.cf();
      // At this point, we have the bad valuations. Now intersect their
      // complement
      !badVals;
      // all states for which all delays remain inside currPlace, or can be
      // reached from zone & currPlace
      badVals.cf();
      // Good values must be after succLHS
      badVals.intersect(*lhs_succ);
      // all states for which all delays remain inside currPlace, or can be
      // reached from zone & currPlace, that can be reached from zone. really, at
      // this point badVals contains the *good* values
      badVals.cf();
      placeholder_forall->intersect(badVals);
      placeholder_forall->cf();
      if(!placeholder_forall->emptiness()) {
        // The placheolder has shrunk; we now check whether the side condition is
        // satisfied.
        // leave conseq unchanged, since that placeholder did not shrink
        premise_and_placeholder_succ = zone;
        premise_and_placeholder_succ.intersect(*placeholder_forall);
        premise_and_placeholder_succ.cf();
        premise_and_placeholder_succ.suc();
        premise_and_placeholder_succ.cf();

        // use previously solved place, not new one for right hand side
        if (!(lhs_succ_and_placeholder >= premise_and_placeholder_succ)) {
          placeholder_forall->makeEmpty();
        }
      }
    }
  }
};

/* IMPLEMENTATION PROOF WITHOUT PLACEHOLDERS */
inline bool prover::do_proof_predicate(const SubstList& discrete_state,
                                       const DBM& zone,
                                       const ExprNode& formula) {
  bool retVal = false;

  ExprNode* e = input_pes.lookup_equation(formula.getPredicate());

  // Get Predicate Index for Hashing
  int predicate_index =
      input_pes.lookup_predicate(formula.getPredicate())->getIntVal() - 1;
  prevParityGfp = currParityGfp;
  currParityGfp = formula.get_Parity();

  /* Look in Known True and Known False Sequent Caches */
  if (useCaching) {
    /* First look in known False Sequent table */
    { // Restricted scope for looking up false sequents
      Sequent* cached_sequent =
          cache.Xlist_false.look_for_sequent(&discrete_state, predicate_index);
      if (cached_sequent != nullptr &&
          cached_sequent->tabled_false_sequent(zone)) {
        cpplog(cpplogging::debug)
            << "---(Invalid) Located a Known False Sequent ----" << std::endl
            << std::endl;

        /* Add backpointer to parent sequent (shallow copy) */
        cached_sequent->addParent(parentRef);
        return false;
      }
    }

    /* Now look in known True Sequent table */
    { // Restricted scope for looking up true sequents
      Sequent* cached_sequent =
          cache.Xlist_true.look_for_sequent(&discrete_state, predicate_index);
      if (cached_sequent != nullptr && cached_sequent->tabled_sequent(zone)) {
        cpplog(cpplogging::debug)
            << "---(Valid) Located a Known True Sequent ----" << std::endl
            << std::endl;

        /* Add backpointer to parent sequent (shallow copy) */
        cached_sequent->addParent(parentRef);
        return true;
      }
    }
  }

  /* Now deal with greatest fixpoint circularity and least
   * fixpoint circularity */
  Sequent* h = nullptr;
  { // Restricted scope for detecting circularities
    Sequent* t = new Sequent(&formula, &discrete_state);
    if (currParityGfp) { // Thus a Greatest Fixpoint
      h = cache.Xlist_pGFP.locate_sequent(t, predicate_index);
      if ((!newSequent) && h->tabled_sequent(zone)) {
        // Found gfp Circularity - thus valid
        cpplog(cpplogging::debug)
            << "---(Valid) Located a True Sequent or gfp Circularity ----"
            << std::endl
            << std::endl;

        /* Add backpointer to parent sequent (shallow copy) */
        h->addParent(parentRef);

        // Add sequent to known true cache
        if (useCaching) {
          Sequent* true_sequent = new Sequent(&formula, &discrete_state);
          Sequent* cached_true_sequent =
              cache.Xlist_true.locate_sequent(true_sequent, predicate_index);
          cached_true_sequent->update_sequent(zone);
        }
        return true; // greatest fixed point circularity found
      }

      h->push_sequent(new DBM(zone));
    } else { // Thus, a least fixpoint
      // Now look for a Circularity
      h = cache.Xlist_pLFP.locate_sequent(t, predicate_index);
      if ((!newSequent) && h->tabled_sequent_lfp(zone)) {
        cpplog(cpplogging::debug)
            << "---(Invalid) Located a lfp Circularity ----" << std::endl
            << std::endl;

        /* Add backpointer to parent sequent (shallow copy) */
        h->addParent(parentRef);

        // Now Put Sequent in False Cache
        if (useCaching) {
          Sequent* false_sequent = new Sequent(&formula, &discrete_state);
          Sequent* cached_false_sequent =
              cache.Xlist_false.locate_sequent(false_sequent, predicate_index);
          cached_false_sequent->update_false_sequent(zone);
        }
        return false; // least fixed point circularity found
      }

      h->push_sequent(new DBM(zone));
    }
  } // End scope for circularity
  assert(h != nullptr);
  // no least/greatest fixed point circularity was found; the sequent has been
  // added to the appropriate cache.

  // NO CIRCULARITY FOUND

  /* Assign parent value after caching since during caching we may have
   * to use the previous parent */
  Sequent* tempParentState = parentRef;
  /* Get the current variable: do a shallow, not deep copy */
  parentRef = h;

  retVal = do_proof(discrete_state, zone, *e);

    /* Now update the parent so it points to the previous parent, and not this
   * predicate */
  parentRef = tempParentState;

  /* Key Concept of Purging:
   * If Was True, discovered false, check that
   *		Z_now_false <= Z_cached_true | or | Z_cached_true >= Z_now_false
   * If Was False, discovered true, check that
   *		Z_now_true >= Z_cached_false | or | Z_cached_false <= Z_now_true
   * This Must be done regardless of how the tabling
   * is done for that specific cache */
  // Purge updated sequent
  if (useCaching) {
    if (retVal) {
      /* First look in opposite parity Caches */
      bool madeEmpty = false;
      Sequent* true_sequent = new Sequent(&formula, &discrete_state);
      /* If found, Purge Sequent from its cache */
      Sequent* cached_false_sequent =
          cache.Xlist_false.look_for_and_purge_rhs_sequent(
              &zone, true_sequent, predicate_index, false, &madeEmpty);

      /* Now purge backpointers */
      if (cached_false_sequent != nullptr) {
        cache.look_for_and_purge_rhs_backStack(
            cached_false_sequent->parents(),
            cached_false_sequent->parents_with_placeholders());
      }

      // Now update in proper Cache
      Sequent* cached_true_sequent =
          cache.Xlist_true.locate_sequent(true_sequent, predicate_index);
      cached_true_sequent->update_sequent(zone);
      // Since we update the cached_true_sequent with true_sequent, we shall
      // not free true_sequent.

      if (madeEmpty) {
        delete cached_false_sequent;
      }
    } else { // !retVal
      /* True cache (not gfp caches) */
      Sequent* false_sequent = new Sequent(&formula, &discrete_state);
      bool madeEmpty = false;
      /* If found, Purge Sequent from its cache */
      Sequent* cached_true_sequent =
          cache.Xlist_true.look_for_and_purge_rhs_sequent(
              &zone, false_sequent, predicate_index, true, &madeEmpty);

      /* Now purge backpointers.
       * Ignore circularity booleans because they do not form backpointers */
      if (cached_true_sequent != nullptr) {
        cache.look_for_and_purge_rhs_backStack(
            cached_true_sequent->parents(),
            cached_true_sequent->parents_with_placeholders());
      }

      // Now update in proper Cache
      Sequent* cached_false_sequent =
          cache.Xlist_false.locate_sequent(false_sequent, predicate_index);
      cached_false_sequent->update_false_sequent(zone);

      if (madeEmpty) {
        delete cached_true_sequent;
      }
    }
  }

  /* The line: h->addParent(parentRef);
   * is not needed since the backpointer stored before proof. */
  h->pop_sequent();
  return retVal;
}

// [FC14] Proof rule \land
inline bool prover::do_proof_and(const SubstList& discrete_state,
                                 const DBM& zone, const ExprNode& formula) {
  /* Because zone is only changed after it is copied, it can
   * be passed to both branches. */
  bool retVal = do_proof(discrete_state, zone, *formula.getLeft());
  if (retVal) {
    retVal = do_proof(discrete_state, zone, *formula.getRight());
  }
  return retVal;
}

/* For an expression l || r we consider three cases, using a placeholder:
 * - the proof for l returns an empty placeholder
 * - the proof for l covers the entire DBM zone
 * - the proof for l covers a strict, non-empty subset of zone
 */
// [FC14] Proof rule based on \lor_{s_2}
inline bool prover::do_proof_or(const SubstList& discrete_state,
                                const DBM& zone, const ExprNode& formula) {
  bool retVal = false;

  /* Use two placeholders to provide split here */
  DBMList placeholder1(*INFTYDBM);
  do_proof_place(discrete_state, zone, &placeholder1, *formula.getLeft());
  placeholder1.cf();

  // We optimise on proving the right hand side, depending on the placeholder.
  // If empty, the right hand side needs to hold for the entire DBM
  // If the placeholder already covers the entire DBM, we are done,
  // otherwise we need to prove the right hand side for a fresh placeholder.

  // Reset place parent to NULL
  parentPlaceRef = nullptr;
  if (placeholder1.emptiness()) {
    retVal = do_proof(discrete_state, zone, *formula.getRight());
  } else if (placeholder1 >= zone) {
    retVal = true;
  } else {
    /* Here we get the corner case where we have to use the
     * OR Split rule, so we try to establish whether part of zone is covered by
     * l, and the other part is covered by formula. */
    DBMList placeholder2(*INFTYDBM);
    do_proof_place(discrete_state, zone, &placeholder2, *formula.getRight());
    placeholder2.cf();

    // Reset place parent to NULL
    parentPlaceRef = nullptr;
    if (placeholder2.emptiness()) {
      retVal = false;
    } else if (placeholder2 >= zone) {
      retVal = true;
    } else {
      placeholder2.addDBMList(placeholder1); // here placeholder2 is placeholder
                                             // \phi_{\lor} from [FC14]
      retVal = placeholder2 >= zone; // if the union of both placeholders covers
                                     // the set of states, we are still happy
    }
  }
  return retVal;
}

// [FC14], rules \lor_{l} and \lor_{r}
inline bool prover::do_proof_or_simple(const SubstList& discrete_state,
                                       const DBM& zone,
                                       const ExprNode& formula) {
  /* Simplified OR does not need to split on placeholders */
  bool retVal = do_proof(discrete_state, zone, *formula.getLeft());
  if (!retVal) {
    retVal = do_proof(discrete_state, zone, *formula.getRight());
  }
  return retVal;
}

// [FC14] Rule \forall_{t1}
inline bool prover::do_proof_forall(const SubstList& discrete_state,
                                    const DBM& zone, const ExprNode& formula) {
  /* Here the model checker looks at the zone of
   * all time sucessors and then substitutes in
   * the substitued constraints and sees if the
   * zone satifies the constraints */
  /* DBM zone is copied because it is changed by suc() and invs_chk().
   * The copying here assures that zone is unchanged when it is returned,
   * allowing multiple branches of AND and OR to have the same zone. */
  DBM succ_lhs(zone);
  succ_lhs.suc();
  restrict_to_invariant(input_pes.invariants(), &succ_lhs, discrete_state);
  succ_lhs.cf();

  return do_proof(discrete_state, succ_lhs, *formula.getQuant());
}

// [FC14] Proof rules \forall_{ro1}, \forall_{ro2}, \forall_{ro3}
inline bool prover::do_proof_forall_rel(const SubstList& discrete_state,
                                        const DBM& zone,
                                        const ExprNode& formula) {
  /* Proof methodology:
   * first, see if \phi_1 is satisfied during the time advance.
   * If it is, check that phi_2 is true both at and before those
   * times (time predecessor).
   * If this is not satisfactory, then do a regular FORALL proof
   * without a placeholder. */

  bool retVal = false;

  /* First, see if \exists(phi_1) is true. The common case is that it
   * will not be. */
  DBM lhs_succ(zone);
  lhs_succ.suc();
  // Make sure lhs_succ is not modified; we reuse it for the sake of efficiency.

  DBMList placeholder1(*INFTYDBM); // phi_{s1}
  restrict_to_invariant(input_pes.invariants(), &placeholder1, discrete_state);
  do_proof_place(discrete_state, lhs_succ, &placeholder1, *formula.getLeft());
  placeholder1.cf();

  // Reset place parent to NULL
  parentPlaceRef = nullptr;

  if (placeholder1.emptiness()) { // Here, \forall phi_2 needs to hold.
    // [FC14] derived rule? of \forall_{ro1} TODO
    if (cpplogEnabled(cpplogging::debug)) {
      print_sequentCheck(std::cerr, step - 1, retVal, zone, placeholder1,
                         discrete_state, formula.getOpType());
      cpplog(cpplogging::debug)
          << "----() Empty Relativization Placeholder: phi1 is never true -----"
          << std::endl
          << std::endl;
    }

    /* Since here, \forall phi_2 must be true; we use \forall_{ro1}.
     * Note that we do not call do_proof_forall on a new sequent, instead we
     * unfold the definition of \forall_{t1}. */
    /* DBM zone is copied because it is changed by suc() and invs_chk().
     * The copying here assures that zone is unchanged when it is returned,
     * allowing multiple branches of AND and OR to have the same zone. */
    DBM lhs_succ_invariant(lhs_succ); // that part of lhs_succ that satisfies
                                      // the location invariant
    restrict_to_invariant(input_pes.invariants(), &lhs_succ_invariant, discrete_state);
    lhs_succ_invariant.cf();
    retVal = do_proof(discrete_state, lhs_succ_invariant, *formula.getRight());
  } else if (placeholder1 >= zone) {
    // placeholder1 nonempty
    /* First check for the simplest case: no time elapse is needed */
    /* For improved performance, first ask if the formula
     * is true with no time elapse. */
    retVal = true;
    // [FC14] proof rule \forall_{ro2};
    if (cpplogEnabled(cpplogging::debug)) {
      print_sequentCheck(cpplogGet(cpplogging::debug), step - 1, retVal, zone,
                         placeholder1, discrete_state, formula.getOpType());
      cpplog(cpplogging::debug) << "----(Valid) Placeholder indicates no time "
                                   "elapse is needed (Check Only)-----"
                                << std::endl
                                << "----With Placeholder := {" << placeholder1
                                << "} ----" << std::endl
                                << std::endl;
    }

    // If here, we neither need a placeholder nor to elapse time
    retVal = do_proof(discrete_state, zone, *formula.getRight());
  } else {
    retVal = true;
    // This is the more complicated case that requires a placeholder
    // for the FORALL
    /* Now check that we can elapse to the placeholder. */
    // Store the set of times that satisfy phi1
    cpplog(cpplogging::debug)
        << "----() Relativization \\phi_1 placeholder obtained as {"
        << placeholder1 << "} ----" << std::endl
        << std::endl;

    /* We omit the check that we can elapse to the placeholder;
     * We will check that once at the end */
    DBMList placeholder2(*INFTYDBM);
    DBM lhs_succ2(lhs_succ); // copy to avoid modifying lhs_succ
    do_proof_place(discrete_state, lhs_succ2, &placeholder2, *formula.getRight());
    placeholder2.cf();

    cpplog(cpplogging::debug)
        << "----() Formula \\phi_2 placeholder obtained as {" << placeholder2
        << "} ----" << std::endl
        << std::endl;

    // Reset place parent to NULL
    parentPlaceRef = nullptr;
    if (placeholder2.emptiness()) { // \phi_2 is satisfied nowhere.
      retVal = false;
    } else if (placeholder2 >= lhs_succ) {
      /* In this simple case, all possible times satisfy \phi_2
       * so we can avoid many checks. */
      retVal = true;
    } else {
      /* Now do a succ check on phi_2 to get \phi_forall
       * and a predCheck using both phi_1 and phi_2 to get phi_exists */
      /* we also note that the times satisfying \phi_1
       * (the relativization formula condition) are neither empty
       * nor everything. */

      DBMList placeholder_forall(*INFTYDBM);
      succCheckRule(&discrete_state, zone, &lhs_succ, &placeholder2, &placeholder_forall);
      placeholder_forall.cf();

      if (cpplogEnabled(cpplogging::debug)) {
        print_sequentCheck(cpplogGet(cpplogging::debug), step - 1, retVal,
                           lhs_succ2, placeholder2, discrete_state, formula.getOpType());
        cpplog(cpplogging::debug)
            << "----() FORALL (of FORALL_REL) Placeholder Check obtained  FA "
               "Placeholder := {"
            << placeholder_forall << "} ----" << std::endl
            << std::endl;
      }

      /* Now we do the pred check to find the exists placeholder;
       * This involves the predCheck method and checking that time can
       * can elapse. Note that the exists is a simplified version
       * where \phi_2 (the right) is the relativized clause and
       * \phi_1 (the left) is the formula. By using the placeholders
       * computed previously, we save time by not having to recompute
       * the formulas. */
      DBMList placeholder1_predecessor(placeholder1);
      placeholder1_predecessor.pre();
      placeholder1_predecessor.cf();

      DBMList placeholder_exists(*INFTYDBM);
      /*--- PredCheck code----*/
      predCheckRule(&placeholder_exists, zone, &lhs_succ, &placeholder2,
                    &placeholder1, &placeholder1_predecessor);
      placeholder_exists.cf();
      cpplog(cpplogging::debug)
          << "----() FORALL Rel Exists predCheck placeholder obtained as := {"
          << placeholder_exists << "} ----" << std::endl
          << std::endl;

      if (!placeholder_exists.emptiness()) {
        /* if it is nonempty, it passes the second check and we continue
         * Given the FORALL rule rewrite, do not allow the instance
         * after the time elapse */
        /* Extract the new refined placeholder. */
        placeholder_exists.intersect(placeholder1);
        placeholder_exists.cf();

        /* Now check that it works. */
        placeholder_exists.pre();
        /* This cf() is needed. */
        placeholder_exists.cf();
        // Need we intersect this with succ(Gamma) or
        // do we need to perform an elapse check?
        // what if this is empty?

        if (cpplogEnabled(cpplogging::debug)) {
          print_sequentCheck(cpplogGet(cpplogging::debug), step - 1, retVal,
                             zone, placeholder_exists, discrete_state, formula.getOpType());
          cpplog(cpplogging::debug)
              << "----() FORALL Rel Exists placeholder after time elapse check "
                 "is := {"
              << placeholder_exists << "} ----" << std::endl
              << std::endl;
        }
      }
      /* Last, we do an or check on the two placeholders */
      bool forallEmpty = placeholder_forall.emptiness();
      bool existsEmpty = placeholder_exists.emptiness();
      if (forallEmpty && existsEmpty) {
        retVal = false;
      } else if (existsEmpty) {
        placeholder_exists = placeholder_forall;
      } else if (!forallEmpty && !existsEmpty) {
        if (placeholder_exists <= placeholder_forall) {
          placeholder_exists = placeholder_forall;
        } else if (!(placeholder_forall <= placeholder_exists)) {
          /* This case requires us to union the two placeholders. */
          placeholder_exists.addDBMList(placeholder_forall);
        }
      }
      retVal = placeholder_exists >= zone;

      // Debug information here?
      if (cpplogEnabled(cpplogging::debug)) {
        print_sequentCheck(cpplogGet(cpplogging::debug), step - 1, retVal, zone,
                           placeholder_exists, discrete_state, formula.getOpType());
        cpplog(cpplogging::debug)
            << "----() Final FORALL REL Placeholder is := {"
            << placeholder_exists << "} ----" << std::endl
            << std::endl;
      }
    }
  }

  return retVal;
}

// [FC14] Proof rule \exists_{t1}
inline bool prover::do_proof_exists(const SubstList& discrete_state,
                                    const DBM& zone, const ExprNode& formula) {
  bool retVal = false;

  /* Support for exists(), written by Peter Fontana */
  // This support gives a placeholder variable
  // and uses a similar method do_proof_place
  // which recursively uses (slightly more complex rules)
  // to solve for the placeholders.

  /* First Try to get a placeholder value that works */
  DBM lhs_succ(zone);
  lhs_succ.suc();

  /* The proper derivation for EXISTS is to incorporate the invariant
   * in the placeholder, and not the LHS. */
  DBMList placeholder(*INFTYDBM);
  restrict_to_invariant(input_pes.invariants(), &placeholder, discrete_state);

  do_proof_place(discrete_state, lhs_succ, &placeholder, *formula.getQuant());
  // Reset place parent to NULL
  parentPlaceRef = nullptr;
  placeholder.cf();
  if (placeholder.emptiness()) {
    retVal = false;
    if (cpplogEnabled(cpplogging::debug)) {
      print_sequentCheck(cpplogGet(cpplogging::debug), step - 1, retVal, zone,
                         placeholder, discrete_state, formula.getOpType());
      cpplog(cpplogging::debug) << "----(Invalid) Empty Placeholder: No Need "
                                   "for Placeholder Check-----"
                                << std::endl
                                << std::endl;
    }
    return retVal;
  } else {
    /* Now check that it works. */
    placeholder.pre();
    /* This cf() is needed. */
    placeholder.cf();
    retVal = placeholder >= zone;

    if (cpplogEnabled(cpplogging::debug)) {
      print_sequentCheck(cpplogGet(cpplogging::debug), step - 1, retVal, zone,
                         placeholder, discrete_state, formula.getOpType());
      if (retVal) {
        cpplog(cpplogging::debug)
            << "----(Valid) Placeholder Check Passed (Check Only)-----"
            << std::endl
            << "----With Placeholder := {" << placeholder << "} ----"
            << std::endl
            << std::endl;

      } else {
        cpplog(cpplogging::debug)
            << "----(Invalid) Placeholder Check Failed-----" << std::endl
            << std::endl;
      }
    }

    return retVal;
  }
}

inline bool prover::do_proof_exists_rel(const SubstList& discrete_state,
                                        const DBM& zone,
                                        const ExprNode& formula) {
  bool retVal = false;

  /* First Try to get a placeholder value that works */
  DBM zone_succ(zone);
  zone_succ.suc();

  DBMList placeholder2(*INFTYDBM);
  restrict_to_invariant(input_pes.invariants(), &placeholder2, discrete_state);

  do_proof_place(discrete_state, zone_succ, &placeholder2, *formula.getRight());
  // Reset place parent to NULL
  parentPlaceRef = nullptr;
  placeholder2.cf();
  if (placeholder2.emptiness()) {
    retVal = false;
    if (cpplogEnabled(cpplogging::debug)) {
      print_sequentCheck(cpplogGet(cpplogging::debug), step - 1, retVal, zone,
                         placeholder2, discrete_state, formula.getOpType());
      cpplog(cpplogging::debug) << "----(Invalid) Empty First Placeholder: No "
                                   "Need for additional Placeholder Checks-----"
                                << std::endl
                                << std::endl;
    }
  } else {
    retVal = true;

    /* Now check for the relativization.
     * First, find the subset of the predecessor_< of the placeholder
     * that satisfies the left clause.
     * Second: utilize a pred_check() method to further tighten the
     * placeholder in order that the entire predecessor does satisfy
     * the relativization formaula.  */
    /* First step */
    DBMList placeholder2_predecessor(placeholder2);
    placeholder2_predecessor.pre();
    // pred Closure makes sure that the exact valuation for the placeholder
    // is excluded.
    placeholder2_predecessor.predClosureRev();
    placeholder2_predecessor.cf();
    /* At this point, placeholder2_predecessor is the time predecessor_{<} of
     * the placeholders that satisfy phi_2, the right hand formula */

    /* We find all the times that satisfy phi_1, and then intersect it
     * with the time predecessor of the phi_2 placeholders. */
    DBMList placeholder1(*INFTYDBM);
    // Since invariants are past closed, we do not need to intersect
    // this placeholder with the invariant.
    do_proof_place(discrete_state, zone_succ, &placeholder1, *formula.getLeft());
    /* Second step: tighten and check the predecessor */
    // Must check for emptiness to handle the corner case when it is empty

    cpplog(cpplogging::debug)
        << "----() Placeholder of times where \\phi_1 is true----- {"
        << placeholder1 << "} ----" << std::endl
        << std::endl;

    // This provides a preliminary check.
    // If the left hand side and right hand side never hold at the same time, we
    // only need to check whether the right hand side holds immediately
    DBMList placeholder1_intersect_placeholder2_pred(placeholder1);
    placeholder1_intersect_placeholder2_pred.intersect(placeholder2_predecessor);
    placeholder1_intersect_placeholder2_pred.cf();
    if (placeholder1_intersect_placeholder2_pred.emptiness()) {
      if (cpplogEnabled(cpplogging::debug)) {
        print_sequentCheck(
            cpplogGet(cpplogging::debug), step - 1, false, zone_succ,
            placeholder1_intersect_placeholder2_pred, discrete_state, formula.getOpType());
        cpplog(cpplogging::debug)
            << "----() Empty Second Placeholder: Relativization Formula "
               "\\phi_1 is never true-----"
            << std::endl
            << std::endl;
      }

      /* Now determine if $\phi_2$ is true without a time elapse.
       * If so, make a non-empty placeholder. In this case, the third
       * Check will be true by default and can be skipped.
       * Else, return empty and break */
      placeholder2.intersect(zone); // zone here is before the time elapse
      placeholder2.cf();
      if (placeholder2.emptiness()) {
        retVal = false;
        cpplog(cpplogging::debug)
            << "----(Invalid) Time Elapsed required for formula to be true; "
               "hence, relativized formula cannot always be false."
            << std::endl
            << std::endl;
      } else {
        /* While a time elapse is not required, the placeholder
         * must span all of zone */
        retVal = placeholder2 >= zone;

        if (retVal) {
          cpplog(cpplogging::debug)
              << "----(Valid) Time Elapse not required and placeholder spans "
                 "zone; hence, formula is true-----"
              << std::endl;
        } else {
          cpplog(cpplogging::debug)
              << "----(Invalid) While Time Elapse not required, placeholder is "
                 "not large enough-----"
              << std::endl;
        }
        cpplog(cpplogging::debug) << "----With resulting Placeholder := {"
                                  << placeholder2 << "} ----" << std::endl
                                  << std::endl;
      }
    } else {
      // There are locations where both left-hand side and right-hand side hold.
      // we therefore need to check the side-conditions
      DBMList placeholder(placeholder1); // tightened placeholder for the
                                         // result; copy since placeholder1 is
                                         // used in the predCheckRule
                                         // computation
      /*--- PredCheck code----*/
      predCheckRule(&placeholder, zone, &zone_succ, &placeholder1, &placeholder2,
                    &placeholder2_predecessor);
      if (placeholder.emptiness()) {
        retVal = false;

        cpplog(cpplogging::debug)
            << "----(Invalid) Relativization placeholder failed-----"
            << std::endl
            << "----With resulting Placeholder := {" << placeholder << "} ----"
            << std::endl
            << std::endl;
      } else {
        // if it is nonempty, it passes the second check and we continue

        if (cpplogEnabled(cpplogging::debug)) {
          print_sequent_place(std::cerr, step - 1, retVal, zone_succ,
                              placeholder2_predecessor, *formula.getLeft(),
                              discrete_state, formula.getOpType());
          cpplog(cpplogging::debug) << "----(Valid) Relativization Placeholder "
                                       "Check Passed (Check Only)-----"
                                    << std::endl
                                    << "----With resulting Placeholder := {"
                                    << placeholder << "} ----" << std::endl
                                    << std::endl;
        }

        // Allow for the possibility of the time instant after the elapse
        placeholder.closure();
        /* Extract the new refined placeholder. */
        placeholder.intersect(placeholder2);
        placeholder.cf();

        /* Now check that it works. */
        placeholder.pre();
        /* This cf() is needed. */
        placeholder.cf();
        retVal = placeholder >= zone;

        if (cpplogEnabled(cpplogging::debug)) {
          print_sequentCheck(cpplogGet(cpplogging::debug), step - 1, retVal, zone,
                             placeholder, discrete_state, formula.getOpType());
          if (retVal) {
            cpplog(cpplogging::debug)
                << "----(Valid) Last Placeholder Check Passed (Check Only)-----"
                << std::endl
                << "----With Placeholder := {" << placeholder << "} ----"
                << std::endl
                << std::endl;

          } else {
            cpplog(cpplogging::debug)
                << "----(Invalid) Last Placeholder Check Failed-----" << std::endl
                << std::endl;
          }
        }
      }
    }
  }

  return retVal;
}

inline bool prover::do_proof_allact(const SubstList& discrete_state,
                                    const DBM& zone, const ExprNode& formula) {
  bool retVal = true;
  /* Enumerate through all transitions */
  cpplog(cpplogging::debug) << "\t Proving ALLACT Transitions:----\n"
                            << std::endl;

  for (std::vector<Transition*>::const_iterator it =
           input_pes.transitions().begin();
       it != input_pes.transitions().end(); ++it) {
    Transition* transition = *it;
    /* Obtain the entire ExprNode and prove it */
    DBM tempLHS(zone);

    bool guard_satisfied =
        comp_ph(&tempLHS, *(transition->getLeftExpr()), discrete_state);
    if (!guard_satisfied) {
      cpplog(cpplogging::debug)
          << "Transition: " << transition << " cannot be taken." << std::endl;
      continue;
    }

    /* Now check the invariant; if the invariant is satisfiable, we update the
       left hand side to be the part of the left hand side that satisfies the
       location invariant. */
    DBM invariant_region(*INFTYDBM);
    const SubstList* source_location = transition->getEnteringLocation(&discrete_state);
    bool invariant_satisfiable = restrict_to_invariant(
        input_pes.invariants(), &invariant_region, *source_location);
    delete source_location;

    if (invariant_satisfiable) {
      invariant_region.cf();
      // Some clocks are reset on this transition
      const ClockSet* reset_clocks = transition->getCSet();
      if (reset_clocks != nullptr) {
        invariant_region.preset(reset_clocks);
      }
      invariant_region.cf();
      /* Now perform clock assignments sequentially: perform the
       * front assignments first */
      const std::vector<std::pair<short int, short int>>* clock_assignments =
          transition->getAssignmentVector();
      if (clock_assignments != nullptr) {
        // Iterate over the vector and print it
        for (std::vector<std::pair<short int, short int>>::const_iterator it =
                 clock_assignments->begin();
             it != clock_assignments->end(); it++) {
          invariant_region.preset((*it).first, (*it).second);
          invariant_region.cf();
        }
      }

      tempLHS.intersect(invariant_region);
      tempLHS.cf();
      if (tempLHS.emptiness()) {
        cpplog(cpplogging::debug)
            << "Transition: " << transition
            << " cannot be taken; entering invariant is false." << std::endl
            << "\tExtra invariant condition: " << invariant_region << std::endl;
        continue;
      }
    }

    transition->getNewTrans(formula.getQuant());

    /* Constraints are bounded by input_pes.max_constant() */
    /* This is to extend the LHS to make sure that
     * the RHS is satisfied by any zone that satisfies
     * the LHS by expanding the zone so it contains
     * all the proper regions where the clocks
     * exceed a certain constant value. */
    tempLHS.cf();
    tempLHS.bound(input_pes.max_constant());
    tempLHS.cf();

    cpplog(cpplogging::debug)
        << "Executing transition (with destination) " << transition << std::endl
        << "\tExtra invariant condition: " << invariant_region << std::endl;

    numLocations++;
    retVal = do_proof(discrete_state, tempLHS, *transition->getRightExpr());
    if (!retVal) {
      cpplog(cpplogging::debug)
          << "Trainsition: " << transition << std::endl
          << "\tinvalidates property and breaks transition executions. "
          << std::endl;

      break;
    }
  }
  cpplog(cpplogging::debug) << "\t --- end of ALLACT." << std::endl;
  return retVal;
}

inline bool prover::do_proof_existact(const SubstList& discrete_state,
                                      const DBM& zone,
                                      const ExprNode& formula) {
  bool retVal = false;
  /* Enumerate through all transitions */

  cpplog(cpplogging::debug) << "\t Proving EXISTACT Transitions:----\n"
                            << std::endl;

  /* Use placeholders to split rules */
  DBMList* partialPlace = nullptr;
  for (std::vector<Transition*>::const_iterator it =
           input_pes.transitions().begin();
       it != input_pes.transitions().end(); it++) {
    Transition* transition = *it;

    /* Obtain the entire ExprNode and prove it */

    // Make a similar comp function for exists so
    // because the entire zone must be able to transition
    // or split by placeholders
    DBMList tempPlace(*INFTYDBM);
    DBM tempLHS(zone);
    bool guard_satisfied = comp_ph_exist_place(
        &tempLHS, &tempPlace, *(transition->getLeftExpr()), discrete_state);
    if (!guard_satisfied) {
      cpplog(cpplogging::debug)
          << "Transition: " << transition << " cannot be taken." << std::endl;
      continue;
    }

    /* Now check the invariant */
    DBM invariant_region(*INFTYDBM);
    const SubstList* source_location = transition->getEnteringLocation(&discrete_state);
    bool invariant_satisfiable = restrict_to_invariant(
        input_pes.invariants(), &invariant_region, *source_location);
    delete source_location;
    if (invariant_satisfiable) {
      invariant_region.cf();
      const ClockSet* reset_clocks = transition->getCSet();
      if (reset_clocks != nullptr) {
        invariant_region.preset(reset_clocks);
      }
      invariant_region.cf();
      /* Now perform clock assignments sequentially: perform the
       * front assignments first */
      const std::vector<std::pair<short int, short int>>* clock_assignments =
          transition->getAssignmentVector();
      if (clock_assignments != nullptr) {
        for (std::vector<std::pair<short int, short int>>::const_iterator it =
                 clock_assignments->begin();
             it != clock_assignments->end(); it++) {
          invariant_region.preset((*it).first, (*it).second);
          invariant_region.cf();
        }
      }

      /* Check if invariant preset is satisfied by the zone.
       * If not, tighten the placeholder */
      if (!(tempLHS <= invariant_region)) {
        // for performance reasons, also tighten the left hand side
        tempPlace.intersect(invariant_region);
        tempPlace.cf();
        if (tempPlace.emptiness()) {
          cpplog(cpplogging::debug)
              << "Transition: " << transition
              << " cannot be taken; entering invariant is false." << std::endl
              << "\tExtra invariant condition: " << invariant_region
              << std::endl;

          continue;
        }
        tempLHS.intersect(invariant_region);
        tempLHS.cf();
      }
    }

    transition->getNewTrans(formula.getQuant());
    /* Constraints are bounded by input_pes.max_constant() */
    /* This is to extend the LHS to make sure that
     * the RHS is satisfied by any zone that satisfies
     * the LHS by expanding the zone so it contains
     * all the proper regions where the clocks
     * exceed a certain constant value. */

    tempLHS.bound(input_pes.max_constant());
    tempLHS.cf();
    // Above placeholder restricted to satisfy incoming invariant

    cpplog(cpplogging::debug) << "Executing transition (with destination) "
                              << transition << std::endl;
    numLocations++;
    do_proof_place(discrete_state, tempLHS, &tempPlace,
                                 *transition->getRightExpr());

    // Reset place parent to NULL
    parentPlaceRef = nullptr;
    if (!tempPlace.emptiness()) {
      // At least a partial solution for the existence of a transition was found
      if (tempPlace >= zone) {
        // This transition covers the entire left hand side, we're done.
        retVal = true;
        break;
      } else if (partialPlace == nullptr) {
        // No partial solution yet, create one.
        partialPlace = new DBMList(tempPlace);
      } else {
        // Add partial solution.
        partialPlace->addDBMList(tempPlace);
      }
    }
  }

  if (!retVal && partialPlace != nullptr) {
    /* Here compare to make sure our partial placeholders are enough */
    retVal = (*partialPlace >= zone);
  }

  // clean up memory if needed.
  delete partialPlace;

  cpplog(cpplogging::debug) << "\t --- end of EXISTACT." << std::endl;

  return retVal;
}

inline bool prover::do_proof_imply(const SubstList& discrete_state,
                                   const DBM& zone, const ExprNode& formula) {
  bool retVal = false;
  /* Here is the one call to comp_ph(...) outside of comp_ph(...) */
  DBM tempLHS(zone);
  if (comp_ph(&tempLHS, *(formula.getLeft()), discrete_state)) {
    /* Constraints are bounded by input_pes.max_constant() */
    /* This is to extend the LHS to make sure that
     * the RHS is satisfied by any zone that satisfies
     * the LHS by expanding the zone so it contains
     * all the proper regions where the clocks
     * exceed a certain constant value. */
    tempLHS.cf();
    tempLHS.bound(input_pes.max_constant());
    tempLHS.cf();

    retVal = do_proof(discrete_state, tempLHS, *formula.getRight());
  } else {
    /* The set of states does not satisfy the premises of the IF
     * so thus the proof is true */
    retVal = true;
    cpplog(cpplogging::debug)
        << "---(Valid) Leaf IMPLY Reached, Premise Not Satisfied----"
        << std::endl
        << std::endl;
  }
  return retVal;
}

inline bool prover::do_proof_constraint(const DBM& zone,
                                        const ExprNode& formula) {
  bool retVal = (zone <= *(formula.dbm()));
  cpplog(cpplogging::debug)
      << "---(" << (retVal ? "V" : "Inv")
      << "alid) Leaf DBM (CONSTRAINT) Reached----" << std::endl
      << std::endl;
  return retVal;
}

inline bool prover::do_proof_bool(const ExprNode& formula) {
  bool retVal = (formula.getBool());
  cpplog(cpplogging::debug) << "---(" << (retVal ? "V" : "Inv")
                            << "alid) Leaf BOOL Reached----" << std::endl
                            << std::endl;
  return retVal;
}

inline bool prover::do_proof_atomic(const SubstList& discrete_state,
                                    const ExprNode& formula) {
  bool retVal = (discrete_state.at(formula.getAtomic()) == formula.getIntVal());
  cpplog(cpplogging::debug) << "---(" << (retVal ? "V" : "Inv")
                            << "alid) Leaf ATOMIC == Reached----" << std::endl
                            << std::endl;
  return retVal;
}

inline bool prover::do_proof_atomic_not(const SubstList& discrete_state,
                                        const ExprNode& formula) {
  bool retVal = (discrete_state.at(formula.getAtomic()) != formula.getIntVal());
  cpplog(cpplogging::debug) << "---(" << (retVal ? "V" : "Inv")
                            << "alid) Leaf ATOMIC != Reached----" << std::endl
                            << std::endl;
  return retVal;
}

inline bool prover::do_proof_atomic_lt(const SubstList& discrete_state,
                                       const ExprNode& formula) {
  bool retVal = (discrete_state.at(formula.getAtomic()) < formula.getIntVal());
  cpplog(cpplogging::debug) << "---(" << (retVal ? "V" : "Inv")
                            << "alid) Leaf ATOMIC < Reached----" << std::endl
                            << std::endl;
  return retVal;
}

inline bool prover::do_proof_atomic_gt(const SubstList& discrete_state,
                                       const ExprNode& formula) {
  bool retVal = (discrete_state.at(formula.getAtomic()) > formula.getIntVal());
  cpplog(cpplogging::debug) << "---(" << (retVal ? "V" : "Inv")
                            << "alid) Leaf ATOMIC > Reached----" << std::endl
                            << std::endl;
  return retVal;
}

inline bool prover::do_proof_atomic_le(const SubstList& discrete_state,
                                       const ExprNode& formula) {
  bool retVal = (discrete_state.at(formula.getAtomic()) <= formula.getIntVal());
  cpplog(cpplogging::debug) << "---(" << (retVal ? "V" : "Inv")
                            << "alid) Leaf ATOMIC < Reached----" << std::endl
                            << std::endl;
  return retVal;
}

inline bool prover::do_proof_atomic_ge(const SubstList& discrete_state,
                                       const ExprNode& formula) {
  bool retVal = (discrete_state.at(formula.getAtomic()) >= formula.getIntVal());
  cpplog(cpplogging::debug) << "---(" << (retVal ? "V" : "Inv")
                            << "alid) Leaf ATOMIC > Reached----" << std::endl
                            << std::endl;
  return retVal;
}

inline bool prover::do_proof_sublist(const SubstList& discrete_state,
                                     const DBM& zone, const ExprNode& formula) {
  SubstList st(formula.getSublist(), &discrete_state);
  return do_proof(st, zone, *formula.getExpr());
}

inline bool prover::do_proof_reset(const SubstList& discrete_state,
                                   const DBM& zone, const ExprNode& formula) {
  DBM lhs_reset(zone);
  lhs_reset.reset(formula.getClockSet());
  lhs_reset.cf();
  return do_proof(discrete_state, lhs_reset, *formula.getExpr());
}

inline bool prover::do_proof_assign(const SubstList& discrete_state,
                                    const DBM& zone, const ExprNode& formula) {
  DBM lhs_assign(zone);
  /* Here the DBM zone is where the value of
   * clock x is reset to clock y, which is possibly
   * a constant or a value*/
  lhs_assign.reset(formula.getcX(), formula.getcY());
  lhs_assign.cf();
  return do_proof(discrete_state, lhs_assign, *formula.getExpr());
}

inline bool prover::do_proof_replace(const SubstList& discrete_state,
                                     const DBM& zone, const ExprNode& formula) {
  SubstList sub_(discrete_state);
  sub_[formula.getcX()] = discrete_state.at(formula.getcY());
  return do_proof(sub_, zone, *formula.getExpr());
}

inline bool prover::do_proof_ablewaitinf(const SubstList& discrete_state,
                                         const DBM& zone) {
  DBM ph(zone);
  ph.suc();
  restrict_to_invariant(input_pes.invariants(), &ph, discrete_state);
  ph.cf();
  /* Time can diverge if and only if there are no upper bound
   * constraints in the successor */
  bool retVal = !ph.hasUpperConstraint();
  cpplog(cpplogging::debug)
      << "---(" << (retVal ? "V" : "Inv") << "alid) Time "
      << (retVal ? "" : "un")
      << "able to diverge to INFTY in current location----" << std::endl
      << std::endl;

  return retVal;
}

// FIXME: eliminate duplication with do_proof_ablewaitinf
inline bool prover::do_proof_unablewaitinf(const SubstList& discrete_state,
                                           const DBM& zone) {
  DBM ph(zone);
  ph.suc();
  restrict_to_invariant(input_pes.invariants(), &ph, discrete_state);
  ph.cf();
  /* Time cannot diverge if and only if there is an upper bound
   * constraint in the successor */
  bool retVal = ph.hasUpperConstraint();
  cpplog(cpplogging::debug)
      << "---(" << (retVal ? "V" : "Inv") << "alid) Time "
      << (retVal ? "un" : "")
      << "able to diverge to INFTY in current location----" << std::endl
      << std::endl;
  return retVal;
}

/* IMPLEMENTATION PROVER WITH PLACEHOLDERS */
inline void prover::do_proof_place_predicate(const SubstList& discrete_state,
                                                 const DBM& zone,
                                                 DBMList* place,
                                                 const ExprNode& formula) {
  ExprNode* e = input_pes.lookup_equation(formula.getPredicate());

  // Get Predicate Index for Hashing
  int predicate_index =
      input_pes.lookup_predicate(formula.getPredicate())->getIntVal() - 1;
  prevParityGfp = currParityGfp;
  currParityGfp = formula.get_Parity();
  place->cf();

  /* First look in known true and false sequent tables */
  if (useCaching) {
    { // restricted block for known false sequents
      /* First look in known False Sequent tables.
       * Note: The False sequents with placeholders do not
       * need to store placeholders. */
      SequentPlace* cached_sequent =
          cache.Xlist_false_ph.look_for_sequent(&discrete_state, predicate_index);
      if (cached_sequent != nullptr &&
          cached_sequent->tabled_false_sequent(zone)) {
        // Found known false
        place->makeEmpty();
        cpplog(cpplogging::debug)
            << "---(Invalid) Located a Known False Sequent ----" << std::endl
            << std::endl;

        /* Update backpointers to add possible pointer for parent
         * This is a bit conservative */
        /* Now that we have a proven sequent, add the backpointer
         * from the child to the parent */
        if (parentPlaceRef != nullptr) {
          cached_sequent->addParent(parentPlaceRef);
        } else { // Parent is regular sequent
          cached_sequent->addParent(parentRef);
        }
        return;
      }
    }

    /* Next look in known True Sequent tables. */
    { // restricted block for known true sequents
      SequentPlace* cached_sequent =
          cache.Xlist_true_ph.look_for_sequent(&discrete_state, predicate_index);
      DBMList cached_placeholder(*INFTYDBM);
      /* Note: tempPlace is changed by tabled_sequentPlace() */
      if (cached_sequent != nullptr &&
          cached_sequent->tabled_sequent(zone, &cached_placeholder)) {
        // Found known true
        *place = cached_placeholder;
        if (cached_placeholder.emptiness()) {
          // returning placeholder must be non-empty for the sequent
          // to be valid
          return;
        }
        // Note: we intersect the current found placeholder
        // with the placeholder stored in the sequent.

        cpplog(cpplogging::debug)
            << "---(Valid) Located a Known True Sequent ----" << std::endl
            << std::endl;

        /* Update backpointers to add possible pointer for parent
         * This is a bit conservative */
        /* Now that we have a proven sequent, add the backpointer
         * in the cache from the child to the parent */
        if (parentPlaceRef != nullptr) {
          cached_sequent->addParent(parentPlaceRef);
        } else { // Parent is regular sequent
          cached_sequent->addParent(parentRef);
        }
        return;
      }
    }
  }

  /* Now deal with greatest fixpoint and least fixpoint circularity */
  SequentPlace* h = nullptr;
  { // Restricted scope for detecting circularities
    SequentPlace* t = new SequentPlace(&formula, &discrete_state);
    if (currParityGfp) { // Thus a Greatest Fixpoint
      /* Already looked in known false so no need to do so */
      h = cache.Xlist_pGFP_ph.locate_sequent(t, predicate_index);
      if (!newSequent && h->tabled_sequent_gfp(zone, place)) {
        // Found gfp Circularity - thus valid
        cpplog(cpplogging::debug)
            << "---(Valid) Located True Sequent or gfp Circularity ----"
            << std::endl
            << std::endl;

        /* Now update backpointer for greatest fixpoint circularity */
        if (parentPlaceRef != nullptr) {
          h->addParent(parentPlaceRef);
        } else { // Parent is regular sequent
          h->addParent(parentRef);
        }

        // Add sequent to known true cache
        if (useCaching) {
          SequentPlace* true_sequent = new SequentPlace(&formula, &discrete_state);
          SequentPlace* cached_true_sequent =
              cache.Xlist_true_ph.locate_sequent(true_sequent, predicate_index);
          cached_true_sequent->update_sequent(zone, place);
        }
        return;
      }

      h->push_sequent(std::make_pair(new DBM(zone), new DBMList(*place)));
    } else { // Thus, a least fixpoint
      // Now look in lfp circularity cache
      h = cache.Xlist_pLFP_ph.locate_sequent(t, predicate_index);
      if (!newSequent && h->tabled_sequent_lfp(zone, place)) {
        // Found lfp circularity - thus invalid
        place->makeEmpty();

        cpplog(cpplogging::debug)
            << "---(Invalid) Located lfp Circularity ----" << std::endl
            << std::endl;

        /* Now update backpointer for least fixpoint circularity */
        if (parentPlaceRef != nullptr) {
          h->addParent(parentPlaceRef);
        } else { // Parent is regular sequent
          h->addParent(parentRef);
        }

        // Now Put Sequent in False Cache
        if (useCaching) {
          SequentPlace* false_sequent = new SequentPlace(&formula, &discrete_state);
          SequentPlace* cached_false_sequent =
              cache.Xlist_false_ph.locate_sequent(false_sequent,
                                                  predicate_index);
          cached_false_sequent->update_false_sequent(zone);
        }
        return;
      }

      h->push_sequent(std::make_pair(new DBM(zone), new DBMList(*place)));
    }
  } // End scope for circularity

  assert(h != nullptr);
  // no least/greatest fixed point circularity was found; the sequent has been
  // added to the appropriate cache

  // NO CIRCULARITY FOUND

  /* Assign parent value after caching since during caching we may have
   * to use the previous parent */
  SequentPlace* tempParentPlace = parentPlaceRef;
  /* Get the current variable */
  parentPlaceRef = h;

  do_proof_place(discrete_state, zone, place, *e);

  /* Now update the parent so it points to the previous parent, and not this
   * predicate */
  parentPlaceRef = tempParentPlace;

  h->pop_sequent(); // XXX Why do this at a different place than in the
                    // non-placeholder case? (JK)
  // ds might be empty, but we leave it in

  // Now Purge updated premise
  place->cf();

  /* Key Concept of Purging:
   * If Was True, discovered false, check that
   *		Z_now_false <= Z_cached_true | or | Z_cached_true >= Z_now_false
   * If Was False, discovered true, check that
   *		Z_now_true >= Z_cached_false | or | Z_cached_false <= Z_now_true
   * This Must be done regardless of how the tabling
   * is done for that specific cache */
  if (useCaching) {
    if (!place->emptiness()) {
      /* First look in opposite parity Caches */
      bool madeEmpty = false;
      SequentPlace* true_sequent = new SequentPlace(&formula, &discrete_state);
      SequentPlace* cached_false_sequent =
          cache.Xlist_false_ph.look_for_and_purge_rhs_sequent(
              std::make_pair(&zone, place), true_sequent, predicate_index, false,
              &madeEmpty);

      /* Now purge backpointers */
      if (cached_false_sequent != nullptr) {
        cache.look_for_and_purge_rhs_backStack(
            cached_false_sequent->parents(),
            cached_false_sequent->parents_with_placeholders());
        // Delete t2s later to prevent double deletion
      }

      // Now update in proper Cache
      SequentPlace* cached_true_sequent =
          cache.Xlist_true_ph.locate_sequent(true_sequent, predicate_index);
      cached_true_sequent->update_sequent(zone, place);

      // this delete is necessary for memory management but problematic
      if (madeEmpty) {
        delete cached_false_sequent;
      }
    } else {
      /* place is empty */
      /* First look in opposite parity Cache */
      // Now look in placeholder caches
      bool madeEmpty = false;
      SequentPlace* false_sequent = new SequentPlace(&formula, &discrete_state);
      SequentPlace* cached_true_sequent =
          cache.Xlist_true_ph.look_for_and_purge_rhs_sequent(
              std::make_pair(&zone, place), false_sequent, predicate_index, true,
              &madeEmpty);

      /* Now purge backpointers.
       * Ignore circularity booleans because they do not form backpointers */
      if (cached_true_sequent != nullptr) {
        cache.look_for_and_purge_rhs_backStack(
            cached_true_sequent->parents(),
            cached_true_sequent->parents_with_placeholders());
      }

      // Now update in proper Cache
      SequentPlace* cached_false_sequent =
          cache.Xlist_false_ph.locate_sequent(false_sequent, predicate_index);
      cached_false_sequent->update_false_sequent(zone);

      // This delete is necessary for memory management but problematic
      if (madeEmpty) {
        delete cached_true_sequent;
      }
    }
  }
}

inline void prover::do_proof_place_and(const SubstList& discrete_state,
                                           const DBM& zone, DBMList* place,
                                           const ExprNode& formula) {
  DBMList placeholder_right(*place);
  do_proof_place(discrete_state, zone, place, *formula.getLeft());
  place->cf();
  if (!place->emptiness()) {
    placeholder_right.intersect(*place);
    do_proof_place(discrete_state, zone, &placeholder_right, *formula.getRight());
    place->intersect(placeholder_right);
  }
}

// [FC14] Proof rule \lor_{s2}
inline void prover::do_proof_place_or(const SubstList& discrete_state,
                                          const DBM& zone, DBMList* place,
                                          const ExprNode& formula) {
  place->cf();
  DBMList placeholder_left(*place); // FIXME: why initialise with *place here?

  do_proof_place(discrete_state, zone, &placeholder_left, *formula.getLeft());
  placeholder_left.cf();

  // Now do the right proof, and take the right if its placeholder is
  // larger that from the left side.
  if (!placeholder_left.emptiness() &&
      placeholder_left >=
          *place) { // why compare to *place; it seems this should be zone
    /* Here, the current transition successful;
     * we are done */
    *place = placeholder_left;
    return;
  }

  // We use place here, since the result of the second call is likely to be
  // part of the result anyway. If not, we will roll back later.
  // *place is thus placeholder_right.
  do_proof_place(discrete_state, zone, place, *formula.getRight());
  place->cf();

  if (cpplogEnabled(cpplogging::debug)) {
    // Check Debugging Here to make sure it is giving the right output
    print_sequentCheck(cpplogGet(cpplogging::debug), step - 1, false, zone,
                       placeholder_left, discrete_state, formula.getOpType());
    cpplog(cpplogging::debug)
        << "Left Placeholder of OR (P): " << placeholder_left
        << "\nRight Placeholder of OR (P): " << *place << std::endl;
  }

  /* Note: <= >= Not clearly working if empty DBMs; should be resolved in the
   *  implementation of <=; */
  if (placeholder_left.emptiness() || placeholder_left <= *place) {
    // the result is the right placeholder. Already established.
  } else if (place->emptiness() || *place <= placeholder_left) {
    *place = placeholder_left; // roll back
  } else {
    // corner case, union of DBMs
    place->addDBMList(placeholder_left);
  }

  cpplog(cpplogging::debug)
      << "Final Placeholder of OR (P): " << *place << std::endl
      << std::endl;
}

inline void prover::do_proof_place_or_simple(const SubstList& discrete_state,
                                                 const DBM& zone,
                                                 DBMList* place,
                                                 const ExprNode& formula) {
  /* In OR_SIMPLE, the placeholder will either be empty or completely full
   * in one of the two cases. Hence, fewer comparisons with unions of zones
   * are needed. */
  place->cf();
  DBMList placeholder_left(*place);
  do_proof_place(discrete_state, zone, &placeholder_left, *formula.getLeft());
  placeholder_left.cf();

  // Now do the right proof, and take the right if its placeholder is
  // larger that from the left side.
  if (!placeholder_left.emptiness() && (placeholder_left >= *place)) {
    /* Here, the current transition successful;
     * we are done */
    *place = placeholder_left;
    return;
  }

  // We anticipate the right placeholder is the correct result here.
  // if not, we roll back later.
  do_proof_place(discrete_state, zone, place, *formula.getRight());
  place->cf();

  /* If the left is simple, then we have an empty left or
   * left is the entire placeholder. */

  if (!placeholder_left.emptiness() && place->emptiness()) {
    // Take previous DBM
    *place = placeholder_left;
  }

  /* If both are non-empty then the left is not the
   * entire placeholder. Hence, the left was not the simple
   * disjunct. Therefore, the right must be the simple disjunct
   * and must be the entire placeholder. */
}

// [FC14] Proof rule \forall_{t2}
inline void prover::do_proof_place_forall(const SubstList& discrete_state,
                                              const DBM& zone,
                                              DBMList* place,
                                              const ExprNode& formula) {
  /* Here the model checker looks at the zone of
   * all time sucessors and then substitutes in
   * the substitued constraints and sees if the
   * zone satifies the constraints */
  DBM lhs_succ(zone);
  lhs_succ.suc();

  /* Per proof rules with the placeholder,
   * do not incorporate the invariant into the FORALL here */
  *place = *INFTYDBM;

  do_proof_place(discrete_state, lhs_succ, place, *formula.getQuant());
  place->cf();

  // must we consider not the invariant even if the placeholder is empty. (?)

  if (!place->emptiness()) { // Only do if a nonempty placeholder
    /* Now do the second proof rule to compute the first placeholder
     */

    DBMList placeholder_forall(*place);
    succCheckRule(&discrete_state, zone, &lhs_succ, place, &placeholder_forall);
    *place = placeholder_forall;

    if (cpplogEnabled(cpplogging::debug)) {
      // Result only used for printing the correct value below.
      bool result = !place->emptiness();
      // This work is done in the succCheck method.
      // Perhaps I should move the debug rule there?
      DBM succLHS(zone);
      succLHS.suc();
      succLHS.cf();
      DBMList succRuleConseq(zone);
      succRuleConseq.intersect(*place);
      succRuleConseq.cf();
      succRuleConseq.suc();
      succRuleConseq.cf();
      print_sequentCheck(cpplogGet(cpplogging::debug), step - 1, result,
                         succLHS, succRuleConseq, discrete_state, formula.getOpType());
      if (result) {
        cpplog(cpplogging::debug)
            << "----(Valid) Placeholder Check Passed-----" << std::endl
            << "--With Placeholder := {" << *place << "} ----" << std::endl
            << std::endl;
      } else {
        cpplog(cpplogging::debug)
            << "----(Invalid) Placeholder Check Failed-----" << std::endl
            << std::endl;
      }
    }
  }
}

inline void prover::do_proof_place_forall_rel(const SubstList& discrete_state,
                                                  const DBM& zone,
                                                  DBMList* place,
                                                  const ExprNode& formula) {
  bool retVal = false;
  /* Proof methodology:
   * first, see if \phi_1 is satisfied during the time advance.
   * If it is, check that phi_2 is true both at and before those
   * times (time predecessor).
   * If this is not satisfactory, then do a regular FORALL proof
   * without a placeholder. */

  /* First, see if \exists(phi_1) is true. The common case is that it
   * will not be. */
  /* First try to get a new placeholder value that works */
  DBM lhs_succ(zone);
  lhs_succ.suc();

  DBMList placeholder1(*INFTYDBM);
  restrict_to_invariant(input_pes.invariants(), &placeholder1, discrete_state);
  do_proof_place(discrete_state, lhs_succ, &placeholder1, *formula.getLeft());
  placeholder1.cf();

  if (placeholder1.emptiness()) {
    if (cpplogEnabled(cpplogging::debug)) {
      print_sequentCheck(cpplogGet(cpplogging::debug), step - 1, retVal,
                         lhs_succ, placeholder1, discrete_state, formula.getOpType());
      cpplog(cpplogging::debug) << "--------() Empty Relativization "
                                   "Placeholder: phi1 is never true ----------"
                                << std::endl
                                << std::endl;
    }
    /* Since here, \forall phi_2 computes the entire placeholder */
    /* Here the model checker looks at the zone of
     * all time sucessors and then substitutes in
     * the substitued constraints and sees if the
     * zone satifies the constraints */

    DBMList newPlace(*INFTYDBM);
    do_proof_place(discrete_state, lhs_succ, &newPlace, *formula.getRight());
    newPlace.cf();
    if (!(newPlace.emptiness())) { // Only do if a nonempty placeholder
      /* Now do the second proof rule to compute the first placeholder
       */

      DBMList currPlace(newPlace);
      succCheckRule(&discrete_state, zone, &lhs_succ, &currPlace, &newPlace);

      retVal = !newPlace.emptiness();
      *place = newPlace;

      if (cpplogEnabled(cpplogging::debug)) {
        // This work is done in the succCheck method.
        // Perhaps I should move the debug rule there?
        DBMList succRuleConseq(zone);
        succRuleConseq.intersect(newPlace);
        succRuleConseq.cf();
        succRuleConseq.suc();
        succRuleConseq.cf();
        print_sequentCheck(cpplogGet(cpplogging::debug), step - 1, retVal,
                           lhs_succ, succRuleConseq, discrete_state, formula.getOpType());
        if (retVal) {
          cpplog(cpplogging::debug)
              << "----(Valid) FORALL (FORALL_REL) Placeholder Check Passed-----"
              << std::endl
              << "--With Placeholder := {" << *place << "} ----"
              << std::endl
              << std::endl;
        } else {
          cpplog(cpplogging::debug) << "----(Invalid) FORALL (FORALL_REL) "
                                       "Placeholder Check Failed-----"
                                    << std::endl
                                    << std::endl;
        }
      }
    }
  } else if (placeholder1 == *INFTYDBM) {
  // First check for the simplest case: no time elapse is needed
  /* Perhaps we can reduce *INFTYDBM to be *place
   * given the proof rules. */

    if (cpplogEnabled(cpplogging::debug)) {
      print_sequentCheck(cpplogGet(cpplogging::debug), step - 1, retVal, zone,
                         placeholder1, discrete_state, formula.getOpType());
      cpplog(cpplogging::debug)
          << "----(Valid) EXISTS (in FORALL_REL) Placeholder indicates no "
             "time elapse is needed (Check Only)-----"
          << std::endl
          << "----With Placeholder := {" << placeholder1 << "} ----"
          << std::endl
          << std::endl;
    }

    // If here, we neither need a placeholder nor to elapse time
    DBMList infPlace(*INFTYDBM);
    do_proof_place(discrete_state, zone, &infPlace, *formula.getRight());
    infPlace.cf();
    if (!(infPlace.emptiness())) { // Only do if a nonempty placeholder
      /* Now do the second proof rule to compute the first placeholder */
      retVal = true;

      if (cpplogEnabled(cpplogging::debug)) {
        print_sequentCheck(cpplogGet(cpplogging::debug), step - 1, retVal,
                           zone, infPlace, discrete_state, formula.getOpType());
        cpplog(cpplogging::debug)
            << "----(Valid) Placeholder Check Passed-----" << std::endl
            << "--With Placeholder := {" << infPlace << "} ----"
            << std::endl
            << std::endl;
      }
    }
    *place = infPlace;

  } else {
    // This is the more complicated case that requires a placeholder
    // for the FORALL
    /* Now check that we can elapse to the placeholder. */
    // Store the set of times that satisfy phi1

    cpplog(cpplogging::debug)
        << "----() Relativization \\phi_1 placeholder obtained as {"
        << placeholder1 << "} ----" << std::endl
        << std::endl;

    /* We omit the check that we can elapse to the placeholder;
     * We will check that once at the end */
    DBMList placeholder2(*INFTYDBM);
    do_proof_place(discrete_state, lhs_succ, &placeholder2, *formula.getRight());
    placeholder2.cf();

    cpplog(cpplogging::debug)
        << "----() Formula \\phi_2 placeholder obtained as {" << placeholder2
        << "} ----" << std::endl
        << std::endl;

    // Reset place parent to nullptr
    parentPlaceRef = nullptr;

    if (placeholder2.emptiness()) {
      retVal = false;
      *place = placeholder2;
    } else if (placeholder2 >= lhs_succ) {
      /* In this simple case, all possible times satisfy \phi_2
       * so we can avoid many checks. */
      retVal = true;
      *place = placeholder2;
    } else {
      /* Now do a succ check on phi_2 to get \phi_forall
       * and a predCheck using both phi_1 and phi_2 to get phi_exists */
      /* we also note that the times satisfying \phi_1
       * (the relativization formula condition) are neither empty
       * nor everything. */

      DBMList forallPlace(placeholder2);
      succCheckRule(&discrete_state, zone, &lhs_succ, &placeholder2, &forallPlace);
      forallPlace.cf();

      if (cpplogEnabled(cpplogging::debug)) {
        print_sequentCheck(cpplogGet(cpplogging::debug), step - 1, retVal,
                           lhs_succ, placeholder2, discrete_state, formula.getOpType());
        cpplog(cpplogging::debug)
            << "----() FORALL (of FORALL_REL) Placeholder Check obtained  FA "
               "Placeholder := {"
            << forallPlace << "} ----" << std::endl
            << std::endl;
      }

      /* Now we do the pred check to find the exists placeholder;
       * This involves the predCheck method and checking that time can
       * can elapse. Note that the exists is a simplified version
       * where \phi_2 (the right) is the relativized clause and
       * \phi_1 (the left) is the formula. By using the placeholders
       * computed previously, we save time by not having to recompute
       * the formulas. */
      DBMList phi1PredPlace(placeholder1);
      phi1PredPlace.pre();
      phi1PredPlace.cf();
      /*--- PredCheck code----*/
      predCheckRule(&placeholder2, zone, &lhs_succ, &placeholder2, &placeholder1,
                    &phi1PredPlace);
      placeholder2.cf();

      cpplog(cpplogging::debug)
          << "----() FORALL Rel Exists placeholder obtained as := {"
          << placeholder2 << "} ----" << std::endl
          << std::endl;

      if (!placeholder2.emptiness()) {
        /* if it is nonempty, it passes the second check and we continue
         * Given the FORALL rule rewrite, do not allow the instance
         * after the time elapse. */
        /* Extract the new refined placeholder. */
        placeholder2.intersect(placeholder1);
        placeholder2.cf();

        /* Now check that it works. */
        /* Since we are not using retPlace anymore, we do not
         * need to copy it for the check. */
        placeholder2.pre();
        /* This cf() is needed. */
        placeholder2.cf();
        // check elapse further?

        if (cpplogEnabled(cpplogging::debug)) {
          print_sequentCheck(cpplogGet(cpplogging::debug), step - 1, retVal,
                             zone, placeholder2, discrete_state, formula.getOpType());
          cpplog(cpplogging::debug) << "----() FORALL Rel Exists placeholder "
                                       "after time elapse check is := {"
                                    << placeholder2 << "} ----" << std::endl
                                    << std::endl;
        }
      }
      /* Last, we do an "or" check on the two placeholders */
      bool forallEmpty = forallPlace.emptiness();
      bool existsEmpty = placeholder2.emptiness();
      retVal = true;
      if (forallEmpty && existsEmpty) {
        place->makeEmpty();
        retVal = false;
      } else if (forallEmpty) {
        *place = placeholder2;
      } else if (existsEmpty) {
        *place = forallPlace;
      } else if (forallPlace <= placeholder2) {
        *place = placeholder2;
      } else if (placeholder2 <= forallPlace) {
        *place = forallPlace;
      } else {
        *place = placeholder2;
        /* This case requires us to union the two placeholders. */
        place->addDBMList(forallPlace);
      }
    }

    cpplog(cpplogging::debug)
        << "Final Placeholder of FORALL_REL (P): " << *place
        << std::endl
        << std::endl;
  }
}

inline void prover::do_proof_place_exists(const SubstList& discrete_state,
                                              const DBM& zone,
                                              DBMList* place,
                                              const ExprNode& formula) {
  /* First try to get a new placeholder value that works */
  place->cf();
  DBM lhs_succ(zone);
  lhs_succ.suc();

  // The invariant goes into the placeholder, not the left hand side
  DBMList placeholder(*INFTYDBM);
  restrict_to_invariant(input_pes.invariants(), &placeholder, discrete_state);

  do_proof_place(discrete_state, lhs_succ, &placeholder, *formula.getQuant());
  placeholder.cf();

  if (placeholder.emptiness()) {
    if (cpplogEnabled(cpplogging::debug)) {
      print_sequentCheck(cpplogGet(cpplogging::debug), step - 1, false,
                         lhs_succ, placeholder, discrete_state, formula.getOpType());
      cpplog(cpplogging::debug) << "----(Invalid) Empty First Placeholder: No "
                                   "Need for additional Placeholder Checks-----"
                                << std::endl
                                << std::endl;
    }
    *place = placeholder;
  } else {
    /* Now check that it works (the new placeholder can be
     * obtained from the old
     * For the placeholder rule, we use this check
     * to give us the value of the old placeholder */
    placeholder.pre();
    place->intersect(placeholder);
    place->cf();

    if (cpplogEnabled(cpplogging::debug)) {
      bool result = !place->emptiness();
      print_sequent_placeCheck(std::cerr, step - 1, result, zone, *place, *place,
                               discrete_state, formula.getOpType());
      if (result) {
        cpplog(cpplogging::debug)
            << "----(Valid) Placeholder Check Passed-----" << std::endl
            << "--With Placeholder := {" << *place << "} ----" << std::endl
            << std::endl;
      } else {
        cpplog(cpplogging::debug)
            << "----(Invalid) Placeholder Check Failed-----" << std::endl
            << std::endl;
      }
    }
  }
}

inline void prover::do_proof_place_exists_rel(const SubstList& discrete_state,
                                                  const DBM& zone,
                                                  DBMList* place,
                                                  const ExprNode& formula) {
  /* First Try to get a placeholder value that works */
  place->cf();
  DBM zone_succ(zone);
  zone_succ.suc();

  DBMList placeholder2(*INFTYDBM);
  restrict_to_invariant(input_pes.invariants(), &placeholder2, discrete_state);

  do_proof_place(discrete_state, zone_succ, &placeholder2, *formula.getRight());
  // Reset place parent to nullptr
  parentPlaceRef = nullptr;
  placeholder2.cf();
  if (placeholder2.emptiness()) {
    if (cpplogEnabled(cpplogging::debug)) {
      print_sequentCheck(cpplogGet(cpplogging::debug), step - 1, false, zone,
                         placeholder2, discrete_state, formula.getOpType());
      cpplog(cpplogging::debug) << "----(Invalid) Empty First Placeholder: No "
                                   "Need for additional Placeholder Checks-----"
                                << std::endl
                                << std::endl;
    }
    *place = placeholder2;
  } else {
    /* Now check for the relativization.
     * First, find the subset of the predecessor_< of the placeholder
     * that satisfies the left clause.
     * Second: utilize a pred_check() method to further tighten the
     * placeholder in order that all  */
    /* First step */
    DBMList placeholder2_predecessor(placeholder2);
    placeholder2_predecessor.pre();
    // pred Closure makes sure that the exact valuation for the placeholder
    // is excluded.
    placeholder2_predecessor.predClosureRev();
    placeholder2_predecessor.cf();
    /* At this point, phi2PredPlace is the time predecessor_{<} of the
     * placeholders that satisfy phi_2, the right hand formula */

    /* We find all the times that satisfy phi_1, and then intersect it
     * with the time predecessor of the phi_2 placeholders. */
    DBMList placeholder1(*INFTYDBM);
    do_proof_place(discrete_state, zone_succ, &placeholder1, *formula.getLeft());
    /* Second step: tighten and check the predecessor */
    // Must check for emptiness to handle the corner case when it is empty

    cpplog(cpplogging::debug)
        << "----() Placeholder of times where \\phi_1 is true----- {" << placeholder1
        << "} ----" << std::endl
        << std::endl;

    DBMList placeholder1_intersect_placeholder2_pred(placeholder1);
    placeholder1_intersect_placeholder2_pred.intersect(placeholder2_predecessor);
    placeholder1_intersect_placeholder2_pred.cf();
    if (placeholder1_intersect_placeholder2_pred.emptiness()) {
      *place = placeholder1_intersect_placeholder2_pred;

      if (cpplogEnabled(cpplogging::debug)) {
        print_sequentCheck(cpplogGet(cpplogging::debug), step - 1, false, zone_succ,
                           *place, discrete_state, formula.getOpType());

        cpplog(cpplogging::debug)
            << "----() Empty Second Placeholder: Relativization Formula \\phi_1 "
               "is never true-----"
            << std::endl
            << std::endl;
      }

      /* Now determine if $\phi_2$ is true without a time elapse.
       * If so, make a non-empty placeholder. In this case, the third
       * Check will be true by default and can be skipped.
       * Else, return empty and break */
      placeholder2.intersect(zone); // zone here is before the time elapse
      placeholder2.cf();
      if (placeholder2.emptiness()) {
        cpplog(cpplogging::debug)
            << "----(Invalid) Time Elapsed required for formula to be true; "
               "hence, relativized formula cannot always be false."
            << std::endl
            << std::endl;
      } else {
        /* While a time elapse is not required, the placeholder
         * must span all of zone */
        if (placeholder2 >= zone) {
          cpplog(cpplogging::debug)
              << "----(Valid) Time Elapse not required and placeholder spans "
                 "zone; hence, formula is true-----"
              << std::endl;
        } else {
          cpplog(cpplogging::debug)
              << "----(Invalid) While Time Elapse not required, placeholder is "
                 "not large enough-----"
              << std::endl;
        }
        cpplog(cpplogging::debug) << "----With resulting Placeholder := {"
                                  << placeholder2 << "} ----" << std::endl
                                  << std::endl;
      }
    } else {

      /*--- PredCheck code----*/
      DBMList placeholder(placeholder1);
      predCheckRule(&placeholder, zone, &zone_succ, &placeholder1, &placeholder2,
                    &placeholder2_predecessor);
      if (placeholder.emptiness()) {
        cpplog(cpplogging::debug)
            << "----(Invalid) Relativization placeholder failed-----" << std::endl
            << "----With resulting Placeholder := {" << placeholder << "} ----"
            << std::endl
            << std::endl;

        *place = placeholder;
      }
      else
      {
        // if it is still nonempty, it passes the second check and we continue

        if (cpplogEnabled(cpplogging::debug)) {
          print_sequent_place(std::cerr, step - 1, true, zone_succ, placeholder2_predecessor,
                              *formula.getLeft(), discrete_state, formula.getOpType());
          cpplog(cpplogging::debug) << "----(Valid) Relativization Placeholder Check "
                                       "Passed (Check Only)-----"
                                    << std::endl
                                    << "----With resulting Placeholder := {"
                                    << placeholder << "} ----" << std::endl
                                    << std::endl;
        }


        // Allow for the possibility of the time instant after the elapse
        placeholder.closure();
        /* Extract the new refined placeholder */
        placeholder.intersect(placeholder2);
        placeholder.cf();

        /* Now check that it works (the new placeholder can be
         * obtained from the old
         * For the placeholder rule, we use this check
         * to give us the value of the old placeholder */
        placeholder.pre();
        place->intersect(placeholder);
        place->cf();

        if (cpplogEnabled(cpplogging::debug)) {
          print_sequent_placeCheck(std::cerr, step - 1, !place->emptiness(), zone, *place,
                                   *place, discrete_state, formula.getOpType());
          if (!place->emptiness()) {
            cpplog(cpplogging::debug)
                << "----(Valid) Final Placeholder Check Passed-----" << std::endl
                << "--With Placeholder := {" << *place << "} ----" << std::endl
                << std::endl;
          } else {
            cpplog(cpplogging::debug)
                << "----(Invalid) Final Placeholder Check Failed-----" << std::endl
                << std::endl;
          }
        }
      }
    }
  }
}

inline void prover::do_proof_place_allact(const SubstList& discrete_state,
                                              const DBM& zone,
                                              DBMList* place,
                                              const ExprNode& formula) {
  /* Enumerate through all transitions */
  cpplog(cpplogging::debug) << "\t Proving ALLACT Transitions:----\n"
                            << std::endl;

  /* For reasons to avoid convexity until the end, find all of the
   * placeholders for each clause individually. For all transitions
   * that can be executed, store the resulting placeholders with transitions
   * so that we only need to give a non-convex placeholder when finished */
  std::vector<DBMList*> transition_placeholders;
  bool emptyRetPlace = false;
  for (std::vector<Transition*>::const_iterator it =
           input_pes.transitions().begin();
       it != input_pes.transitions().end(); it++) {
    Transition* transition = *it;

    /* Obtain the entire ExprNode and prove it */
    DBM tempLHS(zone);

    DBMList guard_region(*place);
    bool guard_satisfied =
        comp_ph_all_place(&tempLHS, &guard_region, *(transition->getLeftExpr()),
                          discrete_state);
    if (!guard_satisfied) {
      cpplog(cpplogging::debug)
          << "Transition: " << transition << " cannot be taken." << std::endl;
      continue;
    }
    /* Now guardPlace has the largest placeholder satisfying the
     * guard. Note that we use tempPlace for the proof. guardPlace
     * is used later to restrict the placeholder if needed. */

    /* Now check the invariant */
    DBMList transition_placeholder(*place);
    DBM invariant_region(*INFTYDBM);
    const SubstList* source_location = transition->getEnteringLocation(&discrete_state);
    bool invariant_satisfiable = restrict_to_invariant(input_pes.invariants(),
                                                       &invariant_region,
                                                       *source_location);
    delete source_location;

    if (invariant_satisfiable) {
      invariant_region.cf();
      const ClockSet* reset_clocks = transition->getCSet();
      if (reset_clocks != nullptr) {
        invariant_region.preset(reset_clocks);
      }
      invariant_region.cf();
      /* Now perform clock assignments sequentially: perform the
       * front assignments first */
      const std::vector<std::pair<short int, short int>>* clock_assignments =
          transition->getAssignmentVector();
      if (clock_assignments != nullptr) {
        // Iterate over the vector and print it
        for (std::vector<std::pair<short int, short int>>::const_iterator it =
                 clock_assignments->begin();
             it != clock_assignments->end(); it++) {
          invariant_region.preset((*it).first, (*it).second);
          invariant_region.cf();
        }
      }
      // Now invPlace has the largest placeholder satisfying
      // the invariant

      /* Check if invariant preset is satisfied by the zone.
       * If not, tighten the placeholder */

      if (!(tempLHS <= invariant_region)) {
        tempLHS.intersect(invariant_region);
        tempLHS.cf();
        if (tempLHS.emptiness()) {
          cpplog(cpplogging::debug)
              << "Transition: " << transition
              << " cannot be taken; entering invariant is false." << std::endl
              << "\tExtra invariant condition: " << invariant_region << std::endl;

          continue;
        }
        transition_placeholder.intersect(invariant_region);
        transition_placeholder.cf();
      }
    }

    transition->getNewTrans(formula.getQuant());
    /* Constraints are bounded by input_pes.max_constant() */
    /* This is to extend the LHS to make sure that
     * the RHS is satisfied by any zone that satisfies
     * the LHS by expanding the zone so it contains
     * all the proper regions where the clocks
     * exceed a certain constant value. */
    tempLHS.cf();
    tempLHS.bound(input_pes.max_constant());
    tempLHS.cf();
    // The transition RHS handles resets and substitutions
    cpplog(cpplogging::debug)
        << "Executing transition (with destination) " << transition << std::endl;
    // use phLHS since the zone is tightened to satisfy
    // the invariant
    numLocations++;
    do_proof_place(discrete_state, tempLHS, &transition_placeholder, *transition->getRightExpr());
    transition_placeholder.cf();
    /* Given ALLAct, this segment may require zone unions. */
    if (transition_placeholder.emptiness()) {
      // Code here
      DBMList* newPlace;
      DBMList invList(invariant_region);
      !invList;
      invList.cf();
      !guard_region;
      guard_region.cf();
      // Now combine the placeholders
      bool invEmpty = invList.emptiness();
      bool guardEmpty = guard_region.emptiness();
      if (invEmpty && guardEmpty) {
        // This means that no such placeholder is possible
        transition_placeholder.makeEmpty();
        emptyRetPlace = true;
        break;
      } else if (invEmpty) {
        newPlace = new DBMList(guard_region);
      } else if (guardEmpty) {
        newPlace = new DBMList(invList);
      } else if (invList <= guard_region) {
        newPlace = new DBMList(guard_region);
      } else if (guard_region <= invList) {
        newPlace = new DBMList(invList);
      } else {
        /* This is the bad case, because zone unions are required */
        newPlace = new DBMList(guard_region);
        newPlace->addDBMList(invList);
      }
      transition_placeholders.push_back(newPlace);
      continue;
    }
    DBMList tempPlace(transition_placeholder);
    tempPlace.intersect(tempLHS);
    tempPlace.cf();
    if (transition_placeholder >= tempPlace) {
      /* This is the good case, since our placeholder need not
       * be restricted. Hence, we need not do anything here */

    } else {
      // Here tempRetDBM (retPlaceDBM) < tempLHSCp, meaning a restricted
      // placeholder Same code as when empty, but we have another placeholder
      DBMList* newPlace;
      DBMList invList(invariant_region);
      !invList;
      invList.cf();
      !guard_region;
      guard_region.cf();
      // Now combine the placeholders
      bool invEmpty = invList.emptiness();
      bool guardEmpty = guard_region.emptiness();
      // we know that tempPlace is not empty
      if (invEmpty && guardEmpty) {
        // This means that no such placeholder is possible
        newPlace = new DBMList(transition_placeholder);
      } else {
        if (invEmpty) {
          newPlace = new DBMList(guard_region);
        } else if (guardEmpty) {
          newPlace = new DBMList(invList);
        } else if (invList <= guard_region) {
          newPlace = new DBMList(guard_region);
        } else if (guard_region <= invList) {
          newPlace = new DBMList(invList);
        } else {
          /* This is the bad case, because zone unions are required */
          newPlace = new DBMList(guard_region);
          newPlace->addDBMList(invList);
        }
        /* Like OR, we now handle the tempPlace.
         * However, we know that both are not empty */
        if (tempPlace <= *newPlace) {
          // nothing needs to be done here
        } else if (*newPlace <= tempPlace) {
          delete newPlace;
          newPlace = new DBMList(tempPlace);
        } else {
          /* This is the bad case, because zone unions are required */
          newPlace->addDBMList(transition_placeholder);
        }
      }
      transition_placeholders.push_back(newPlace);
    }
  }


  /* Handle the vector */
  if (!(transition_placeholders.empty()) && !(emptyRetPlace)) {
    /* If the vector is empty, then there is nothing to do
     * hence, we only
     * handle the case with a non-empty placeholder. */
    // For now, just intersect the placeholders
    for (std::vector<DBMList*>::iterator it = transition_placeholders.begin();
         it != transition_placeholders.end(); it++) {
      /* Intersecting alone is not good enough, so need to do both */
      place->intersect(*(*it));
      place->cf();
    }
  }

  // Now go through the vector and delete everything in the vector
  // (Don't delete the transitions since we passed references,
  // but do delete the DBMLists since we passed copies)
  delete_vector_elements(transition_placeholders);
  transition_placeholders.clear();

  cpplog(cpplogging::debug)
      << "\t --- end of ALLACT. Returned plhold: " << *place << std::endl;
}

inline void prover::do_proof_place_existact(const SubstList& discrete_state,
                                                const DBM& zone,
                                                DBMList* place,
                                                const ExprNode& formula) {
  DBMList result(*place); // DBM to accumulate the result.
  result.makeEmpty();

  /* Enumerate through all transitions */
  cpplog(cpplogging::debug) << "\t Proving EXISTACT Transitions:----\n"
                            << std::endl;

  for (std::vector<Transition*>::const_iterator it =
           input_pes.transitions().begin();
       it != input_pes.transitions().end(); it++) {
    Transition* transition = *it;

    /* Obtain the entire ExprNode and prove it */

    DBMList tempPlace(*place);
    DBM tempLHS(zone);
    // Method tightens zone and place to those subsets satisfying the guard
    // (leftExpr).
    bool guard_satisfied = comp_ph_exist_place(&tempLHS, &tempPlace,
                                        *(transition->getLeftExpr()), discrete_state);
    if (!guard_satisfied) {
      cpplog(cpplogging::debug)
          << "Transition: " << transition << " cannot be taken." << std::endl;
      continue;
    }

    /* Now check the invariant of the target location (getEnteringLocation gives
       the destination location of the transition */
    DBM invariant_region(*INFTYDBM);
    const SubstList* source_location = transition->getEnteringLocation(&discrete_state);
    bool invariant_satisfiable = restrict_to_invariant(
        input_pes.invariants(), &invariant_region, *source_location);
    delete source_location;
    if (invariant_satisfiable) { // the invariant does not hold vacuously.
      invariant_region.cf();
      const ClockSet* reset_clocks = transition->getCSet();
      if (reset_clocks != nullptr) {
        invariant_region.preset(reset_clocks);
      }
      invariant_region.cf();
      /* Now perform clock assignments sequentially: perform the
       * front assignments first */
      const std::vector<std::pair<short int, short int>>* clock_assignments =
          transition->getAssignmentVector();
      if (clock_assignments != nullptr) {
        // Iterate over the vector and print it
        for (std::vector<std::pair<short int, short int>>::const_iterator it =
                 clock_assignments->begin();
             it != clock_assignments->end(); it++) {
          invariant_region.preset((*it).first, (*it).second);
          invariant_region.cf();
        }
      }
      /* Check if invariant preset is satisfied by the zone.
       * If not, tighten the placeholder */
      // For performace reasons, also tighten the left hand side
      if (!(tempLHS <= invariant_region)) {
        tempPlace.intersect(invariant_region);
        tempPlace.cf();
        if (tempPlace.emptiness()) {
          cpplog(cpplogging::debug)
              << "Transition: " << transition
              << " cannot be taken; entering invariant is false." << std::endl
              << "\tExtra invariant condition: " << invariant_region << std::endl;

          continue;
        }
        tempLHS.intersect(invariant_region);
        tempLHS.cf();
      }
    }

    transition->getNewTrans(formula.getQuant());
    /* Constraints are bounded by input_pes.max_constant() */
    /* This is to extend the LHS to make sure that
     * the RHS is satisfied by any zone that satisfies
     * the LHS by expanding the zone so it contains
     * all the proper regions where the clocks
     * exceed a certain constant value. */

    // for performance reasons, also tighten LHS with invariant

    tempLHS.bound(input_pes.max_constant());
    tempLHS.cf();

    cpplog(cpplogging::debug)
        << "Executing transition (with destination) " << transition << std::endl
        << "\tExtra invariant condition: " << invariant_region << std::endl;

    numLocations++;
    do_proof_place(discrete_state, tempLHS, &tempPlace, *transition->getRightExpr());
    tempPlace.cf();
    /* placeholder logic partially incomplete
     * due to not addressing when new placeholder
     * is incomparable to the previous */
    if (tempPlace.emptiness()) {
      // skip, already covered by result.
    } else if (tempPlace >= *place) { // FIXME: shouldn't this be LHS?
      /* Here, the current transition successful;
       * we are done */
      result = *place;
      break;
    } else if (result.emptiness()) {
      result = tempPlace;
      // result was empty, tempPlace is it.
    } else if (tempPlace <= result) {
      // result is included in previousdbm,
    } else if (result <= tempPlace) {
      result = tempPlace;
      /* here, we keep tempPlace as our current. */
    } else { /* Corner Case: make a union of DBMLists */
      result.addDBMList(tempPlace);
    }
  }

  cpplog(cpplogging::debug)
      << "\t --- end of EXISTACT. Returned plhold: " << result
      << std::endl;
  *place = result;
}

inline void prover::do_proof_place_imply(const SubstList& discrete_state,
                                             const DBM& zone,
                                             DBMList* place,
                                             const ExprNode& formula) {
  DBM lhs_copy(zone);
  /* call comp_ph() for efficient proving of IMPLY's left. */
  if (comp_ph(&lhs_copy, *(formula.getLeft()), discrete_state)) {
    /* Constraints are bounded by input_pes.max_constant() */
    /* This is to extend the LHS to make sure that
     * the RHS is satisfied by any zone that satisfies
     * the LHS by expanding the zone so it contains
     * all the proper regions where the clocks
     * exceed a certain constant value. */
    lhs_copy.cf();
    lhs_copy.bound(input_pes.max_constant());
    lhs_copy.cf();
    do_proof_place(discrete_state, lhs_copy, place, *formula.getRight());
  } else {
    /* The set of states does not satisfy the premises of the IF
     * so thus the proof is true */
    cpplog(cpplogging::debug)
        << "---(Valid) Leaf IMPLY Reached, Premise Not Satisfied----"
        << std::endl
        << std::endl;
  }
}

inline void prover::do_proof_place_constraint(const DBM& zone,
                                                  DBMList* place,
                                                  const ExprNode& formula) {
  // The line: (formula->dbm())->cf(); is not needed.
  if (zone <= *(formula.dbm())) {
    cpplog(cpplogging::debug) << "---(Valid) Leaf DBM (CONSTRAINT) Reached "
                                 "with no need for Placeholder----"
                              << std::endl
                              << std::endl;
  } else {
    /* Here, since we only have a single constraint here,
     * DBM will tighten only to match the single constraint
     * Since multiple constraints are represented as an
     * AND of Constraints */
    place->intersect(*(formula.dbm()));
    place->cf();

    // Now test constraint
    DBMList tPlace(*place);
    tPlace.intersect(zone);
    tPlace.cf();

    if (tPlace.emptiness()) {
      // New Combined DBM Does not satisfy Constraint
      place->makeEmpty();
      cpplog(cpplogging::debug)
          << "---(Invalid, Placeholder) Leaf DBM (CONSTRAINT) Unsatisfied "
             "regardless of placeholder----"
          << std::endl
          << std::endl;
    } else {
      cpplog(cpplogging::debug)
          << "---(Valid, Placeholder) Leaf DBM (CONSTRAINT) Reached and "
             "Placeholder Computed----"
          << std::endl
          << "----Placeholder := {" << *place << "}----" << std::endl
          << std::endl;
    }
  }
}

inline void prover::do_proof_place_bool(DBMList* place,
                                            const ExprNode& formula) {
  if (!do_proof_bool(formula)) {
    place->makeEmpty();
  }
}

inline void prover::do_proof_place_atomic(const SubstList& discrete_state,
                                              DBMList* place,
                                              const ExprNode& formula) {
  if (!do_proof_atomic(discrete_state, formula)) {
    place->makeEmpty();
  }
}

inline void prover::do_proof_place_atomic_not(const SubstList& discrete_state,
                                                  DBMList* place,
                                                  const ExprNode& formula) {
  if (!do_proof_atomic_not(discrete_state, formula)) {
    place->makeEmpty();
  }
}

inline void prover::do_proof_place_atomic_lt(const SubstList& discrete_state,
                                                 DBMList* place,
                                                 const ExprNode& formula) {
  if (!do_proof_atomic_lt(discrete_state, formula)) {
    place->makeEmpty();
  }
}

inline void prover::do_proof_place_atomic_gt(const SubstList& discrete_state,
                                                 DBMList* place,
                                                 const ExprNode& formula) {
  if (!do_proof_atomic_gt(discrete_state, formula)) {
    place->makeEmpty();
  }
}

inline void prover::do_proof_place_atomic_le(const SubstList& discrete_state,
                                                 DBMList* place,
                                                 const ExprNode& formula) {
  if (!do_proof_atomic_le(discrete_state, formula)) {
    place->makeEmpty();
  }
}

inline void prover::do_proof_place_atomic_ge(const SubstList& discrete_state,
                                                 DBMList* place,
                                                 const ExprNode& formula) {
  if (!do_proof_atomic_ge(discrete_state, formula)) {
    place->makeEmpty();
  }
}

inline void prover::do_proof_place_sublist(const SubstList& discrete_state,
                                               const DBM& zone,
                                               DBMList* place,
                                               const ExprNode& formula) {
  SubstList st(formula.getSublist(), &discrete_state);
  do_proof_place(st, zone, place, *formula.getExpr());
}

inline void prover::do_proof_place_reset(const SubstList& discrete_state,
                                             const DBM& zone,
                                             DBMList* place,
                                             const ExprNode& formula) {
  // Bound the LHS to prevent infinite proofs
  DBM lhs_reset(zone);
  lhs_reset.bound(input_pes.max_constant());
  lhs_reset.cf();
  lhs_reset.reset(formula.getClockSet());
  lhs_reset.cf();

  DBMList tPlace(*INFTYDBM);
  do_proof_place(discrete_state, lhs_reset, &tPlace, *formula.getExpr());
  tPlace.cf();
  if (tPlace.emptiness()) {
    *place = tPlace;
  } else {
    /* Now do the check that the new placeholder follows from
     * the previous placeholder. by setting it to such */
    DBMList p2Copy(tPlace);
    // Apply the reset (weakest precondition operator)
    p2Copy.preset(formula.getClockSet());

    // Use the rule to compute what the old place holder should be
    place->intersect(p2Copy);
    place->cf();
    bool retVal = !place->emptiness();

    if (cpplogEnabled(cpplogging::debug)) {
      print_sequent_placeCheck(std::cerr, step - 1, retVal, zone, *place, p2Copy,
                               discrete_state, formula.getOpType());
      if (retVal) {
        cpplog(cpplogging::debug)
            << "----(Valid) Placeholder Check Passed-----" << std::endl
            << "--With Placeholder := {" << *place << "} ----" << std::endl
            << std::endl;
      } else {
        cpplog(cpplogging::debug)
            << "----(Invalid) Placeholder Check Failed-----" << std::endl
            << std::endl;
      }
    }
  }
}

inline void prover::do_proof_place_assign(const SubstList& discrete_state,
                                              const DBM& zone,
                                              DBMList* place,
                                              const ExprNode& formula) {
  // use zone->cf() for more efficiency
  DBM lhs_assign(zone);
  /* Here the DBM zone is where the value of
   * clock x is reset to clock y, which is possibly
   * a constant or a value*/
  short int cX = formula.getcX();
  short int cY = formula.getcY();
  lhs_assign.reset(cX, cY);
  lhs_assign.cf();
  DBMList placeB(*INFTYDBM);
  do_proof_place(discrete_state, lhs_assign, &placeB, *formula.getExpr());
  placeB.cf();
  if (placeB.emptiness()) {
    *place = placeB;
  } else {
    // Double Check that the new placeholder follows from the first
    placeB.preset(cX, cY);

    // Now assign the old placeholder accordingly
    place->intersect(placeB);
    place->cf();

    if (cpplogEnabled(cpplogging::debug)) {
      bool retVal = !place->emptiness();
      print_sequent_placeCheck(std::cerr, step - 1, retVal, zone, *place, placeB,
                               discrete_state, formula.getOpType());
      if (retVal) {
        cpplog(cpplogging::debug)
            << "----(Valid) Placeholder Check Passed-----" << std::endl
            << "--With Placeholder := {" << *place << "} ----" << std::endl
            << std::endl;
      } else {
        cpplog(cpplogging::debug)
            << "----(Invalid) Placeholder Check Failed-----" << std::endl
            << std::endl;
      }
    }
  }
}

inline void prover::do_proof_place_replace(const SubstList& discrete_state,
                                               const DBM& zone,
                                               DBMList* place,
                                               const ExprNode& formula) {
  SubstList sub_(discrete_state);
  sub_[formula.getcX()] = discrete_state.at(formula.getcY());
  do_proof_place(sub_, zone, place, *formula.getExpr());
}

inline void prover::do_proof_place_ablewaitinf(const SubstList& discrete_state,
                                                   const DBM& zone,
                                                   DBMList* place) {
  DBMList ph(zone);
  ph.intersect(*place);
  ph.cf();
  ph.suc();
  restrict_to_invariant(input_pes.invariants(), &ph, discrete_state);
  ph.cf();
  /* Time can diverge if and only if there are no upper bound
   * constraints in the successor. By design of succ() and invariants,
   * either all DBMs have an upper bound constraint, or none
   * of them do. Hence, checking the first is always good enough. */
  assert(!ph.getDBMList()->empty());
  DBM* currDBM = *(ph.getDBMList()->begin());

  if (currDBM->hasUpperConstraint()) {
    place->makeEmpty();
    cpplog(cpplogging::debug)
        << "---(Invalid) Time unable to diverge to INFTY in current location---"
        << std::endl
        << std::endl;
  } else {
    cpplog(cpplogging::debug)
        << "---(Valid) Time able to diverge to INFTY in current location----"
        << std::endl
        << std::endl;
  }
}

inline void prover::do_proof_place_unablewaitinf(const SubstList& discrete_state,
                                                     const DBM& zone,
                                                     DBMList* place) {
  DBMList ph(zone);
  ph.intersect(*place);
  ph.cf();
  ph.suc();
  restrict_to_invariant(input_pes.invariants(), &ph, discrete_state);
  ph.cf();
  /* Time cannot diverge if and only if there is an upper bound
   * constraint in the successor. By design of succ() and invariants,
   * either all DBMs have an upper bound constraint, or none
   * of them do. Hence, checking the first is always good enough. */
  assert(!ph.getDBMList()->empty());
  DBM* currDBM = *(ph.getDBMList()->begin());
  if (!currDBM->hasUpperConstraint()) {
    place->makeEmpty();
    cpplog(cpplogging::debug)
        << "---(Invalid) Time able to diverge to INFTY in current location---"
        << std::endl
        << std::endl;
  } else {
    cpplog(cpplogging::debug)
        << "---(Valid) Time unable to diverge to INFTY in current location----"
        << std::endl
        << std::endl;
  }
}

#endif /* PROOF_HH */
