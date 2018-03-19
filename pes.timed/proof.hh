/** \file proof.hh
 * Proof-search implementation for timed-automata model checking, based on PESs.
 * @author Peter Fontana
 * @author Dezhuang Zhang
 * @author Rance Cleaveland
 * @author Jeroen Keiren
 * @copyright MIT Licence, see the accompanying LICENCE.txt
 */

#ifndef PROOF_HH
#define PROOF_HH

#include "cpplogging/logger.h"
#include "prover_options.hh"
#include "pes.hh"
#include "DBM.hh"
#include "ExprNode.hh"
#include "transition.hh"
#include "comp_ph.hh"
#include "sequent_cache.hh"

class prover {
protected:
  const pes& input_pes;

  const prover_options& options;

  bool currParityGfp;
  bool prevParityGfp;

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

  /** Cache for storing sequents. This incorporates true and false sequents, as
   * well as sequents for predicate variables in order to detect cycles.
   */
  sequent_cache cache;

public:
  prover(const pes& input_pes, const prover_options& options)
      : input_pes(input_pes),
        options(options),
        currParityGfp(false),
        prevParityGfp(false),
        step(0),
        numLocations(1),
        parentRef(nullptr),
        parentPlaceRef(nullptr),
        cache(input_pes, options.nbits, input_pes.predicates().size() * options.nHash, options.nHash) {
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

  /** Prove a given property for the provided PES.
   * @param p the PES to prove.
   * @param placeholder the placeholder to use (default nullptr).
   * if the nullptr is provided as placholder, internally do_proof (without placeholders)
   * is used. If a non-empty placeholder is provided, that placeholder is used in the
   * proof using do_proof_place. In this case, the method returns true iff the initial clock zone
   * is included in the resulting placeholder. */
  bool do_proof_init(pes& p, DBMList* placeholder = nullptr)
  {
    const ExprNode* start_pred = p.lookup_predicate(p.start_predicate());

    /* A Placeholder to remember the current parity;
     * false = lfp parity, true = gfp parity. */
    currParityGfp = start_pred->get_Parity();
    /* A Placeholder to remember the previous parity;
     * false = lfp parity, true = gfp parity. */
    prevParityGfp = currParityGfp;

    if (placeholder == nullptr)
    {
      return do_proof(p.initial_state(), *p.initial_clock_zone(), *start_pred);
    } else {
      do_proof_place(p.initial_state(), *p.initial_clock_zone(), placeholder, *start_pred);
      return *placeholder >= *p.initial_clock_zone();
    }
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
  __attribute__((flatten))
  bool do_proof(const SubstList& discrete_state,
                                         const DBM& zone,
                                         const ExprNode& formula) {
    assert(zone.isInCf());
    bool result = false;
    if (cpplogEnabled(cpplogging::debug)) {
      print_sequent(std::cerr, step, result, zone, formula, discrete_state,
                    formula.getOpType());
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
        result = do_proof_place_bool(nullptr, formula);
        break;
      }
      case ATOMIC: {
        result = do_proof_place_atomic(discrete_state, nullptr, formula);
        break;
      }
      case ATOMIC_NOT: {
        result = do_proof_place_atomic_not(discrete_state, nullptr, formula);
        break;
      }
      case ATOMIC_LT: {
        result = do_proof_place_atomic_lt(discrete_state, nullptr, formula);
        break;
      }
      case ATOMIC_GT: {
        result = do_proof_place_atomic_gt(discrete_state, nullptr, formula);
        break;
      }
      case ATOMIC_LE: {
        result = do_proof_place_atomic_le(discrete_state, nullptr, formula);
        break;
      }
      case ATOMIC_GE: {
        result = do_proof_place_atomic_ge(discrete_state, nullptr, formula);
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
        result = do_proof_place_ablewaitinf(discrete_state, zone, nullptr);
        break;
      }
      case UNABLEWAITINF: {
        result = do_proof_place_unablewaitinf(discrete_state, zone, nullptr);
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
  bool do_proof_sublist(const SubstList& discrete_state, const DBM& zone,
                        const ExprNode& formula);
  bool do_proof_reset(const SubstList& discrete_state, const DBM& zone,
                      const ExprNode& formula);
  bool do_proof_assign(const SubstList& discrete_state, const DBM& zone,
                       const ExprNode& formula);
  bool do_proof_replace(const SubstList& discrete_state, const DBM& zone,
                        const ExprNode& formula);

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
  bool do_proof_place_bool(DBMList* place, const ExprNode& formula);
  bool do_proof_place_atomic(const SubstList& discrete_state,
                             DBMList* place, const ExprNode& formula);
  bool do_proof_place_atomic_not(const SubstList& discrete_state,
                                 DBMList* place, const ExprNode& formula);
  bool do_proof_place_atomic_lt(const SubstList& discrete_state,
                                DBMList* place, const ExprNode& formula);
  bool do_proof_place_atomic_gt(const SubstList& discrete_state,
                                DBMList* place, const ExprNode& formula);
  bool do_proof_place_atomic_le(const SubstList& discrete_state,
                                DBMList* place, const ExprNode& formula);
  bool do_proof_place_atomic_ge(const SubstList& discrete_state,
                                DBMList* place, const ExprNode& formula);
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
  bool do_proof_place_ablewaitinf(const SubstList& discrete_state,
                                  const DBM& zone, DBMList* place);
  bool do_proof_place_unablewaitinf(const SubstList& discrete_state,
                                    const DBM& zone, DBMList* place);

  inline void establish_exists_rel_sidecondition(
      DBMList* result,
      const DBM& zone,
      const DBMList& placeholder1,
      const DBMList& placeholder2) {

    // By default do not print the debugging info for computing side condition.
    // The this next line to debug to get the output
      cpplogging::logger::set_reporting_level(cpplogging::verbose, "exists_rel_sidecondition");

    cpplog(cpplogging::debug, "exists_rel_sidecondition") << "Computing side condition for relativized exists with zone " << zone << std::endl
                              << " placeholder1: " << placeholder1 << std::endl
                              << " placeholder2: " << placeholder2 << std::endl;
    DBM succ_zone(zone);
    succ_zone.suc();
    succ_zone.cf();

    // First check if placeholder2 works without restricting.
    DBMList pred_placeholder2_strict(placeholder2);
    pred_placeholder2_strict.pre();
    pred_placeholder2_strict.predClosureRev();
    pred_placeholder2_strict.cf();

    cpplog(cpplogging::debug, "exists_rel_sidecondition") << "  pre_<(placeholder2) = " << pred_placeholder2_strict << std::endl;

    // left hand side of containment check
    DBMList succ_zone_and_pred_placeholder2_strict(succ_zone);
    succ_zone_and_pred_placeholder2_strict.intersect(pred_placeholder2_strict);
    succ_zone_and_pred_placeholder2_strict.cf();

    cpplog(cpplogging::debug, "exists_rel_sidecondition") << "  succ((l,cc)) && pre_<(placeholder2) = " << succ_zone_and_pred_placeholder2_strict << std::endl;

    // right hand side of containment check
    DBMList succ_zone_and_placeholder1(succ_zone);
    succ_zone_and_placeholder1.intersect(placeholder1);
    succ_zone_and_placeholder1.cf();

    cpplog(cpplogging::debug, "exists_rel_sidecondition") << "  succ((l,cc)) && placeholder1 = " << succ_zone_and_placeholder1 << std::endl;

    if(succ_zone_and_pred_placeholder2_strict <= succ_zone_and_placeholder1) {
      *result = placeholder2;
      cpplog(cpplogging::debug, "exists_rel_sidecondition") << "   placeholder2 works!" << std::endl;
    } else {
      result->makeEmpty();

      DBMList placeholder1_complement(placeholder1);
      !placeholder1_complement;
      placeholder1_complement.cf();

      cpplog(cpplogging::debug, "exists_rel_sidecondition") << "   !placeholder1 = " << placeholder1_complement << std::endl;

      // Process on a per-DBM basis
      for (const DBM* const placeholder2_zone: *placeholder2.getDBMList())
      {
        cpplog(cpplogging::debug, "exists_rel_sidecondition") << "    placeholder2-part = " << *placeholder2_zone << std::endl;

        DBM pred_placeholder2_zone_strict(*placeholder2_zone);
        pred_placeholder2_zone_strict.pre();
        pred_placeholder2_zone_strict.predClosureRev();
        pred_placeholder2_zone_strict.cf();

        cpplog(cpplogging::debug, "exists_rel_sidecondition") << "    pre_<(placeholder2-part) = " << pred_placeholder2_zone_strict << std::endl;

        // left hand side of containment check
        DBMList succ_zone_and_pred_placeholder2_zone_strict(succ_zone);
        succ_zone_and_pred_placeholder2_zone_strict.intersect(pred_placeholder2_zone_strict);
        succ_zone_and_pred_placeholder2_zone_strict.cf();
        cpplog(cpplogging::debug, "exists_rel_sidecondition") << "    succ((l,cc)) && pre_<(placeholder2-part) = " << succ_zone_and_pred_placeholder2_zone_strict << std::endl;

        DBMList bad(succ_zone_and_pred_placeholder2_zone_strict);
        bad.intersect(placeholder1_complement);
        bad.cf();

        cpplog(cpplogging::debug, "exists_rel_sidecondition") << "    bad = " << bad << std::endl;

        DBMList bad_successors_strict(bad);
        bad_successors_strict.suc();
        bad_successors_strict.closureRev();
        bad_successors_strict.cf();

        DBMList bad_successors_strict_complement(bad_successors_strict);
        !bad_successors_strict_complement;
        bad_successors_strict_complement.cf();

        DBMList placeholder(*placeholder2_zone);
        placeholder.intersect(bad_successors_strict_complement);
        placeholder.cf();

        cpplog(cpplogging::debug, "exists_rel_sidecondition") << "    adding placeholder " << placeholder << std::endl;

        result->addDBMList(placeholder);
      }
    }
  }

  inline void establish_forall_place_sidecondition(DBMList* result,
                                                   const SubstList& discrete_state,
                                                   const DBM& zone,
                                                   const DBMList& placeholder2)
  {
    assert(placeholder2.isInCf());

    // First, we establish whether placeholder2 is a good candidate for the result.
    // i.e. assume placeholder = !inv(l) || placeholder2
    DBM succ_zone(zone);
    succ_zone.suc();
    succ_zone.cf();

    // establish placeholder = !inv(l) || placeholder2
    // this ensures satisfaction of first sidecondition.
    DBMList placeholder(placeholder2);
    DBMList invariant_region(*INFTYDBM);
    bool nonempty_invariant = restrict_to_invariant(
        input_pes.invariants(), &invariant_region, discrete_state);
    if (nonempty_invariant) {
      !invariant_region;
      invariant_region.cf();
      placeholder.addDBMList(invariant_region);
      placeholder.cf();
    }

    // Guess placeholder_forall == placeholder is enough to satisfy second sidecondition.
    DBMList placeholder_forall(placeholder);

    // succ((l,cc)) && placeholder
    DBMList succ_zone_and_placeholder(placeholder);
    succ_zone_and_placeholder.intersect(succ_zone);
    succ_zone_and_placeholder.cf();

    // succ((l,cc) && placeholder_forall)
    DBMList succ_zone_restricted_to_placeholder_forall(zone);
    succ_zone_restricted_to_placeholder_forall.intersect(placeholder_forall);
    succ_zone_restricted_to_placeholder_forall.cf();
    succ_zone_restricted_to_placeholder_forall.suc();
    succ_zone_restricted_to_placeholder_forall.cf();

    if(succ_zone_restricted_to_placeholder_forall <= succ_zone_and_placeholder) {
      // success
      *result = placeholder_forall;
    } else {
      // restrict placeholder_forall.
      // oberve that forall(placeholder) = !exists(!placeholderl).
      // compute the subset of !placeholder that can be reached from (l,cc) && placeholder_forall
      DBMList not_placeholder(placeholder);
      !not_placeholder;
      not_placeholder.intersect(succ_zone_restricted_to_placeholder_forall);
      not_placeholder.cf();

      // Note for exists(!placeholder), we determine all predecessors that
      // lead to this set.
      not_placeholder.pre();
      not_placeholder.cf();
      // we now have an approximation of exists(!placeholder_forall)
      !not_placeholder;
      // and this leads to an approximation of !exists(!placeholder_forall);
      // We do ensure all these states are reachable from (l,cc).
      not_placeholder.intersect(succ_zone);
      not_placeholder.cf();

      // Restrict placeholder!
      placeholder_forall.intersect(not_placeholder);
      placeholder_forall.cf();

      // Check that this is indeed correct.
      // succ((l,cc) && placeholder_forall)
      succ_zone_restricted_to_placeholder_forall = zone;
      succ_zone_restricted_to_placeholder_forall.intersect(placeholder_forall);
      succ_zone_restricted_to_placeholder_forall.cf();
      succ_zone_restricted_to_placeholder_forall.suc();
      succ_zone_restricted_to_placeholder_forall.cf();

      if(succ_zone_restricted_to_placeholder_forall.emptiness() || succ_zone_restricted_to_placeholder_forall <= succ_zone_and_placeholder) {
        *result = placeholder_forall;
      } else {
        cpplog(cpplogging::debug, "forall_place_sidecondition")
            << "placeholder_forall: " << placeholder_forall << std::endl
            << "succ((l,cc) && placeholder_forall): " << succ_zone_restricted_to_placeholder_forall << std::endl
            << "succ((l,cc)) && old placeholder_forall: " << succ_zone_and_placeholder << std::endl;
        assert(succ_zone_restricted_to_placeholder_forall <= succ_zone_and_placeholder);
        // The old implementation simply returns the empty placeholder here.
        // JK is wondering whether this is really reachable.
        result->makeEmpty();
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
  const int predicate_index =
      input_pes.lookup_predicate(formula.getPredicate())->getIntVal() - 1;
  prevParityGfp = currParityGfp;
  currParityGfp = formula.get_Parity();

  /* Look in Known True and Known False Sequent Caches */
  if (options.useCaching) {
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
      bool newSequent;
      h = cache.Xlist_pGFP.locate_sequent(t, predicate_index, newSequent);
      if ((!newSequent) && h->tabled_sequent(zone)) {
        // Found gfp Circularity - thus valid
        cpplog(cpplogging::debug)
            << "---(Valid) Located a True Sequent or gfp Circularity ----"
            << std::endl
            << std::endl;

        /* Add backpointer to parent sequent (shallow copy) */
        h->addParent(parentRef);

        // Add sequent to known true cache
        if (options.useCaching) {
          Sequent* true_sequent = new Sequent(&formula, &discrete_state);
          Sequent* cached_true_sequent =
              cache.Xlist_true.locate_sequent(true_sequent, predicate_index, newSequent);
          cached_true_sequent->update_sequent(zone);
        }
        return true; // greatest fixed point circularity found
      }
    } else { // Thus, a least fixpoint
      // Now look for a Circularity
      bool newSequent;
      h = cache.Xlist_pLFP.locate_sequent(t, predicate_index, newSequent);
      if ((!newSequent) && h->tabled_sequent_lfp(zone)) {
        cpplog(cpplogging::debug)
            << "---(Invalid) Located a lfp Circularity ----" << std::endl
            << std::endl;

        /* Add backpointer to parent sequent (shallow copy) */
        h->addParent(parentRef);

        // Now Put Sequent in False Cache
        if (options.useCaching) {
          Sequent* false_sequent = new Sequent(&formula, &discrete_state);
          Sequent* cached_false_sequent =
              cache.Xlist_false.locate_sequent(false_sequent, predicate_index, newSequent);
          cached_false_sequent->update_false_sequent(zone);
        }
        return false; // least fixed point circularity found
      }
    }
    h->push_sequent(new DBM(zone));
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
  if (options.useCaching) {
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
      bool newSequent;
      Sequent* cached_true_sequent =
          cache.Xlist_true.locate_sequent(true_sequent, predicate_index, newSequent);
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
      bool newSequent;
      Sequent* cached_false_sequent =
          cache.Xlist_false.locate_sequent(false_sequent, predicate_index, newSequent);
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

  // Reset place parent to nullptr
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

    // Reset place parent to nullptr
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

  // Reset place parent to nullptr
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
    restrict_to_invariant(input_pes.invariants(), &placeholder2, discrete_state);
    placeholder2.cf();
    do_proof_place(discrete_state, lhs_succ, &placeholder2, *formula.getRight());
    placeholder2.cf();

    cpplog(cpplogging::debug)
        << "----() Formula \\phi_2 placeholder obtained as {" << placeholder2
        << "} ----" << std::endl
        << std::endl;

    // Reset place parent to nullptr
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
      establish_forall_place_sidecondition(&placeholder_forall, discrete_state, zone, placeholder2);
      placeholder_forall.cf();

      if (cpplogEnabled(cpplogging::debug)) {
        print_sequentCheck(cpplogGet(cpplogging::debug), step - 1, retVal,
                           lhs_succ, placeholder2, discrete_state, formula.getOpType());
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
      DBMList placeholder_exists(*INFTYDBM);
      /*--- PredCheck code----*/
      DBMList placeholder_and(placeholder2);
      placeholder_and.intersect(placeholder1);
      placeholder_and.cf();
      establish_exists_rel_sidecondition(&placeholder_exists, zone, placeholder2, placeholder_and);
      placeholder_exists.cf();
      cpplog(cpplogging::debug)
          << "----() FORALL Rel Exists predCheck placeholder obtained as := {"
          << placeholder_exists << "} ----" << std::endl
          << std::endl;

      if (!placeholder_exists.emptiness()) {
        /* Now check that it works. */
        placeholder_exists.pre();
        /* This cf() is needed. */
        placeholder_exists.cf();

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
          placeholder_exists.cf();
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

  DBMList placeholder_dbg_copy(placeholder); // Check assumption on do_proof_place
  do_proof_place(discrete_state, lhs_succ, &placeholder, *formula.getQuant());
  // Reset place parent to nullptr
  parentPlaceRef = nullptr;
  placeholder.cf();
  assert(placeholder <= placeholder_dbg_copy);

  placeholder.pre();
  placeholder.cf();
  bool retVal = placeholder >= zone;

  if (cpplogEnabled(cpplogging::debug)) {
    print_sequentCheck(cpplogGet(cpplogging::debug), step - 1, retVal, zone,
                       placeholder, discrete_state, formula.getOpType());
    if (placeholder.emptiness()) {
      cpplog(cpplogging::debug) << "----(Invalid) Empty Placeholder: No Need "
                                   "for Placeholder Check-----" << std::endl
                                << std::endl;
    } else if (retVal) {
      cpplog(cpplogging::debug)
          << "----(Valid) Placeholder Check Passed (Check Only)-----" << std::endl
          << "----With Placeholder := {" << placeholder << "} ----"
          << std::endl << std::endl;
    } else {
      cpplog(cpplogging::debug)
          << "----(Invalid) Placeholder Check Failed-----" << std::endl
          << std::endl;
    }
  }

  return retVal;
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
  // Reset place parent to nullptr
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
      // FIXME: the following code can be simplified significantly (only the inclusion is needed)
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
          assert(placeholder2 == zone);
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
                                         // used in the sidecondition
                                         // computation
      /*--- PredCheck code----*/
      establish_exists_rel_sidecondition(&placeholder, zone, placeholder1, placeholder2);
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
        //placeholder.closure();
        /* Extract the new refined placeholder. */
        //placeholder.intersect(placeholder2);
        //placeholder.cf();
        assert(placeholder <= placeholder2);

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

  for (Transition* const transition: input_pes.transitions()) {
    /* Obtain the entire ExprNode and prove it */
    DBM guard_zone(zone);

    bool guard_satisfied =
        comp_ph(&guard_zone, *(transition->guard()), discrete_state);
    if (!guard_satisfied) {
      cpplog(cpplogging::debug)
          << "Transition: " << transition << " cannot be taken." << std::endl;
      continue;
    }

    /* Now check the invariant; if the invariant is satisfiable, we update the
       left hand side to be the part of the left hand side that satisfies the
       location invariant. */
    DBM invariant_zone(*INFTYDBM);
    bool invariant_satisfiable = restrict_to_invariant(
        input_pes.invariants(), &invariant_zone, transition->destination_location(&discrete_state));

    if (invariant_satisfiable) {
      invariant_zone.cf();
      // Some clocks are reset on this transition
      const ClockSet* reset_clocks = transition->reset_clocks();
      if (reset_clocks != nullptr) {
        invariant_zone.preset(reset_clocks);
      }
      invariant_zone.cf();
      /* Now perform clock assignments sequentially: perform the
       * front assignments first */
      const std::vector<std::pair<short int, short int>>* clock_assignments =
          transition->clock_assignments();
      if (clock_assignments != nullptr) {
        // Iterate over the vector and print it
        for (const std::pair<short int, short int>& clock_assignment: *clock_assignments) {
          invariant_zone.preset(clock_assignment.first, clock_assignment.second);
          invariant_zone.cf();
        }
      }

      guard_zone.intersect(invariant_zone);
      guard_zone.cf();
      if (guard_zone.emptiness()) {
        cpplog(cpplogging::debug)
            << "Transition: " << transition
            << " cannot be taken; entering invariant is false." << std::endl
            << "\tExtra invariant condition: " << invariant_zone << std::endl;
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
    guard_zone.cf();
    guard_zone.bound(input_pes.max_constant());
    guard_zone.cf();

    cpplog(cpplogging::debug)
        << "Executing transition (with destination) " << transition << std::endl
        << "\tExtra invariant condition: " << invariant_zone << std::endl;

    numLocations++;
    retVal = do_proof(discrete_state, guard_zone, *transition->getRightExpr());
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
  for (Transition* const transition: input_pes.transitions()) {
    /* Obtain the entire ExprNode and prove it */

    // Make a similar comp function for exists so
    // because the entire zone must be able to transition
    // or split by placeholders
    DBMList tempPlace(*INFTYDBM);
    DBM tempLHS(zone);
    bool guard_satisfied = comp_ph_exist_place(
        &tempLHS, &tempPlace, *(transition->guard()), discrete_state);
    if (!guard_satisfied) {
      cpplog(cpplogging::debug)
          << "Transition: " << transition << " cannot be taken." << std::endl;
      continue;
    }

    /* Now check the invariant */
    DBM invariant_region(*INFTYDBM);
    bool invariant_satisfiable = restrict_to_invariant(
        input_pes.invariants(), &invariant_region, transition->destination_location(&discrete_state));
    if (invariant_satisfiable) {
      invariant_region.cf();
      const ClockSet* reset_clocks = transition->reset_clocks();
      if (reset_clocks != nullptr) {
        invariant_region.preset(reset_clocks);
      }
      invariant_region.cf();
      /* Now perform clock assignments sequentially: perform the
       * front assignments first */
      const std::vector<std::pair<short int, short int>>* clock_assignments =
          transition->clock_assignments();
      if (clock_assignments != nullptr) {
        for (const std::pair<short int, short int>& clock_assignment: *clock_assignments) {
          invariant_region.preset(clock_assignment.first, clock_assignment.second);
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

    // Reset place parent to nullptr
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
  // Formula is phi[x:=y] with x and y clocks.
  DBM lhs_assign(zone);
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

/* IMPLEMENTATION PROVER WITH PLACEHOLDERS */
inline void prover::do_proof_place_predicate(const SubstList& discrete_state,
                                             const DBM& zone, DBMList* place,
                                             const ExprNode& formula) {
  ExprNode* e = input_pes.lookup_equation(formula.getPredicate());

  // Get Predicate Index for Hashing
  int predicate_index =
      input_pes.lookup_predicate(formula.getPredicate())->getIntVal() - 1;
  prevParityGfp = currParityGfp;
  currParityGfp = formula.get_Parity();
  place->cf();

  /* First look in known true and false sequent tables */
  if (options.useCaching) {
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
      bool newSequent;
      h = cache.Xlist_pGFP_ph.locate_sequent(t, predicate_index, newSequent);
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
        if (options.useCaching) {
          SequentPlace* true_sequent = new SequentPlace(&formula, &discrete_state);
          SequentPlace* cached_true_sequent =
              cache.Xlist_true_ph.locate_sequent(true_sequent, predicate_index, newSequent);
          cached_true_sequent->update_sequent(zone, place);
        }
        return;
      }

      h->push_sequent(std::make_pair(new DBM(zone), new DBMList(*place)));
    } else { // Thus, a least fixpoint
      // Now look in lfp circularity cache
      bool newSequent;
      h = cache.Xlist_pLFP_ph.locate_sequent(t, predicate_index, newSequent);
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
        if (options.useCaching) {
          SequentPlace* false_sequent = new SequentPlace(&formula, &discrete_state);
          SequentPlace* cached_false_sequent =
              cache.Xlist_false_ph.locate_sequent(false_sequent,
                                                  predicate_index, newSequent);
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
  if (options.useCaching) {
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
      }

      // Now update in proper Cache
      bool newSequent;
      SequentPlace* cached_true_sequent =
          cache.Xlist_true_ph.locate_sequent(true_sequent, predicate_index, newSequent);
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
      bool newSequent;
      SequentPlace* cached_false_sequent =
          cache.Xlist_false_ph.locate_sequent(false_sequent, predicate_index, newSequent);
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
  do_proof_place(discrete_state, zone, place, *formula.getLeft());
  place->cf();
  if (!place->emptiness()) {
    DBMList placeholder_right(*place);
    do_proof_place(discrete_state, zone, &placeholder_right, *formula.getRight());
    place->intersect(placeholder_right);
  }
}

// [FC14] Proof rule \lor_{s2}
inline void prover::do_proof_place_or(const SubstList& discrete_state,
                                      const DBM& zone, DBMList* place,
                                      const ExprNode& formula) {
  place->cf();
  DBMList placeholder_left(*place);

  do_proof_place(discrete_state, zone, &placeholder_left, *formula.getLeft());
  placeholder_left.cf();

  if (!(placeholder_left >= *place))
  {
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
    assert(placeholder_left == *place);
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
    establish_forall_place_sidecondition(&placeholder_forall, discrete_state, zone, *place);
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
      print_sequentCheck(cpplogGet(cpplogging::debug), step - 1, false,
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

    DBMList placeholder2(*place);
    do_proof_place(discrete_state, lhs_succ, &placeholder2, *formula.getRight());
    placeholder2.cf();
    if (placeholder2.emptiness()) {
      place->makeEmpty();
    } else { // Only do if a nonempty placeholder
      /* Now do the second proof rule to compute the first placeholder
       */

      establish_forall_place_sidecondition(place, discrete_state, zone, placeholder2);
      place->cf();

      if (cpplogEnabled(cpplogging::debug)) {
        // This work is done in the succCheck method.
        // Perhaps I should move the debug rule there?
        bool retVal = !place->emptiness();

        DBMList succRuleConseq(zone);
        succRuleConseq.intersect(*place);
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
      print_sequentCheck(cpplogGet(cpplogging::debug), step - 1, false, zone,
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
    do_proof_place(discrete_state, zone, place, *formula.getRight());
    place->cf();
    if (!place->emptiness()) { // Only do if a nonempty placeholder
      if (cpplogEnabled(cpplogging::debug)) {
        print_sequentCheck(cpplogGet(cpplogging::debug), step - 1, true,
                           zone, *place, discrete_state, formula.getOpType());
        cpplog(cpplogging::debug)
            << "----(Valid) Placeholder Check Passed-----" << std::endl
            << "--With Placeholder := {" << *place << "} ----"
            << std::endl
            << std::endl;
      }
    }

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
    restrict_to_invariant(input_pes.invariants(), &placeholder2, discrete_state);
    placeholder2.cf();
    do_proof_place(discrete_state, lhs_succ, &placeholder2, *formula.getRight());
    placeholder2.cf();

    cpplog(cpplogging::debug)
        << "----() Formula \\phi_2 placeholder obtained as {" << placeholder2
        << "} ----" << std::endl
        << std::endl;

    // Reset place parent to nullptr
    parentPlaceRef = nullptr;

    if (placeholder2.emptiness()) {
      *place = placeholder2;
    } else if (placeholder2 >= lhs_succ) {
      /* \forallrel(\phi_2) holds, avoid extra work. */
      *place = placeholder2;
    } else {
      /* Now do a succ check on phi_2 to get \phi_forall
       * and a predCheck using both phi_1 and phi_2 to get phi_exists */
      /* we also note that the times satisfying \phi_1
       * (the relativization formula condition) are neither empty
       * nor everything. */

      DBMList placeholder_forall(*INFTYDBM);
      establish_forall_place_sidecondition(&placeholder_forall, discrete_state, zone, placeholder2);
      placeholder_forall.cf();

      if (cpplogEnabled(cpplogging::debug)) {
        print_sequentCheck(cpplogGet(cpplogging::debug), step - 1, false,
                           lhs_succ, placeholder2, discrete_state, formula.getOpType());
        cpplog(cpplogging::debug)
            << "----() FORALL (of FORALL_REL) Placeholder Check obtained  FA "
               "Placeholder := {"
            << placeholder_forall << "} ----" << std::endl
            << std::endl;
      }


      DBMList placeholder_exists(*INFTYDBM);
      DBMList placeholder_and(placeholder2);
      placeholder_and.intersect(placeholder1);
      placeholder_and.cf();
      establish_exists_rel_sidecondition(&placeholder_exists, zone, placeholder2, placeholder_and);
      placeholder_exists.cf();

      cpplog(cpplogging::debug)
          << "----() FORALL Rel Exists placeholder obtained as := {"
          << placeholder2 << "} ----" << std::endl
          << std::endl;

      if (!placeholder_exists.emptiness()) {
        /* Now check that it works. */
        /* Since we are not using retPlace anymore, we do not
         * need to copy it for the check. */
        placeholder_exists.pre();
        /* This cf() is needed. */
        placeholder_exists.cf();
        // check elapse further?

        if (cpplogEnabled(cpplogging::debug)) {
          print_sequentCheck(cpplogGet(cpplogging::debug), step - 1, false,
                             zone, placeholder_exists, discrete_state, formula.getOpType());
          cpplog(cpplogging::debug) << "----() FORALL Rel Exists placeholder "
                                       "after time elapse check is := {"
                                    << placeholder_exists << "} ----" << std::endl
                                    << std::endl;
        }
      }

      /* Last, we do an "or" check on the two placeholders */
      bool forallEmpty = placeholder_forall.emptiness();
      bool existsEmpty = placeholder_exists.emptiness();
      if (forallEmpty && existsEmpty) {
        place->makeEmpty();
      } else if (forallEmpty || placeholder_forall <= placeholder_exists) {
        *place = placeholder_exists;
      } else if (existsEmpty || placeholder_exists <= placeholder_forall) {
        *place = placeholder_forall;
      } else {
        *place = placeholder_exists;
        /* This case requires us to union the two placeholders. */
        place->addDBMList(placeholder_forall);
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
      *place = placeholder2;
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
      establish_exists_rel_sidecondition(&placeholder, zone, placeholder1, placeholder2);
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
  for (Transition* const transition: input_pes.transitions()) {
    /* Obtain the entire ExprNode and prove it */
    DBM tempLHS(zone);

    DBMList guard_region(*place);
    bool guard_satisfied =
        comp_ph_all_place(&tempLHS, &guard_region, *(transition->guard()),
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
    bool invariant_satisfiable = restrict_to_invariant(input_pes.invariants(),
                                                       &invariant_region,
                                                       transition->destination_location(&discrete_state));

    if (invariant_satisfiable) {
      invariant_region.cf();
      const ClockSet* reset_clocks = transition->reset_clocks();
      if (reset_clocks != nullptr) {
        invariant_region.preset(reset_clocks);
      }
      invariant_region.cf();
      /* Now perform clock assignments sequentially: perform the
       * front assignments first */
      const std::vector<std::pair<short int, short int>>* clock_assignments =
          transition->clock_assignments();
      if (clock_assignments != nullptr) {
        // Iterate over the vector and print it
        for (const std::pair<short int, short int>& clock_assignment: *clock_assignments) {
          invariant_region.preset(clock_assignment.first, clock_assignment.second);
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
  if (emptyRetPlace) {
    place->makeEmpty();
  } else {
    /* If the vector is empty, then there is nothing to do
     * hence, we only
     * handle the case with a non-empty placeholder. */
    // For now, just intersect the placeholders
    for (DBMList* const transition_placeholder: transition_placeholders) {
      /* Intersecting alone is not good enough, so need to do both */
      place->intersect(*transition_placeholder);
    }
    place->cf();
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

  for (Transition* const transition: input_pes.transitions()) {
    /* Obtain the entire ExprNode and prove it */

    DBMList tempPlace(*place);
    DBM tempLHS(zone);
    // Method tightens zone and place to those subsets satisfying the guard
    // (leftExpr).
    bool guard_satisfied = comp_ph_exist_place(&tempLHS, &tempPlace,
                                        *(transition->guard()), discrete_state);
    if (!guard_satisfied) {
      cpplog(cpplogging::debug)
          << "Transition: " << transition << " cannot be taken." << std::endl;
      continue;
    }

    /* Now check the invariant of the target location (getEnteringLocation gives
       the destination location of the transition */
    DBM invariant_region(*INFTYDBM);
    bool invariant_satisfiable = restrict_to_invariant(
        input_pes.invariants(), &invariant_region, transition->destination_location(&discrete_state));
    if (invariant_satisfiable) { // the invariant does not hold vacuously.
      invariant_region.cf();
      const ClockSet* reset_clocks = transition->reset_clocks();
      if (reset_clocks != nullptr) {
        invariant_region.preset(reset_clocks);
      }
      invariant_region.cf();
      /* Now perform clock assignments sequentially: perform the
       * front assignments first */
      const std::vector<std::pair<short int, short int>>* clock_assignments =
          transition->clock_assignments();
      if (clock_assignments != nullptr) {
        // Iterate over the vector and print it
        for (const std::pair<short int, short int>& clock_assignment: *clock_assignments) {
          invariant_region.preset(clock_assignment.first, clock_assignment.second);
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
      result = tempPlace;
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
      result.cf();
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
  DBM zone_copy(zone);
  /* call comp_ph() for efficient proving of IMPLY's left. */
  if (comp_ph(&zone_copy, *(formula.getLeft()), discrete_state)) {
    /* Constraints are bounded by input_pes.max_constant() */
    /* This is to extend the LHS to make sure that
     * the RHS is satisfied by any zone that satisfies
     * the LHS by expanding the zone so it contains
     * all the proper regions where the clocks
     * exceed a certain constant value. */
    zone_copy.bound(input_pes.max_constant());
    zone_copy.cf();
    do_proof_place(discrete_state, zone_copy, place, *formula.getRight());
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

    // Test if the constraint is satisfiable within the zone; if not, clear the
    // placeholder.
    // FIXME: this should be fine if we just use place here (although, strictly
    // speaking, the placeholder may become a bit smaller in that case).
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

inline bool prover::do_proof_place_bool(DBMList* place,
                                        const ExprNode& formula) {
  bool retVal = (formula.getBool());
  cpplog(cpplogging::debug) << "---(" << (retVal ? "V" : "Inv")
                            << "alid) Leaf BOOL Reached----" << std::endl
                            << std::endl;

  if (!retVal && place != nullptr) {
    place->makeEmpty();
  }

  return retVal;
}

inline bool prover::do_proof_place_atomic(const SubstList& discrete_state,
                                          DBMList* place,
                                          const ExprNode& formula) {
  bool retVal = (discrete_state.at(formula.getAtomic()) == formula.getIntVal());
  cpplog(cpplogging::debug) << "---(" << (retVal ? "V" : "Inv")
                            << "alid) Leaf ATOMIC == Reached----" << std::endl
                            << std::endl;
  if (!retVal && place != nullptr) {
    place->makeEmpty();
  }

  return retVal;
}

inline bool prover::do_proof_place_atomic_not(const SubstList& discrete_state,
                                              DBMList* place,
                                              const ExprNode& formula) {
  bool retVal = (discrete_state.at(formula.getAtomic()) != formula.getIntVal());
  cpplog(cpplogging::debug) << "---(" << (retVal ? "V" : "Inv")
                            << "alid) Leaf ATOMIC != Reached----" << std::endl
                            << std::endl;

  if (!retVal && place != nullptr) {
    place->makeEmpty();
  }

  return retVal;
}

inline bool prover::do_proof_place_atomic_lt(const SubstList& discrete_state,
                                             DBMList* place,
                                             const ExprNode& formula) {
  bool retVal = (discrete_state.at(formula.getAtomic()) < formula.getIntVal());
  cpplog(cpplogging::debug) << "---(" << (retVal ? "V" : "Inv")
                            << "alid) Leaf ATOMIC < Reached----" << std::endl
                            << std::endl;

  if (!retVal && place != nullptr) {
    place->makeEmpty();
  }

  return retVal;
}

inline bool prover::do_proof_place_atomic_gt(const SubstList& discrete_state,
                                             DBMList* place,
                                             const ExprNode& formula) {
  bool retVal = (discrete_state.at(formula.getAtomic()) > formula.getIntVal());
  cpplog(cpplogging::debug) << "---(" << (retVal ? "V" : "Inv")
                            << "alid) Leaf ATOMIC > Reached----" << std::endl
                            << std::endl;
  if (!retVal && place != nullptr) {
    place->makeEmpty();
  }
  return retVal;
}

inline bool prover::do_proof_place_atomic_le(const SubstList& discrete_state,
                                             DBMList* place,
                                             const ExprNode& formula) {
  bool retVal = (discrete_state.at(formula.getAtomic()) <= formula.getIntVal());
  cpplog(cpplogging::debug) << "---(" << (retVal ? "V" : "Inv")
                            << "alid) Leaf ATOMIC < Reached----" << std::endl
                            << std::endl;

  if (!retVal && place != nullptr) {
    place->makeEmpty();
  }
  return retVal;
}


inline bool prover::do_proof_place_atomic_ge(const SubstList& discrete_state,
                                             DBMList* place,
                                             const ExprNode& formula) {
  bool retVal = (discrete_state.at(formula.getAtomic()) >= formula.getIntVal());
  cpplog(cpplogging::debug) << "---(" << (retVal ? "V" : "Inv")
                            << "alid) Leaf ATOMIC > Reached----" << std::endl
                            << std::endl;

  if (!retVal && place != nullptr) {
    place->makeEmpty();
  }
  return retVal;
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
  DBM lhs_reset(zone);
// JK: It does not become clear why this is necessary here
//  lhs_reset.bound(input_pes.max_constant());
//  lhs_reset.cf();
  lhs_reset.reset(formula.getClockSet());
  lhs_reset.cf();

  DBMList placeholder1(*INFTYDBM);
  do_proof_place(discrete_state, lhs_reset, &placeholder1, *formula.getExpr());
  placeholder1.cf();
  if (placeholder1.emptiness()) {
    *place = placeholder1;
  } else {
    // Apply the preset (weakest precondition operator)
    placeholder1.preset(formula.getClockSet());

    // Use the rule to compute what the old place holder should be
    place->intersect(placeholder1);
    place->cf();

    if (cpplogEnabled(cpplogging::debug)) {
      print_sequent_placeCheck(std::cerr, step - 1, !place->emptiness(), zone, *place, placeholder1,
                               discrete_state, formula.getOpType());
      if (!place->emptiness()) {
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

inline bool prover::do_proof_place_ablewaitinf(const SubstList& discrete_state,
                                               const DBM& zone,
                                               DBMList* place) {
  DBMList ph(zone);
  if(place != nullptr) {
    ph.intersect(*place);
  }
  ph.cf();
  ph.suc();
  restrict_to_invariant(input_pes.invariants(), &ph, discrete_state);
  ph.cf();
  /* Time can diverge if and only if there are no upper bound
   * constraints in the successor. By design of succ() and invariants,
   * either all DBMs have an upper bound constraint, or none
   * of them do. Hence, checking the first is always good enough. */
  assert(!ph.getDBMList()->empty());
  DBM* firstDBM = *(ph.getDBMList()->begin());

  bool retVal = !firstDBM->hasUpperConstraint();
  if(!retVal && place != nullptr)
  {
    place->makeEmpty();
  }

  cpplog(cpplogging::debug)
      << "---(" << (retVal ? "V" : "Inv") << "alid) Time "
      << (retVal ? "" : "un")
      << "able to diverge to INFTY in current location---" << std::endl
      << std::endl;

  return retVal;
}

inline bool prover::do_proof_place_unablewaitinf(const SubstList& discrete_state,
                                                 const DBM& zone,
                                                 DBMList* place) {
  DBMList ph(zone);
  if(place != nullptr) {
    ph.intersect(*place);
  }
  ph.cf();
  ph.suc();
  restrict_to_invariant(input_pes.invariants(), &ph, discrete_state);
  ph.cf();
  /* Time cannot diverge if and only if there is an upper bound
   * constraint in the successor. By design of succ() and invariants,
   * either all DBMs have an upper bound constraint, or none
   * of them do. Hence, checking the first is always good enough. */
  assert(!ph.getDBMList()->empty());

  DBM* firstDBM = *(ph.getDBMList()->begin());
  bool retVal = firstDBM->hasUpperConstraint();
  if(!retVal && place != nullptr) {
    place->makeEmpty();
  }

  cpplog(cpplogging::debug)
      << "---(" << (retVal ? "V" : "Inv") << "alid) Time "
      << (retVal ? "un" : "")
      << "able to diverge to INFTY in current location---" << std::endl
      << std::endl;
  return retVal;
}

#endif /* PROOF_HH */
