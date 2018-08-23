/** \file sequent_stack.hh
 * Sequent stack, used as basis for caching.
 * @author Peter Fontana
 * @author Dezhuang Zhang
 * @author Rance Cleaveland
 * @author Jeroen Keiren
 * @copyright MIT Licence, see the accompanying LICENCE.txt
 */

#ifndef SEQUENT_STACK_HH
#define SEQUENT_STACK_HH

#include "pes.hh"
#include "DBM.hh"
#include "DBMList.hh"
#include "ExprNode.hh"
#include "sequent.hh"

/** Stack of sequents used to detect, among others, cycles of fixed points */
template <typename SequentType, typename DBMsetElementType, typename DBMsetConstElementType>
class sequentStackT {
protected:
  /** This defines a stack as a vector of Sequent
   * arrays (Sequents). */
  typedef std::vector<SequentType*> stack_t;
  typedef std::vector<DBMsetElementType> DBMsetType;

  const pes& m_input_pes;
  const std::size_t m_num_hash_bins; // number of hashing bins
  const std::size_t m_atomic_size; // number of atomics in PES.
  const std::size_t m_size; // size of stack_t;
  const std::size_t m_hash_bitmask; // bitmask for hashing
  const std::size_t m_predicates_size; // number of predicates in PES.

  // Maps indices of predicate variables to maps of discrete state -> SequentType*.
  std::vector<stack_t> Xlist; // Vector of vectors (stacks)

  /** Provide the hash function to hash atomic (discrete location) variables
   * into bins; it gives a hash bin per SubstList (
   * discrete location representation).
   * Sufficient bins are given so each predicate variable has its
   * own bins (hashing does not collide on predicate variables); this is
   * for optimized performance, since the number of predicates is usually small.
   * Given the possibly large number of discrete states, hashing is used
   * to save space.
   * @param sub (*) The discrete state to hash into a bin.
   * @return The hashed bin index for that discrete state.*/
  std::size_t hash(const SubstList& discrete_state) const {
    // From demo.7.cc (instead of from demo.cc) of previous code
    std::size_t sum = 0;
    for (std::size_t i = 0; i < m_atomic_size; i++) {
      sum += (discrete_state.at(i) & m_hash_bitmask);
      sum = sum & m_hash_bitmask;
    }
    return sum;
  }

  /** Get the right index into the stack */
  std::size_t get_index(const SubstList& discrete_state,
                const ExprNode& formula) const {
    return predicate_index(formula) * m_num_hash_bins + hash(discrete_state);
  }

  // Comparison for look_for_and_purge_rhs_sequent
  constexpr bool match_for_purging_tabled(const DBM* fst, const DBM& snd) const {
    return *fst >= snd;
  }

  // Comparison for look_for_and_purge_rhs_sequent
  constexpr bool match_for_purging_tabled(const std::pair<const DBM*, const DBMList*>& fst,
                                const DBM& snd) const {
    return *(fst.first) == snd;
  }

  /** print the elements pointed to by the components of p */
  void print_DBMset_elt(
      std::ostream& os,
      const std::pair<const DBM* const, const DBMList* const>& p) const {
    os << p.first << ", plhold: " << p.second;
  }

  /** delete the elements pointed to by the components of p */
  void delete_DBMset_elt(const std::pair<DBM*, DBMList*>& p) {
    delete p.first;
    delete p.second;
  }

  constexpr DBM* getDBM(const std::pair<DBM*, DBMList*>& p) const { return p.first; }

  constexpr const DBM* getDBM(const std::pair<const DBM*, const DBMList*>& p) const { return p.first; }

  /** print the element pointed to by p */
  void print_DBMset_elt(std::ostream& os, const DBM* const p) const { os << p; }

  /** delete the element pointed to by p */
  void delete_DBMset_elt(DBM* p) { delete p; }

  constexpr DBM* getDBM(DBM* p) const { return p; }

  constexpr const DBM* getDBM(const DBM* p) const { return p; }

public:
  sequentStackT(const pes& input_pes, const std::size_t num_hash_bins)
      : m_input_pes(input_pes),
        m_num_hash_bins(num_hash_bins),
        m_atomic_size(input_pes.atomic()->size()),
        m_size(input_pes.predicates().size() * num_hash_bins),
        m_hash_bitmask(num_hash_bins-1),
        m_predicates_size(input_pes.predicates().size()),
        Xlist(m_size, stack_t()) {
    assert(is_power_of_two(m_num_hash_bins));
  }

  ~sequentStackT() {
    for (stack_t& stack : Xlist) {
      // Now Iterate and delete for each vector
      delete_vector_elements(stack);
    }
  }

  /* Make this protected eventually */
  int predicate_index(const ExprNode& formula) const
  {
    assert(formula.getOpType() == PREDICATE);
    return m_input_pes.lookup_predicate(formula.getPredicate())->getIntVal() - 1;
  }

  /** Looks in a cache of sequents (the stack Xlist) for the right hand side
   * and discrete state of the input partial sequent; returns a found sequent,
   * and makes a new sequent in the specified stack if it is not found. This
   * method is only used for sequents of predicate variable right hand sided.
   * Because this method both finds a sequent and to adds it into a cache, it
   * makes an unfound sequent (for efficiency). To merely return if no sequent
   * is found, use look_for_sequent(...) instead. The returned partial sequent
   * is then examined for the desired clock state (with tabled_sequent()).
   * @param s (*) The sequent; only its discrete state is examined, but the
   * entire sequent is added if not found.
   * @param pInd The index of the predicate; used to find the proper hashing
   * bin.
   * @return The reference to the sequent with the three components
   * specified as parameters. */
  SequentType* locate_sequent(const SubstList& discrete_state,
                              const ExprNode& formula) {
    assert(formula.getOpType() == PREDICATE);

    SequentType* result = look_for_sequent(discrete_state, formula);
    if (result == nullptr) {
      /* Sequent not found; add it to the cache.
       * (This is why we must take in the entire Sequent s as a parameter
       * and not just its sublist component.) */
      const std::size_t index = get_index(discrete_state, formula);
      Xlist[index].emplace_back(new SequentType(&formula, &discrete_state));
      result = Xlist[index].back();
      cpplog(cpplogging::debug1, "sequent_stack") << "Added new sequent " << *result << " to sequent stack" << std::endl;
    }
    return result;
  }

  /** Looks in a cache of sequents (the stack Xlist)
   * for the right hand side
   * and discrete state of the input partial sequent; returns a found sequent,
   * and returns nullptr if no such sequent is found. This method is only used for
   * sequents of predicate variable right hand sided. The returned partial
   * sequent is then examined for the desired clock state (with
   * tabled_sequent()).
   * @param subs (*) The discrete state of the sequent.
   * @param pInd The index of the predicate; used to find the proper hashing
   * bin.
   * @return The reference to the sequent with the three components
   * specified as parameters. */
  SequentType* look_for_sequent(const SubstList& discrete_state,
                                const ExprNode& formula) const {
    cpplog(cpplogging::debug1, "sequent_stack") << "Locating (" << discrete_state << ", ___) |- " << formula << " in sequent stack" << std::endl;
    const std::size_t index = get_index(discrete_state, formula);
    typename stack_t::const_iterator it = std::find_if(
          Xlist[index].begin(), Xlist[index].end(),
          [&discrete_state](const SequentType* s) {
            return discrete_state == *(s->discrete_state());
          });
    return (it == Xlist[index].end()) ? nullptr : *it;
  }

  /** Given a sequent cache and using the clock state lhs and the
   * discrete state in s, looks for the sequent, and purges it
   * from the cache if it finds it. By assumption, the right
   * hand side of Sequent s is the predicate variable specified
   * by pInd. This method returns the purged sequent if found,
   * and nullptr otherwise. By design of the caches, there should be at most one
   * such sequent in the cache to purge. This is used to look for and purge
   * previously cached
   * (known true) or (known false) sequents to detect a caching mistake
   * or a change in truth of a sequent.
   * @param lhs (*) The DBM of the sequent
   * @param s (*) The sequent (its discrete state is most important)
   * @param Xlist (&*) The sequent cache to examine
   * @param pInd The index of the predicate; used to find the proper hashing
   * bin.
   * @param tableCheck The boolean indicating whether to table for false
   * sequents (make false) or true sequents (make true).  If tableCheck = true,
   * then we are aiming to purge sequents cached as true but discovered to be
   * false. Likewise, if tableCheck = false, then we are aiming to purge
   * sequents cached as false but discovered to be true.
   * @param (*) madeEmpty A reference to a boolean in order that the function
   * can change it to true if the found sequent was deleted from the list.
   * @return The pointer to the purged sequent, or
   * nullptr if no sequent was purged.*/
  SequentType* look_for_and_purge_rhs_sequent(const DBMsetConstElementType elt,
                                              const SubstList& discrete_state,
                                              const ExprNode& formula,
                                              const bool tableCheck,
                                              bool* const madeEmpty) {
    const std::size_t index = get_index(discrete_state, formula);
    *madeEmpty = false;
    /* This assumes that location only locates one sequent in the stack */
    SequentType* foundSequent = nullptr;

    for (typename stack_t::const_iterator it = Xlist[index].begin();
         it != Xlist[index].end(); it++) {
      SequentType* ls = (*it);

      /* For Now, purge the LHS Possibilities
       * that are in line with the proper "tabling"
       * or containment, which are specified by
       * the tableCheck Boolean */
      if (discrete_state == *(ls->discrete_state())) {
        assert(foundSequent == nullptr);
        // Now Iterate on the Tabled Sequents
        /* Key Concept of Purging:
         * If Was True (tableCheck is true), discovered false, check that
         *		Z_now_false <= Z_cached_true | or | Z_cached_true >=
         *Z_now_false If Was False (tableCheck is false), discovered true, check
         *that Z_now_true >= Z_cached_false | or | Z_cached_false <= Z_now_true
         * This Must be done regardless of how the tabling
         * is done for that specific cache */

        for (typename DBMsetType::iterator itb = ls->dbm_set().begin();
             itb != ls->dbm_set().end(); ++itb) {
          if ((tableCheck && match_for_purging_tabled(*itb, *getDBM(elt)))
              || *getDBM(*itb) <= *getDBM(elt)) {
            // purge Here
            delete_DBMset_elt(*itb);
            itb = ls->dbm_set().erase(itb);
            itb--;
            foundSequent = ls;
          }
        }

        // If sequent is empty, remove it from the list of sequents
        if ((ls->dbm_set()).empty()) {
          it = Xlist[index].erase(it);
          it--;
          *madeEmpty = true;
        }
      }
    }

    return foundSequent;
  }

  /** Given a sequent cache and
   * discrete state in s, look for the sequent, and purge
   * all sequents with the same predicate index pInd and discrete state.
   * In order to purge backpointers quickly, clock state comparisons
   * are avoided and all clock states of potential backpointers
   * are conservatively purged (the proofs are still sound and complete).
   * By assumption, the right
   * hand side of Sequent s is the predicate variable specified
   * by pInd. This method returns true if one or more sequents are
   * purged and false otherwise. The caller uses a false return value
   * to indicate that no further purging is needed (guarantees finite
   * termination).
   * @param s (*) The sequent (its discrete state is most important)
   * @param Xlist (&*) The sequent cache to examine
   * @param pInd The index of the predicate; used to find the proper hashing
   * bin.
   * @param tableCheck The boolean indicating whether to table for false
   * sequents (make false) or true sequents (make true).  If tableCheck = true,
   * then we are aiming to purge sequents cached as true but discovered to be
   * false. Likewise, if tableCheck = false, then we are aiming to purge
   * sequents cached as false but discovered to be true.
   * @return true: one or more sequents were purged; false: otherwise.*/
  void look_for_and_purge_rhs_sequent_state(const SequentType* const sequent) {
    const SubstList& discrete_state = *(sequent->discrete_state());
    const ExprNode& formula = *(sequent->rhs());

    const std::size_t index = get_index(discrete_state, formula);
    for (typename stack_t::iterator it = Xlist[index].begin();
         it != Xlist[index].end(); it++) {
      SequentType* ls = (*it);

      /* For Now, purge the LHS Possibilities
       * that are in line with the proper "tabling"
       * or containment, which are specified by
       * the tableCheck Boolean */
      if (discrete_state == *(ls->discrete_state())) {
        /* Key Concept of Purging:
         * If Was True (tableCheck is true), discovered false, check that
         *		Z_now_false <= Z_cached_true | or | Z_cached_true >=
         *Z_now_false If Was False (tableCheck is false), discovered true, check
         *that Z_now_true >= Z_cached_false | or | Z_cached_false <= Z_now_true
         * This Must be done regardless of how the tabling
         * is done for that specific cache */
        // Potential memory leak: may need to go through and delete DBMs
        // Iterate Through and Delete every element of ds
        ls->delete_sequents();
        delete ls; // This line causes some problems
        // If sequent is empty, remove it from the list of sequents
        /* Since deleting all DBM sequents in purging (aggressive: usually
         * over purges), just erase the list. */
        it = Xlist[index].erase(it);
        it--;
        return;
      }
    }
  }

  /** Prints out all of the sequents in the list; the printing (for
   * ease of implementation) prints out the set of DBMs representing the set of
   * sequents with matching discrete location values and matching right hand
   * sides. Typically, the right hand sides will be predicate variables.
   * @param Xlist (*) The stack of sequents to print.
   * @return None. */
  void print_Xlist(std::ostream& os) const {
    int totNumSeq = 0;
    os << "\t--For Each Sequence, Premise sets separated by \";\" --"
       << std::endl;
    for (std::size_t i = 0; i < m_size; ++i) {
      for (typename stack_t::const_iterator it = Xlist[i].begin();
           it != Xlist[i].end(); it++) {
        int conseqNumSeq = 0;
        for (typename DBMsetType::const_iterator ie = (*it)->dbm_set().begin();
             ie != (*it)->dbm_set().end(); ie++) {
          print_DBMset_elt(os, *ie);
          conseqNumSeq++;
          totNumSeq++;
          os << " ; ";
        }
        (*it)->discrete_state()->print(os);
        os << "\t |- " << *((*it)->rhs());

        os << " (" << conseqNumSeq;
        std::string tempStr;
        (conseqNumSeq == 1) ? (tempStr = "Premise") : (tempStr = "Premises");
        os << " " << tempStr << " for this Consequent)";
        os << std::endl;
      }
    }
    os << "Total Number of Sequents: " << totNumSeq << std::endl;
  }
};

typedef sequentStackT<Sequent, DBM*, const DBM*> sequentStack;
typedef sequentStackT<SequentPlace, std::pair<DBM *, DBMList *>, std::pair<const DBM *, const DBMList *>> sequentStackPlace;

#endif // SEQUENT_STACK_HH
