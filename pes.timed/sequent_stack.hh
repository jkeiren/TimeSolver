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
  stack_t* Xlist; // Array of vectors (stacks)

  const std::size_t atomic_size; // number of atomics in PES.
  const int nbits;
  const int size; // size of stack_t;
  const int seqStSize;
  const int predicates_size; // number of predicates in PES.

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
  int hash_func(const SubstList* const sub, const std::size_t atomic_size,
                const int nbits) const {
    // From demo.7.cc (instead of from demo.cc) of previous code
    int sum = 0;
    for (std::size_t i = 0; i < atomic_size; i++) {
      sum += (sub->at(i) & nbits);
      sum = sum & nbits;
    }
    return sum;
  }

  /** Get the right index into the stack */
  int get_index(const SubstList* const discrete_state,
                const int predicate_index) const {
    return predicate_index * seqStSize +
           hash_func(discrete_state, atomic_size, nbits);
  }

  // Comparison for look_for_and_purge_rhs_sequent
  constexpr bool match_for_purging_tabled(const DBM* fst, const DBM& snd) const {
    return *fst <= snd;
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
  sequentStackT(const std::size_t aSize, const int nbits, const int size,
                const int seqStSize, const int predicateInd)
      : Xlist(new stack_t[size]),
        atomic_size(aSize),
        nbits(nbits),
        size(size),
        seqStSize(seqStSize),
        predicates_size(predicateInd) {}

  ~sequentStackT() {
    for (int i = 0; i < size; i++) {
      // Now Iterate and delete for each vector
      delete_vector_elements(Xlist[i]);
    }
    delete[] Xlist;
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
  SequentType* locate_sequent(SequentType* const sequent,
                              int predicate_index,
                              bool& newSequent) const {
    SequentType* ls = look_for_sequent(sequent->discrete_state(), predicate_index);
    SequentType* result = nullptr;
    if (ls == nullptr) {
      /* Sequent not found; add it to the cache.
       * (This is why we must take in the entire Sequent s as a parameter
       * and not just its sublist component.) */
      const int index = get_index(sequent->discrete_state(), predicate_index);
      Xlist[index].push_back(sequent);
      result = Xlist[index].back();
    } else {
      delete sequent;
      result = ls;
    }
    newSequent = (ls == nullptr || ls->dbm_set().empty());
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
   * @param Xlist (*) The cache of sequents to look in.
   * @param pInd The index of the predicate; used to find the proper hashing
   * bin.
   * @return The reference to the sequent with the three components
   * specified as parameters. */
  SequentType* look_for_sequent(const SubstList* const discrete_state,
                                int predicate_index) const {
    const int index = get_index(discrete_state, predicate_index);
    typename stack_t::const_iterator it = std::find_if(
          Xlist[index].begin(), Xlist[index].end(),
          [&discrete_state](const SequentType* s) {
            return *discrete_state == *(s->discrete_state());
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
                                              const SequentType* const sequent,
                                              const int predicate_index,
                                              const bool tableCheck,
                                              bool* const madeEmpty) {
    const int index = get_index(sequent->discrete_state(), predicate_index);
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
      if (*sequent->discrete_state() == *(ls->discrete_state())) {
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
      }

      // If sequent is empty, remove it from the list of sequents
      if ((ls->dbm_set()).empty()) {
        it = Xlist[index].erase(it);
        it--;
        *madeEmpty = true;
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
  void look_for_and_purge_rhs_sequent_state(const SequentType* const sequent,
                                            const int predicate_index) {
    int index = get_index(sequent->discrete_state(), predicate_index);
    for (typename stack_t::iterator it = Xlist[index].begin();
         it != Xlist[index].end(); it++) {
      SequentType* ls = (*it);

      /* For Now, purge the LHS Possibilities
       * that are in line with the proper "tabling"
       * or containment, which are specified by
       * the tableCheck Boolean */
      if (*sequent->discrete_state() == *(ls->discrete_state())) {
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
    for (int i = 0; i < predicates_size * (nbits + 1); i++) {
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
