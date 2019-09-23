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

#include "pes.h"
#include "DBM.h"
#include "DBMList.h"
#include "ExprNode.h"
#include "sequent.h"

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

  /* Make this protected eventually */
  int predicate_index(const ExprNode& formula) const
  {
    assert(formula.getOpType() == PREDICATE);
    return m_input_pes.lookup_predicate(formula.getPredicate())->getIntVal() - 1;
  }

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
      delete_vector_elements(stack);
    }
  }

  /* Add a sequent to the cache.
   * pre: there is no sequent for discrete_state, formula in the cache,
   *      i.e. find_sequent(discrete_state, formula) returns nullptr.
   */
  SequentType* add_sequent(const SubstList& discrete_state,
                           const ExprNode& formula) {

    assert(find_sequent(discrete_state, formula) == nullptr);
    const std::size_t index = get_index(discrete_state, formula);
    Xlist[index].emplace_back(new SequentType(&formula, &discrete_state));

    cpplog(cpplogging::debug1, "sequent_stack") << "Added new sequent " << *Xlist[index].back() << " to sequent stack" << std::endl;

    return Xlist[index].back();
  }

  /** Looks in a cache of sequents (the stack Xlist) for the right hand side
   * and discrete state of the input partial sequent; returns a found sequent,
   * and makes a new sequent in the specified stack if it is not found. This
   * method is only used for sequents of predicate variable right hand sided.
   * Because this method both finds a sequent and to adds it into a cache, it
   * makes an unfound sequent (for efficiency). To merely return if no sequent
   * is found, use find_sequent(...) instead. The returned partial sequent
   * is then examined for the desired clock state (with tabled_sequent()).
   * @param s (*) The sequent; only its discrete state is examined, but the
   * entire sequent is added if not found.
   * @param pInd The index of the predicate; used to find the proper hashing
   * bin.
   * @return The reference to the sequent with the three components
   * specified as parameters. */
  SequentType* find_sequent_else_add(const SubstList& discrete_state,
                              const ExprNode& formula) {
    assert(formula.getOpType() == PREDICATE);
    SequentType* result = find_sequent(discrete_state, formula);
    if (result != nullptr) {
      return result;
    } else {
      return add_sequent(discrete_state, formula);
    }
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
  SequentType* find_sequent(const SubstList& discrete_state,
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
    typename stack_t::const_iterator it = std::find_if(
          Xlist[index].begin(), Xlist[index].end(),
          [&discrete_state](const SequentType* s) {
            return discrete_state == *(s->discrete_state());
          });

    SequentType* foundSequent = nullptr;
    *madeEmpty = false;

    if(it != Xlist[index].end()) {
      for (typename DBMsetType::iterator itb = (*it)->dbm_set().begin();
           itb != (*it)->dbm_set().end(); ++itb) {
        if ((tableCheck && match_for_purging_tabled(*itb, *getDBM(elt)))
            || (!tableCheck && *getDBM(*itb) <= *getDBM(elt))) {
          // purge Here
          delete_DBMset_elt(*itb);
          itb = (*it)->dbm_set().erase(itb);
          itb--;
          foundSequent = (*it);
        }
      }

      // If sequent is empty, remove it from the list of sequents
      if ((*it)->dbm_set().empty()) {
        Xlist[index].erase(it);
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
   * @param s (*) The sequent (its discrete state is most important)
   */
  void look_for_and_purge_rhs_sequent_state(const SequentType* const sequent) {
    const SubstList& discrete_state = *(sequent->discrete_state());
    const ExprNode& formula = *(sequent->rhs());

    const std::size_t index = get_index(discrete_state, formula);
    typename stack_t::const_iterator it = std::find_if(
          Xlist[index].begin(), Xlist[index].end(),
          [&discrete_state](const SequentType* s) {
            return discrete_state == *(s->discrete_state());
          });

    if(it != Xlist[index].end()) {
      (*it)->delete_sequents();
      delete (*it);
      Xlist[index].erase(it);
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
