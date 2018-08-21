/**
  * Caches for sequents. Used in the prover to detect cycles in fixed-points,
  * and to cache known-true and known-false sequents.
  *
  * @author Peter Fontana
  * @author Dezhuang Zhang
  * @author Rance Cleaveland
  * @author Jeroen Keiren
  * @copyright MIT Licence, see the accompanying LICENCE.txt
  */


#ifndef SEQUENT_CACHE_HH
#define SEQUENT_CACHE_HH

#include <deque>
#include "pes.hh"
#include "sequent_stack.hh"

class sequent_cache {
public:

  // Determine whether the predicate is cached as a known false sequent
  bool is_known_false_sequent(const SubstList& discrete_state,
                              const DBM& zone,
                              const ExprNode& formula,
                              Sequent* parentRef)
  {
    Sequent* cached_sequent =
        Xlist_false.look_for_sequent(discrete_state, formula);
    if (cached_sequent != nullptr &&
        cached_sequent->tabled_false_sequent(zone)) {
      /* Add backpointer to parent sequent (shallow copy) */
      cached_sequent->addParent(parentRef);
      return true;
    }
    return false;
  }

  // Determine whether the predicate is cached as a known true sequent
  bool is_known_true_sequent(const SubstList& discrete_state,
                              const DBM& zone,
                              const ExprNode& formula,
                              Sequent* parentRef)
  { // Restricted scope for looking up true sequents
    Sequent* cached_sequent =
        Xlist_true.look_for_sequent(discrete_state, formula);
    if (cached_sequent != nullptr && cached_sequent->tabled_sequent(zone)) {
      /* Add backpointer to parent sequent (shallow copy) */
      cached_sequent->addParent(parentRef);
      return true;
    }
    return false;
  }

  void cache_true_sequent(const SubstList& discrete_state,
                          const DBM& zone,
                          const ExprNode& formula)
  {
    Sequent* cached_true_sequent =
        Xlist_true.locate_sequent(discrete_state, formula);
    cached_true_sequent->update_sequent(zone);
  }

  void cache_false_sequent(const SubstList& discrete_state,
                          const DBM& zone,
                          const ExprNode& formula)
  {
    Sequent* cached_false_sequent =
        Xlist_false.locate_sequent(discrete_state, formula);
    cached_false_sequent->update_false_sequent(zone);
  }

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
  /** XList_false is an array of stacks of sequents that
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

  sequent_cache(const pes& input_pes,
                const std::size_t num_hashing_bins)
      : Xlist_pGFP(input_pes, num_hashing_bins),
        Xlist_pLFP(input_pes, num_hashing_bins),
        Xlist_true(input_pes, num_hashing_bins),
        Xlist_false(input_pes, num_hashing_bins),
        Xlist_pGFP_ph(input_pes, num_hashing_bins),
        Xlist_pLFP_ph(input_pes, num_hashing_bins),
        Xlist_true_ph(input_pes, num_hashing_bins),
        Xlist_false_ph(input_pes, num_hashing_bins)
  {}

  /** Purge backpointers from all caches. Purging occurrs
   * until no sequent was purged (not purging a sequent indicates that
   * no further sequents need to be purged). For performance
   * efficiency, this method passes pointers to vectors.
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

  void look_for_and_purge_rhs_backStack(std::deque<Sequent*>& purgeSeqQueue) {
    /* Now purge the original Sequents */
    while (!(purgeSeqQueue.empty())) {
      Sequent* t = purgeSeqQueue.front();

      /* Note: Purging parent sequents still ignores clock states */

      /* Now purge the sequent and the DBM from all lists.
       * Circularity caches are correctly maintained; therefore,
       * they are not purged. */
      Xlist_false.look_for_and_purge_rhs_sequent_state(t);
      /* If found, Purge Sequent from its cache */
      Xlist_true.look_for_and_purge_rhs_sequent_state(t);

      purgeSeqQueue.pop_front();
    }
  }

  void look_for_and_purge_rhs_backStackPlace(std::deque<SequentPlace*>& purgeSeqPlaceQueue) {
    while (!(purgeSeqPlaceQueue.empty())) {
      SequentPlace* tp = purgeSeqPlaceQueue.front();

      /* Note: Purging parent sequents still ignores clock states. */

      /* Now purge the sequent and the DBM from all lists.
       * Circularity caches are correctly maintained; therefore,
       * they are not purged. */

      /* If found, Purge Sequent from its cache */
      Xlist_false_ph.look_for_and_purge_rhs_sequent_state(tp);
      Xlist_true_ph.look_for_and_purge_rhs_sequent_state(tp);

      purgeSeqPlaceQueue.pop_front();
    }
  }

  void look_for_and_purge_rhs_backStack(const std::vector<Sequent*>& initialPtr) {
    std::deque<Sequent*> purgeSeqQueue(initialPtr.begin(), initialPtr.end());
    look_for_and_purge_rhs_backStack(purgeSeqQueue);
  }

  void look_for_and_purge_rhs_backStack(
      const std::vector<Sequent*>& initialPtr,
      const std::vector<SequentPlace*>& initialPlacePtr) {

    /* Store a vector of stateBackList, where each sequent only has one DBM */

    /* Now iterate until the vector sequentQueue is empty,
     * purging backpointers and adding relevant ones in the queue */
    /* For now, implement purging with deques instead of vectors */
    std::deque<Sequent*> purgeSeqQueue(initialPtr.begin(), initialPtr.end());
    std::deque<SequentPlace*> purgeSeqPlaceQueue(initialPlacePtr.begin(),
                                                 initialPlacePtr.end());

    look_for_and_purge_rhs_backStackPlace(purgeSeqPlaceQueue);
    look_for_and_purge_rhs_backStack(purgeSeqQueue);
  }

  void printTabledSequents(std::ostream& os) const {
    /* If in DEBUG Mode, print out list of Tabled Sequents */
    os << std::endl;
    os << "##--Debug Info: Tabled Sequents===============" << std::endl;
    os << "----GFP Cached Sequents---------" << std::endl;
    Xlist_pGFP.print_Xlist(os);
    // os << "Number of GFP Sequents Tabled: " std::endl;
    os << std::endl;
    os << "----LFP Cached Sequents---------" << std::endl;
    Xlist_pLFP.print_Xlist(os);
    os << std::endl;
    os << "----Known False Cached Sequents---------" << std::endl;
    Xlist_false.print_Xlist(os);
    os << std::endl;
    os << "----Known True Cached Sequents---------" << std::endl;
    Xlist_true.print_Xlist(os);
    os << std::endl;
    os << "##--Debug Info: Tabled Placeholder Sequents==========" << std::endl;
    os << "----GFP Placeholder Cached Sequents---------" << std::endl;
    Xlist_pGFP_ph.print_Xlist(os);
    // os << "Number of GFP Sequents Tabled: " std::endl;
    os << std::endl;
    os << "----LFP Placeholder Cached Sequents---------" << std::endl;
    Xlist_pLFP_ph.print_Xlist(os);
    os << std::endl;
    os << "----Known False (Placeholder) Cached Sequents---------" << std::endl;
    Xlist_false_ph.print_Xlist(os);
    os << std::endl;
    os << "----Known True (Placeholder) Cached Sequents---------" << std::endl;
    Xlist_true_ph.print_Xlist(os);
  }
};

#endif // SEQUENT_CACHE_HH
