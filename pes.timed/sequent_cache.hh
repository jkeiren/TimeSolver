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

#include "pes.hh"
#include "sequent_stack.hh"

class sequent_cache {
protected:
  const pes& input_pes;

  /** The maximum number of bits used in the hashing function
   * when storing discrete states. */
  int nbits;

  /** The size of the Hash table of Sequents: nBits + 1 */
  int nHash;

public:
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

  sequent_cache(const pes& input_pes, const int nbits, const int size,
                const int seqStSize)
      : input_pes(input_pes),
        nbits(nbits),
        nHash(seqStSize),
        Xlist_pGFP(input_pes.atomic().size(), nbits, size, seqStSize,
                   input_pes.predicates().size()),
        Xlist_pLFP(input_pes.atomic().size(), nbits, size, seqStSize,
                   input_pes.predicates().size()),
        Xlist_true(input_pes.atomic().size(), nbits, size, seqStSize,
                   input_pes.predicates().size()),
        Xlist_false(input_pes.atomic().size(), nbits, size, seqStSize,
                    input_pes.predicates().size()),
        Xlist_pGFP_ph(input_pes.atomic().size(), nbits, size, seqStSize,
                      input_pes.predicates().size()),
        Xlist_pLFP_ph(input_pes.atomic().size(), nbits, size, seqStSize,
                      input_pes.predicates().size()),
        Xlist_true_ph(input_pes.atomic().size(), nbits, size, seqStSize,
                      input_pes.predicates().size()),
        Xlist_false_ph(input_pes.atomic().size(), nbits, size, seqStSize,
                       input_pes.predicates().size()) {}

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
  bool look_for_and_purge_rhs_backStack(
      const std::vector<Sequent*>& initialPtr,
      const std::vector<SequentPlace*>& initialPlacePtr) {
    bool madeChange = false;

    /* Store a vector of stateBackList, where each sequent only has one DBM */

    /* Now iterate until the vector sequentQueue is empty,
     * purging backpointers and adding relevant ones in the queue */
    /* For now, implement purging with deques instead of vectors */
    std::deque<Sequent*> purgeSeqQueue(initialPtr.begin(), initialPtr.end());
    std::deque<SequentPlace*> purgeSeqPlaceQueue(initialPlacePtr.begin(),
                                                 initialPlacePtr.end());

    while (!(purgeSeqPlaceQueue.empty())) {
      SequentPlace* tp = purgeSeqPlaceQueue.front();

      int pInd =
          input_pes.lookup_predicate(tp->rhs()->getPredicate())->getIntVal() -
          1;
      /* Note: Purging parent sequents still ignores clock states. */

      /* Now purge the sequent and the DBM from all lists.
       * Circularity caches are correctly maintained; therefore,
       * they are not purged. */

      /* If found, Purge Sequent from its cache */
      bool b2 = Xlist_false_ph.look_for_and_purge_rhs_sequent_state(tp, pInd);
      bool b2b = Xlist_true_ph.look_for_and_purge_rhs_sequent_state(tp, pInd);

      /* Now find its backpointers to add to the queue
       * Only add backpointers to queue if something is purged. */
      if (b2 || b2b) {
        madeChange = true;
        // Now add sequents
        purgeSeqQueue.insert(purgeSeqQueue.end(), tp->parents().begin(),
                             tp->parents().end());
        purgeSeqPlaceQueue.insert(purgeSeqPlaceQueue.end(),
                                  tp->parents_with_placeholders().begin(),
                                  tp->parents_with_placeholders().end());
      }

      purgeSeqPlaceQueue.pop_front();
    }

    /* Now purge the original Sequents */
    while (!(purgeSeqQueue.empty())) {
      Sequent* t = purgeSeqQueue.front();

      int pInd =
          input_pes.lookup_predicate(t->rhs()->getPredicate())->getIntVal() - 1;
      /* Note: Purging parent sequents still ignores clock states */

      /* Now purge the sequent and the DBM from all lists.
       * Circularity caches are correctly maintained; therefore,
       * they are not purged. */
      bool b1 = Xlist_false.look_for_and_purge_rhs_sequent_state(t, pInd);
      /* If found, Purge Sequent from its cache */
      bool b1b = Xlist_true.look_for_and_purge_rhs_sequent_state(t, pInd);

      /* Now find its backpointers to add to the queue
       * Only add backpointers to queue if something is purged. */
      if (b1 || b1b) {
        madeChange = true;
        // Now add sequents
        purgeSeqQueue.insert(purgeSeqQueue.end(), t->parents().begin(),
                             t->parents().end());
        purgeSeqPlaceQueue.insert(purgeSeqPlaceQueue.end(),
                                  t->parents_with_placeholders().begin(),
                                  t->parents_with_placeholders().end());
      }

      purgeSeqQueue.pop_front();
    }
    // For now, do not remove backpointers from backList
    // This may be too conservative.

    return madeChange;
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
