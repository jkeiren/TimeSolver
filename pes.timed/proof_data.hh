/** \file proof.hh
 * Header file for auxiliary data structures used in the proofs.
 * @author Jeroen Keiren
 * @date June 22, 2016 */

#ifndef PROOF_DATA_HH
#define PROOF_DATA_HH

#include "DBM.hh"
#include "DBMList.hh"
#include "ExprNode.hh"

/** Now define a stack of placeholder sequents.
 * Idea: Instead of intersecting the sequent with the placeholder,
 * store the sequents with placeholders separately. */
typedef std::vector<SequentPlace *> stackPlace;

/** This defines a DBMset as a vector of DBM
 * arrays (DBM Arrays). */
typedef std::vector<DBM*>  DBMset;

/** Defines a vector of (DBM, DBMList) pairs. Used for lists
 * of placeholder proofs, since (for faster performance) the union
 * of clock zones is restricted to placeholders. */
typedef std::vector<pair<DBM *, DBMList *> > DBMPlaceSet;

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
inline int hash_func(const SubstList * const sub, const int aSize, const int nbits){
  // From demo.7.cc (instead of from demo.cc) of previous code
  int sum = 0;
  for(int i=0; i<aSize; i++){
    sum += (sub->at(i) & nbits);
    sum = sum & nbits;
  }
  return sum;
}

class sequentStack
{

protected:
  /** This defines a stack as a vector of Sequent
   * arrays (Sequents). */
  typedef std::vector<Sequent*> stack;
  stack * Xlist;

  int aSize;
  int nbits;
  int size;
  int seqStSize;
  const int predicateInd;
  bool& newSequent;

public:

  sequentStack(const int aSize, const int nbits, const int size,
               const int seqStSize, const int predicateInd, bool& newSequent)
  : Xlist(new stack[size]), aSize(aSize), nbits(nbits), size(size),
          seqStSize(seqStSize), predicateInd(predicateInd), newSequent(newSequent)
  {}

  ~sequentStack()
  {
    for(int i = 0; i < size; i++) {
      // Now Iterate and delete for each vector
      for(stack::iterator it = Xlist[i].begin(); it != Xlist[i].end(); it++) {
        Sequent *ls = (*it);
        delete ls;
      }
    }
    delete[] Xlist;
  }


  /** Looks in a cache of sequents (the stack Xlist) for the right hand side
   * and discrete state of the input partial sequent; returns a found sequent, and
   * makes a new sequent in the specified stack if it is not found. This
   * method is only used for sequents of predicate variable right hand sided.
   * Because this method both finds a sequent and to adds it into a cache, it
   * makes an unfound sequent (for efficiency). To merely return if no sequent is
   * found, use look_for_sequent(...) instead. The returned partial sequent is
   * then examined for the desired clock state (with tabled_sequent()).
   * @param s (*) The sequent; only its discrete state is examined, but the entire
   * sequent is added if not found.
   * @param Xlist (*) The cache of sequents to look in.
   * @param pInd The index of the predicate; used to find the proper hashing bin.
   * @return The reference to the sequent with the three components
   * specified as parameters. */
  Sequent * locate_sequent(Sequent * const s, int pInd);

  /** Looks in a cache of sequents (the stack Xlist)
   * for the right hand side
   * and discrete state of the input partial sequent; returns a found sequent, and
   * returns NULL if no such sequent is found. This
   * method is only used for sequents of predicate variable right hand sided.
   * The returned partial sequent is
   * then examined for the desired clock state (with tabled_sequent()).
   * @param subs (*) The discrete state of the sequent.
   * @param Xlist (*) The cache of sequents to look in.
   * @param pInd The index of the predicate; used to find the proper hashing bin.
   * @return The reference to the sequent with the three components
   * specified as parameters. */
  Sequent * look_for_sequent(const SubstList * const subs, int pInd);

  /** Given a sequent cache and using the clock state lhs and the
   * discrete state in s, looks for the sequent, and purges it
   * from the cache if it finds it. By assumption, the right
   * hand side of Sequent s is the predicate variable specified
   * by pInd. This method returns the purged sequent if found,
   * and NULL otherwise. By design of the caches, there should be at most one
   * such sequent in the cache to purge. This is used to look for and purge
   * previously cached
   * (known true) or (known false) sequents to detect a caching mistake
   * or a change in truth of a sequent.
   * @param lhs (*) The DBM of the sequent
   * @param s (*) The sequent (its discrete state is most important)
   * @param Xlist (&*) The sequent cache to examine
   * @param pInd The index of the predicate; used to find the proper hashing bin.
   * @param tableCheck The boolean indicating whether to table for false sequents
   * (make false) or true sequents (make true).  If tableCheck = true, then we are
   * aiming to purge sequents cached as true but discovered to be false. Likewise,
   * if tableCheck = false, then we are aiming to purge sequents cached as
   * false but discovered to be true.
   * @param (*) madeEmpty A reference to a boolean in order that the function
   * can change it to true if the found sequent was deleted from the list.
   * @return The pointer to the purged sequent, or
   * NULL if no sequent was purged.*/
  Sequent * look_for_and_purge_rhs_sequent(const DBM* const lhs, const Sequent * const s,
                                           const int pInd,
                                           const bool tableCheck, bool * const madeEmpty);

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
   * @param pInd The index of the predicate; used to find the proper hashing bin.
   * @param tableCheck The boolean indicating whether to table for false sequents
   * (make false) or true sequents (make true).  If tableCheck = true, then we are
   * aiming to purge sequents cached as true but discovered to be false. Likewise,
   * if tableCheck = false, then we are aiming to purge sequents cached as
   * false but discovered to be true.
   * @return true: one or more sequents were purged; false: otherwise.*/
  bool look_for_and_purge_rhs_sequent_state(const Sequent * const s,
                                            const int pInd, const bool tableCheck) const;

  /** Prints out all of the sequents in the list; the printing (for
   * ease of implementation) prints out the set of DBMs representing the set of
   * sequents with matching discrete location values and matching right hand
   * sides. Typically, the right hand sides will be predicate variables.
   * @param Xlist (*) The stack of sequents to print.
   * @return None. */
  void print_Xlist() const;

};

class sequentStackPlace
{

protected:
  /** This defines a stack as a vector of Sequent
   * arrays (Sequents). */
  typedef std::vector<SequentPlace*> stackPlace;
  stackPlace * Xlist;

  int aSize;
  int nbits;
  int size;
  int seqStSize;
  const int predicateInd;
  bool& newSequent;

public:

  sequentStackPlace(const int aSize, const int nbits, const int size,
                    const int seqStSize, const int predicateInd, bool& newSequent)
  : Xlist(new stackPlace[size]), aSize(aSize), nbits(nbits), size(size),
    seqStSize(seqStSize), predicateInd(predicateInd), newSequent(newSequent)
  {}

  ~sequentStackPlace()
  {
    for(int i = 0; i < size; i++) {
      // Now Iterate and delete for each vector
      for(stackPlace::iterator it = Xlist[i].begin(); it != Xlist[i].end(); it++) {
        SequentPlace *ls = (*it);
        delete ls;
      }
    }
    delete[] Xlist;
  }

  /** Looks in a cache of placeholder sequents (the stack Xlist)
   * for the right hand side
   * and discrete state of the input partial sequent; returns a found sequent, and
   * makes a new sequent in the specified stack if it is not found. This
   * method is only used for sequents of predicate variable right hand sided.
   * Because this method both finds a sequent and to adds it into a cache, it
   * makes an unfound sequent (for efficiency). To merely return if no sequent is
   * found, use look_for_sequent(...) instead. The returned partial sequent is
   * then examined for the desired clock state (with tabled_sequent()).
   * @param s (*) The sequent with placeholders; only its discrete state is
   * examined, but the entire sequent is added if not found.
   * @param Xlist (*) The cache of placeholder sequents to look in.
   * @param pInd The index of the predicate; used to find the proper hashing bin.
   * @return The reference to the sequent with the three components
   * specified as parameters. */
  SequentPlace * locate_sequentPlace(SequentPlace * const s, int pInd);


  /** Looks in a cache of placeholder sequents (the stack Xlist)
   * for the right hand side
   * and discrete state of the input partial sequent; returns a found sequent, and
   * returns NULL if no such sequent is found. This
   * method is only used for sequents of predicate variable right hand sided.
   * The returned partial sequent is
   * then examined for the desired clock state (with tabled_sequent()).
   * @param lhsPlace (*) The placeholder DBM.
   * @param subs (*) The discrete state of the sequent with placeholders.
   * @param Xlist (*) The cache of placeholder sequents to look in.
   * @param pInd The index of the predicate; used to find the proper hashing bin.
   * @return The reference to the sequent with the three components
   * specified as parameters. */
  SequentPlace * look_for_sequentPlace(const DBMList * const lhsPlace,
                                       const SubstList * const subs,
                                       const int pInd);


  /** Given a placeholder sequent cache and using the clock state (lhs,
   * lhsPlace) and the
   * discrete state in s, looks for the placeholder sequent, and purges it
   * from the cache if it finds it. By assumption, the right
   * hand side of Sequent s is the predicate variable specified
   * by pInd. This method returns the purged sequent if found,
   * and NULL otherwise. By design of the caches, there should be at most one
   * such sequent in the cache to purge. This is used to look for and purge
   * previously cached
   * (known true) or (known false) sequents to detect a caching mistake
   * or a change in truth of a sequent.
   * @param lhs (*) The DBM of the sequent.
   * @param lhsPlace (*) The DBMList placeholder in the sequent.
   * @param s (*) The placeholder sequent (its discrete state is most important)
   * @param Xlist (&*) The placeholder sequent cache to examine
   * @param pInd The index of the predicate; used to find the proper hashing bin.
   * @param tableCheck The boolean indicating whether to table for false sequents
   * (make false) or true sequents (make true).  If tableCheck = true, then we are
   * aiming to purge sequents cached as true but discovered to be false. Likewise,
   * if tableCheck = false, then we are aiming to purge sequents cached as
   * false but discovered to be true.
   * @param (*) madeEmpty A reference to a boolean in order that the function
   * can change it to true if the found sequent was deleted from the list.
   * @return The pointer to the purged sequent, or
   * NULL if no sequent was purged.*/
  SequentPlace * look_for_and_purge_rhs_sequentPlace(const DBM * const lhs,
                                                     const DBMList * const lhsPlace,
                                                     SequentPlace const * const s,
                                                     const int pInd, const bool tableCheck,
                                                     bool * const madeEmpty);



  /** Given a placeholder sequent cache and
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
   * @param s (*) The placeholder sequent (its discrete state is most important)
   * @param Xlist (&*) The placeholder sequent cache to examine
   * @param pInd The index of the predicate; used to find the proper hashing bin.
   * @param tableCheck The boolean indicating whether to table for false sequents
   * (make false) or true sequents (make true).  If tableCheck = true, then we are
   * aiming to purge sequents cached as true but discovered to be false. Likewise,
   * if tableCheck = false, then we are aiming to purge sequents cached as
   * false but discovered to be true.
   * @return true: one or more sequents were purged; false: otherwise.*/
  bool look_for_and_purge_rhs_sequentPlace_state(const SequentPlace * const s,
                                                 const int pInd,
                                                 const bool tableCheck) const;



  /** Prints out all of the placeholder sequents in the list; the printing (for
   * ease of implementation) prints out the set of DBMs representing the set of
   * sequents with matching discrete location values and matching right hand
   * sides. Typically, the right hand sides will be predicate variables.
   * @param Xlist (*) The stack of placeholder sequents to print.
   * @return None. */
  void print_Xlist() const;

};

#endif
