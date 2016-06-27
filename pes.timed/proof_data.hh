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

typedef DBM* DBMsetElt;

/** This defines a DBMset as a vector of DBM
 * arrays (DBM Arrays). */
typedef std::vector<DBMsetElt>  DBMset;

typedef std::pair<DBM *, DBMList *> DBMPlaceSetElt;
/** Defines a vector of (DBM, DBMList) pairs. Used for lists
 * of placeholder proofs, since (for faster performance) the union
 * of clock zones is restricted to placeholders. */
typedef std::vector<DBMPlaceSetElt> DBMPlaceSet;

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

template <typename SequentType, typename DBMsetElementType>
class sequentStackT
{

protected:
  /** This defines a stack as a vector of Sequent
   * arrays (Sequents). */
  typedef std::vector<SequentType*> stack;
  typedef std::vector<DBMsetElementType> DBMsetType;
  stack * Xlist;

  int aSize;
  int nbits;
  int size;
  int seqStSize;
  const int predicateInd;
  bool& newSequent;

  // Comparison for look_for_and_purge_rhs_sequent
  bool match_for_purging_tabled(DBM* fst, const DBM& snd)
  {
    return *fst <= snd;
  }

  // Comparison for look_for_and_purge_rhs_sequent
  bool match_for_purging_tabled(const std::pair<DBM*, DBMList*>& fst, const DBM& snd)
  {
    return *(fst.first) == snd;
  }

  /** print the elements pointed to by the components of p */
  void print_DBMset_elt(std::ostream& os, const std::pair<const DBM * const, const DBMList * const>& p) const
  {
    p.first->print_constraint(os, get_clock_strings());
    os << ", plhold: ";
    p.second->print_constraint(os, get_clock_strings());
  }

  /** delete the elements pointed to by the components of p */
  void delete_DBMset_elt(const std::pair<DBM *, DBMList *>& p)
  {
    delete p.first;
    delete p.second;
  }

  DBM* getDBM(const std::pair<DBM*, DBMList*>& p) const
  {
    return p.first;
  }

  /** print the element pointed to by p */
  void print_DBMset_elt(std::ostream& os, const DBM * const p) const
  {
    p->print_constraint(os, get_clock_strings());
  }

  /** delete the element pointed to by p */
  void delete_DBMset_elt(DBM * p)
  {
    delete p;
  }

  DBM* getDBM(DBM * p) const
  {
    return p;
  }

public:

  sequentStackT(const int aSize, const int nbits, const int size,
               const int seqStSize, const int predicateInd, bool& newSequent)
  : Xlist(new stack[size]), aSize(aSize), nbits(nbits), size(size),
          seqStSize(seqStSize), predicateInd(predicateInd), newSequent(newSequent)
  {}

  ~sequentStackT()
  {
    for(int i = 0; i < size; i++) {
      // Now Iterate and delete for each vector
      for(typename stack::iterator it = Xlist[i].begin(); it != Xlist[i].end(); it++) {
        SequentType *ls = (*it);
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
  SequentType * locate_sequent(SequentType * const s, int pInd)
  {
    int indexH = hash_func(s->sub(), aSize, nbits);
    int index = pInd*seqStSize + indexH;
    for(typename stack::const_iterator it = Xlist[index].begin(); it != Xlist[index].end(); it++){
      SequentType *ls = (*it);
      bool matched = true;
      for(int j = 0; j < aSize; j++){
        if (s->sub()->at(j) != ls->sub()->at(j)){
          matched  = false;
          break;
        }
      }
      if (matched) {
        delete s;
        if(ls->ds.size() == 0) {
          newSequent = true;
        }
        else {
          newSequent = false;
        }
        return ls;
      }
    }
    /* Sequent not found; add it to the cache.
     * (This is why we must take in the entire Sequent s as a parameter
     * and not just its sublist component.) */
    newSequent = true;
    Xlist[index].push_back(s);
    return (Xlist[index].back());
  }

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
  SequentType * look_for_sequent(const SubstList * const subs, int pInd){
    int indexH = hash_func(subs, aSize, nbits);
    int index = pInd*seqStSize + indexH;
    for(typename stack::const_iterator it = Xlist[index].begin(); it != Xlist[index].end(); it++){
      SequentType *ls = (*it);
      bool matched = true;
      for(int j = 0; j < aSize; j++){
        if (subs->at(j) != ls->sub()->at(j)){
          matched  = false;
          break;
        }
      }
      if (matched) {
        // Found the Sequent, return it
        return ls;
      }
    }
    // sequent not in structure, so return NULL.
    return NULL;
  }

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
  SequentType * look_for_and_purge_rhs_sequent(const DBMsetElementType elt,
               const SequentType * const s,
               const int pInd,
               const bool tableCheck, bool * const madeEmpty){
    int indexH = hash_func(s->sub(), aSize, nbits);
    int index = pInd*seqStSize + indexH;
    bool matched = false;
    *madeEmpty = false;
    /* This assumes that location only locates one sequent in the stack */
    SequentType * foundSequent = NULL;
    for(typename stack::const_iterator it = Xlist[index].begin(); it != Xlist[index].end(); it++){
      SequentType *ls = (*it);
      matched = true;

      for(int j = 0; j < aSize; j++){
        if (s->sub()->at(j) != ls->sub()->at(j)){
          matched  = false;
          break;
        }
      }

      /* For Now, purge the LHS Possibilities
       * that are in line with the proper "tabling"
       * or containment, which are specified by
       * the tableCheck Boolean */
      if(matched == true){
        // Now Iterate on the Tabled Sequents
        /* Key Concept of Purging:
         * If Was True (tableCheck is true), discovered false, check that
         *		Z_now_false <= Z_cached_true | or | Z_cached_true >= Z_now_false
         * If Was False (tableCheck is false), discovered true, check that
         *		Z_now_true >= Z_cached_false | or | Z_cached_false <= Z_now_true
         * This Must be done regardless of how the tabling
         * is done for that specific cache */
        if(tableCheck) {
          for(typename DBMsetType::iterator itb = ls->ds.begin(); itb != ls->ds.end(); itb++) {
            // JK: there is an interesting difference in the handling of DBMs in the
            // cases without and with placeholders.
            // without placeholders we use the comparison
            // *(*itb) >= *lhs)
            // with placeholders we compare
            // *(*itb).first) == *lhs
            // this is handled in match_for_purgin_tabled
            if (match_for_purging_tabled(*itb, *getDBM(elt))) {
              // purge Here
              delete_DBMset_elt(*itb);
              itb = ls->ds.erase(itb);
              itb--;
              foundSequent = ls;
            }
          }
        }
        else { //tableCheck is false
          for(typename DBMsetType::iterator itb = ls->ds.begin(); itb != ls->ds.end(); itb++) {
            if (*getDBM(*itb) <= *getDBM(elt)) {
              // purge Here
              delete_DBMset_elt(*itb);
              itb = ls->ds.erase(itb);
              itb--;
              foundSequent = ls;
            }
          }

        }

        // Reset matched to delete only other matched purges
        matched = false;

      }

      // If sequent is empty, remove it from the list of sequents
      if((ls->ds).empty()) {
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
   * @param pInd The index of the predicate; used to find the proper hashing bin.
   * @param tableCheck The boolean indicating whether to table for false sequents
   * (make false) or true sequents (make true).  If tableCheck = true, then we are
   * aiming to purge sequents cached as true but discovered to be false. Likewise,
   * if tableCheck = false, then we are aiming to purge sequents cached as
   * false but discovered to be true.
   * @return true: one or more sequents were purged; false: otherwise.*/
  bool look_for_and_purge_rhs_sequent_state(const SequentType * const s,
                    const int pInd, const bool tableCheck) {
    int indexH = hash_func(s->sub(), aSize, nbits);
    int index = pInd*seqStSize + indexH;
    bool matched = false;
    bool foundMatch = false;
    for(typename stack::iterator it = Xlist[index].begin(); it != Xlist[index].end(); it++){
      SequentType *ls = (*it);
      matched = true;

      for(int j = 0; j < aSize; j++){
        if (s->sub()->at(j) != ls->sub()->at(j)){
          matched  = false;
          break;
        }
      }

      /* For Now, purge the LHS Possibilities
       * that are in line with the proper "tabling"
       * or containment, which are specified by
       * the tableCheck Boolean */
      if(matched == true){
        /* Key Concept of Purging:
         * If Was True (tableCheck is true), discovered false, check that
         *		Z_now_false <= Z_cached_true | or | Z_cached_true >= Z_now_false
         * If Was False (tableCheck is false), discovered true, check that
         *		Z_now_true >= Z_cached_false | or | Z_cached_false <= Z_now_true
         * This Must be done regardless of how the tabling
         * is done for that specific cache */
        // Potential memory leak: may need to go through and delete DBMs
        // Iterate Through and Delete every element of ds
        for(typename DBMsetType::iterator itB = ls->ds.begin();
            itB != ls->ds.end(); itB++) {
          delete_DBMset_elt(*itB);
        }
        ls->ds.clear();
        delete ls; // This line causes some problems
        // If sequent is empty, remove it from the list of sequents
        /* Since deleting all DBM sequents in purging (aggressive: usually
         * over purges), just erase the list. */
        it = Xlist[index].erase(it);
        it--;

        // Reset matched to delete only other matched purges
        matched = false;
        
      }
      
    }
    // sequent not in list and thus no purging occurred.
    return foundMatch;
  }

  /** Prints out all of the sequents in the list; the printing (for
   * ease of implementation) prints out the set of DBMs representing the set of
   * sequents with matching discrete location values and matching right hand
   * sides. Typically, the right hand sides will be predicate variables.
   * @param Xlist (*) The stack of sequents to print.
   * @return None. */
  void print_Xlist(std::ostream& os) const {
    int totNumSeq = 0;
    os << "\t--For Each Sequence, Premise sets separated by \";\" --" << endl;
    for(int i = 0; i < predicateInd*(nbits+1); i++){
      for(typename stack::const_iterator it = Xlist[i].begin(); it != Xlist[i].end(); it++){
        int conseqNumSeq = 0;
        for(typename DBMsetType::const_iterator ie = (*it)->ds.begin(); ie != (*it)->ds.end(); ie++){
          print_DBMset_elt(os, *ie);
          conseqNumSeq++;
          totNumSeq++;
          os << " ; ";
        }
        (*it)->sub()->print(os);
        os << "\t |- ";
        print_ExprNode((*it)->rhs(), os);

        os << " (" << conseqNumSeq;
        string tempStr;
        (conseqNumSeq == 1) ? (tempStr = "Premise") : (tempStr = "Premises" );
        os << " "<< tempStr << " for this Consequent)";
        os << endl;
      }
    }
    os << "Total Number of Sequents: " << totNumSeq << endl;
  }

};

typedef sequentStackT<Sequent, DBMsetElt> sequentStack;
typedef sequentStackT<SequentPlace, DBMPlaceSetElt> sequentStackPlace;

#endif
