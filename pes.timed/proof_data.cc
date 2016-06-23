/** \file proof_data.cc
 * Header file for auxiliary data structures used in the proofs.
 * @author Jeroen Keiren
 * @date June 22, 2016 */

#include "proof_data.hh"

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
Sequent * sequentStack::locate_sequent(Sequent * const s, int pInd){
  int indexH = hash_func(s->sub(), aSize, nbits);
  int index = pInd*seqStSize + indexH;
  for(stack::const_iterator it = Xlist[index].begin(); it != Xlist[index].end(); it++){
    Sequent *ls = (*it);
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
SequentPlace * sequentStackPlace::locate_sequentPlace(SequentPlace * const s, int pInd){
  int indexH = hash_func(s->sub(), aSize, nbits);
  int index = pInd*seqStSize + indexH;
  for(stackPlace::const_iterator it = Xlist[index].begin(); it != Xlist[index].end(); it++){
    SequentPlace *ls = (*it);
    bool matched = true;
    for(int j = 0; j < aSize; j++){
      if (s->sub()->at(j) != ls->sub()->at(j)){
        matched  = false;
        break;
      }
    }
    if (matched) {
      delete s;
      if(ls->dsp.size() == 0) {
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
Sequent * sequentStack::look_for_sequent(const SubstList * const subs, int pInd){
  int indexH = hash_func(subs, aSize, nbits);
  int index = pInd*seqStSize + indexH;
  for(stack::const_iterator it = Xlist[index].begin(); it != Xlist[index].end(); it++){
    Sequent *ls = (*it);
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
SequentPlace * sequentStackPlace::look_for_sequentPlace(const DBMList * const lhsPlace,
                                     const SubstList * const subs,
                                     const int pInd){
  int indexH = hash_func(subs, aSize, nbits);
  int index = pInd*seqStSize + indexH;
  for(stackPlace::const_iterator it = Xlist[index].begin(); it != Xlist[index].end(); it++){
    SequentPlace *ls = (*it);
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
Sequent * sequentStack::look_for_and_purge_rhs_sequent(const DBM* const lhs, const Sequent * const s,
                                         const int pInd,
                                         const bool tableCheck, bool * const madeEmpty){
  int indexH = hash_func(s->sub(), aSize, nbits);
  int index = pInd*seqStSize + indexH;
  bool matched = false;
  *madeEmpty = false;
  /* This assumes that location only locates one sequent in the stack */
  Sequent * foundSequent = NULL;
  for(stack::const_iterator it = Xlist[index].begin(); it != Xlist[index].end(); it++){
    Sequent *ls = (*it);
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
        for(DBMset::iterator itb = ls->ds.begin(); itb != ls->ds.end(); itb++) {
          if (*(*itb) >= *lhs) {
            // purge Here
            DBM* tmp = *itb;
            delete tmp;
            itb = ls->ds.erase(itb);
            itb--;
            foundSequent = ls;
          }
        }
      }
      else { //tableCheck is false
        for(DBMset::iterator itb = ls->ds.begin(); itb != ls->ds.end(); itb++) {
          if (*(*itb) <= *lhs) {
            // purge Here
            DBM* tmp = *itb;
            delete tmp;
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
SequentPlace * sequentStackPlace::look_for_and_purge_rhs_sequentPlace(const DBM * const lhs,
                                                   const DBMList * const lhsPlace,
                                                   SequentPlace const * const s,
                                                   const int pInd, const bool tableCheck,
                                                   bool * const madeEmpty){
  int indexH = hash_func(s->sub(), aSize, nbits);
  int index = pInd*seqStSize + indexH;
  bool matched = false;
  *madeEmpty = false;
  /* This assumes that location only locates one sequent in the stack */
  SequentPlace * foundSequent = NULL;
  for(stackPlace::iterator it = Xlist[index].begin(); it != Xlist[index].end(); it++){
    SequentPlace *ls = (*it);
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
        for(DBMPlaceSet::iterator itb = ls->dsp.begin(); itb != ls->dsp.end(); itb++) {
          /* Extra work for placeholders. For now,
           * force equality on LHS sequent and use tabling logic
           * for placeholders. */
          /* For now, ignore placeholders */
          //if (*((*itb).first) == *lhs && *((*itb).second) >= *lhsPlace) {
          if (*((*itb).first) == *lhs) {
            // purge Here
            DBM *lsB = (*itb).first;
            DBMList * lsListB = (*itb).second;
            delete lsB;
            delete lsListB;
            itb = ls->dsp.erase(itb);
            itb--;
            foundSequent = ls;
          }
        }
      }
      else { //tableCheck is false
        for(DBMPlaceSet::iterator itb = ls->dsp.begin(); itb != ls->dsp.end(); itb++) {
          /* Extra work for placeholders. For now,
           * force equality on LHS sequent and use tabling logic
           * for placeholders. */

          if (*((*itb).first) <= *lhs) {
            /* placeholder case for false sequents is special
             * because placeholders shrink for least fixpoints that may need to
             * be purged */
            // if (*((*itb).first) == *lhs) {
            //if (*((*itb).first) == *lhs && *((*itb).second) <= *lhsPlace) {
            // purge Here
            // Hence, we go through and delete DBMs
            DBM *lsB = (*itb).first;
            DBMList * lsListB = (*itb).second;
            delete lsB;
            delete lsListB;
            itb = ls->dsp.erase(itb);
            itb--;
            foundSequent = ls;
          }
        }

      }

      // Reset matched to delete only other matched purges
      matched = false;

    }

    // If sequent is empty, remove it from the list of sequents
    if((ls->dsp).empty()) {
      it = Xlist[index].erase(it);
      it--;
      *madeEmpty = true;

    }

  }
  // sequent not in list and thus no purging occurred.
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
bool sequentStack::look_for_and_purge_rhs_sequent_state(const Sequent * const s,
                                          const int pInd, const bool tableCheck) const {
  int indexH = hash_func(s->sub(), aSize, nbits);
  int index = pInd*seqStSize + indexH;
  bool matched = false;
  bool foundMatch = false;
  for(stack::iterator it = Xlist[index].begin(); it != Xlist[index].end(); it++){
    Sequent *ls = (*it);
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
      for(vector<DBM *>::const_iterator itB = ls->ds.begin();
          itB != ls->ds.end(); itB++) {
        DBM *lsB = (*itB);
        delete lsB;
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
bool sequentStackPlace::look_for_and_purge_rhs_sequentPlace_state(const SequentPlace * const s,
                                               const int pInd,
                                               const bool tableCheck) const {
  int indexH = hash_func(s->sub(), aSize, nbits);
  int index = pInd*seqStSize + indexH;
  bool matched = false;
  bool foundMatch = false;
  for(stackPlace::iterator it = Xlist[index].begin(); it != Xlist[index].end(); it++){
    SequentPlace *ls = (*it);
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
      // Hence, we go through and delete DBMs
      for(vector<pair<DBM*, DBMList *> >::iterator itB = ls->dsp.begin();
          itB != ls->dsp.end(); itB++) {
        DBM *lsB = (*itB).first;
        DBMList * lsListB = (*itB).second;
        delete lsB;
        delete lsListB;
      }
      ls->dsp.clear();
      delete ls;
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
void sequentStack::print_Xlist() const{
  int totNumSeq = 0;
  cout << "\t--For Each Sequence, Premise sets separated by \";\" --" << endl;
  for(int i = 0; i < predicateInd*(nbits+1); i++){
    for(stack::const_iterator it = Xlist[i].begin(); it != Xlist[i].end(); it++){
      int conseqNumSeq = 0;
      for(DBMset::const_iterator ie = (*it)->ds.begin(); ie != (*it)->ds.end(); ie++){
        (*ie)->print_constraint(get_clock_strings());
        conseqNumSeq++;
        totNumSeq++;
        cout << " ; ";
      }
      (*it)->sub()->print(cout);
      cout << "\t |- ";
      print_ExprNode((*it)->rhs(), cout);

      cout << " (" << conseqNumSeq;
      string tempStr;
      (conseqNumSeq == 1) ? (tempStr = "Premise") : (tempStr = "Premises" );
      cout << " "<< tempStr << " for this Consequent)";
      cout << endl;
    }
  }
  cout << "Total Number of Sequents: " << totNumSeq << endl;
}


/** Prints out all of the placeholder sequents in the list; the printing (for
 * ease of implementation) prints out the set of DBMs representing the set of
 * sequents with matching discrete location values and matching right hand
 * sides. Typically, the right hand sides will be predicate variables.
 * @param Xlist (*) The stack of placeholder sequents to print.
 * @return None. */
void sequentStackPlace::print_Xlist() const {
  int totNumSeq = 0;
  cout << "\t--For Each Sequence, Premise sets separated by \";\" --" << endl;
  for(int i = 0; i < predicateInd*(nbits+1); i++){
    for(stackPlace::const_iterator it = Xlist[i].begin(); it != Xlist[i].end(); it++){
      int conseqNumSeq = 0;
      for(DBMPlaceSet::iterator ie = (*it)->dsp.begin(); ie != (*it)->dsp.end(); ie++){
        (*ie).first->print_constraint(get_clock_strings());
        cout << ", plhold: ";
        (*ie).second->print_constraint(get_clock_strings());
        conseqNumSeq++;
        totNumSeq++;
        cout << " ; ";
      }
      (*it)->sub()->print(cout);
      cout << "\t |- ";
      print_ExprNode((*it)->rhs(), cout);

      cout << " (" << conseqNumSeq;
      string tempStr;
      (conseqNumSeq == 1) ? (tempStr = "Premise") : (tempStr = "Premises" );
      cout << " "<< tempStr << " for this Consequent)";
      cout << endl;
    }
  }
  cout << "Total Number of Sequents: " << totNumSeq << endl;
}