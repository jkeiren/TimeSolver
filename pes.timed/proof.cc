/** \file proof.hh
 * Header file for proof
 * @author Peter Fontana, Dezhuang Zhang, and Rance Cleaveland.
 * @version 1.21
 * @date June 21, 2016 */

#include "proof_data.hh"
#include "proof.hh"

using namespace std;

#define DEBUG true

bool prover::do_proof_predicate(int step, DBM* const lhs, const ExprNode* const rhs, SubstList* const sub)
{
  bool retVal = false;

  ExprNode *e = input_pes.lookup_equation(rhs->getPredicate());
  if (e == NULL){
    cerr << "open predicate variable found: "<< rhs->getPredicate()<<endl;
    exit(-1);
  }

  // Get Predicate Index for Hashing
  int pInd = input_pes.lookup_predicate(rhs->getPredicate())->getIntVal() - 1;
  prevParityGfp = currParityGfp;
  currParityGfp = rhs->get_Parity();
  lhs->cf();

  /* Look in Known True and Known False Sequent Caches */
  if(useCaching) {
    /* First look in known False Sequent table */
    Sequent *tf = new Sequent(rhs, sub);
    Sequent *hf = Xlist_false.look_for_sequent(tf->sub(), pInd);
    if(hf != NULL && tabled_false_sequent(hf, lhs)) {
      retVal = false;
#if DEBUG
      if (debug) {
        cout << "---(Invalid) Located a Known False Sequent ----" << endl << endl;
      }
#endif


      /* Add backpointer to parent sequent (shallow copy) */
      hf->parSequent.push_back(parentRef);
      if(tf != hf) {
        delete tf;
      }
      return retVal; // break out of switch
    }
    if(tf != hf) {
      delete tf;
    }

    /* Now look in known True Sequent table */
    Sequent *tfb = new Sequent(rhs, sub); //JK Can be optimised out by reusing tf?
    Sequent *hfb = Xlist_true.look_for_sequent(tfb->sub(), pInd);
    if(hfb != NULL && tabled_sequent(hfb, lhs)) {
      retVal = true;
#if DEBUG
      if (debug) {
        cout << "---(Valid) Located a Known True Sequent ----" << endl << endl;
      }
#endif
      /* Add backpointer to parent sequent (shallow copy) */
      hfb->parSequent.push_back(parentRef);
      if(tfb != hfb) {
        delete tfb;
      }
      return retVal; // break out of switch
    }
    if(tfb != hfb) {
      delete tfb;
    }
  }

  /* Now deal with greatest fixpoint circularity and least
   * fixpoint circularity */

  Sequent *t = new Sequent(rhs, sub);
  Sequent *h;
  if(currParityGfp) { // Thus a Greatest Fixpoint
    h = Xlist_pGFP.locate_sequent(t, pInd);
    if((!newSequent) && tabled_sequent(h, lhs)) {
      // Found gfp Circularity - thus valid
      retVal = true;
#if DEBUG
      if (debug) {
        cout << "---(Valid) Located a True Sequent or gfp Circularity ----" << endl << endl;
      }
#endif
      /* Add backpointer to parent sequent (shallow copy) */
      h->parSequent.push_back(parentRef);

      // Add sequent to known true cache
      if(useCaching) {
        Sequent *t7 = new Sequent(rhs, sub);
        Sequent *h7 = Xlist_true.locate_sequent(t7, pInd);
        update_sequent(h7, lhs);
      }
      return retVal;
    }

    h->ds.push_back(new DBM(*lhs));
  }
  else { // Thus, a least fixpoint
    // Now look for a Circularity
    h = Xlist_pLFP.locate_sequent(t, pInd);
    if((!newSequent) && tabled_sequent_lfp(h, lhs)) {
      // Found lfp circularituy - thus invalid
      retVal = false;
#if DEBUG
      if (debug) {
        cout << "---(Invalid) Located a lfp Circularity ----" << endl << endl;
      }
#endif

      /* Add backpointer to parent sequent (shallow copy) */
      h->parSequent.push_back(parentRef);

      // Now Put Sequent in False Cache
      if(useCaching) {
        Sequent *t7 = new Sequent(rhs, sub);
        Sequent *h7 = Xlist_false.locate_sequent(t7, pInd);
        update_false_sequent(h7, lhs);
      }
      return retVal;
    }

    h->ds.push_back(new DBM(*lhs));
  }

  // NO CIRCULARITY FOUND

  /* Assign parent value after caching since during caching we may have
   * to use the previous parent */
  Sequent * tempParentState = parentRef;
  /* Get the current variable: do a shallow, not deep copy */
  parentRef = h;

  retVal = do_proof(step, lhs, e, sub);

  lhs->cf();

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
  if(useCaching && retVal) {
    /* First look in opposite parity Caches */
    Sequent *t2 = new Sequent(rhs, sub);
    Sequent *t2s;
    bool madeEmpty = false;
    /* If found, Purge Sequent from its cache */
    t2s = Xlist_false.look_for_and_purge_rhs_sequent(lhs, t2, pInd, false, &madeEmpty);


    /* Now purge backpointers */
    if(t2s != NULL) {
      look_for_and_purge_rhs_backStack(&(t2s->parSequent),
                                       &(t2s->parSequentPlace));

    }
    // Now update in proper Cache
    Sequent *t5 = new Sequent(rhs, sub);
    Sequent *h5 = Xlist_true.locate_sequent(t5, pInd);
    update_sequent(h5, lhs);

    // Now make deletions for Memory Cleanup
    if(t2 != t2s) {
      delete t2;
    }
    if(madeEmpty) {
      delete t2s;
    }



  }
  else if(useCaching) {
    /* True cache (not gfp caches) */
    Sequent *t22 = new Sequent(rhs, sub);
    Sequent *t22s;
    bool madeEmpty = false;
    /* If found, Purge Sequent from its cache */
    t22s = Xlist_true.look_for_and_purge_rhs_sequent(lhs, t22, pInd, true, &madeEmpty);


    /* Now purge backpointers.
     * Ignore circularity booleans because they do not form backpointers */
    if(t22s != NULL) {

      look_for_and_purge_rhs_backStack(&(t22s->parSequent),
                                       &(t22s->parSequentPlace));

    }
    // Now update in proper Cache
    Sequent *t5 = new Sequent(rhs, sub);
    Sequent *h5 = Xlist_false.locate_sequent(t5, pInd);
    update_false_sequent(h5, lhs);

    // Now make deletions for Memory Cleanup
    if( t22 != t22s) {
      delete t22;
    }
    if(madeEmpty) {
      delete t22s;
    }
  }

  /* The line: h->parSequent.push_back(parentRef);
   * is not needed since the backpointer stored before proof. */

  DBM * tempDBM = h->ds.back();
  delete tempDBM;
  h->ds.pop_back();
  return retVal;
}

bool prover::do_proof_and(int step, DBM * const lhs, const ExprNode * const rhs, SubstList * const sub)
{
  /* Because lhs is only changed after it is copied, it can
   * be passed to both branches. */
  bool retVal = do_proof(step, lhs, rhs->getLeft(), sub);
  if(retVal == true) {
    retVal = do_proof(step, lhs, rhs->getRight(), sub);
  }
  return retVal;
}

bool prover::do_proof_or(int step, DBM * const lhs, const ExprNode * const rhs, SubstList * const sub)
{
  bool retVal = false;

  /* Use two placeholders to provide split here */
  DBMList place1(*INFTYDBM);
  retPlaceDBM = do_proof_place(step, lhs, &place1, rhs->getLeft(), sub);
  retPlaceDBM->cf();
  // Reset place parent to NULL
  parentPlaceRef = NULL;
  if(retPlaceDBM->emptiness()) {
    retVal = do_proof(step, lhs, rhs->getRight(), sub);
  }
  else if(*retPlaceDBM >= *lhs) {
    retVal = true;
  }
  else {
    /* Here we get the corner case where we have to use the
     * OR Split rule */
    place1 = *retPlaceDBM;
    DBMList place2(*INFTYDBM);
    retPlaceDBM = do_proof_place(step, lhs, &place2, rhs->getRight(), sub);
    retPlaceDBM->cf();

    // Reset place parent to NULL
    parentPlaceRef = NULL;
    if(retPlaceDBM->emptiness()) {
      retVal = false;
    }
    else if(*retPlaceDBM >= *lhs) {
      retVal = true;
    }
    else {
      retPlaceDBM->addDBMList(place1);
      retVal = (*retPlaceDBM) >= *lhs;
    }
  }
  return retVal;
}

bool prover::do_proof_or_simple(int step, DBM * const lhs, const ExprNode * const rhs, SubstList * const sub)
{
  /* Simplified OR does not need to split on placeholders */
  bool retVal = do_proof(step, lhs, rhs->getLeft(), sub);
  // Reset place parent to NULL
  if(!retVal) {
    DBM lhsb(*lhs);
    retVal  = do_proof(step, &lhsb, rhs->getRight(), sub);
  }
  return retVal;
}

bool prover::do_proof_forall(int step, DBM * const lhs, const ExprNode * const rhs, SubstList * const sub)
{
  /* Here the model checker looks at the zone of
   * all time sucessors and then substitutes in
   * the substitued constraints and sees if the
   * zone satifies the constraints */
  lhs->cf();
  /* DBM lhs is copied because it is changed by suc() and invs_chk().
   * The copying here assures that lhs is unchanged when it is returned,
   * allowing multiple branches of AND and OR to have the same lhs. */
  DBM ph(*lhs);
  ph.suc();
  invs_chk(input_pes.invariants(), &ph, *sub);

  return do_proof(step, &ph, rhs->getQuant(), sub);
}

bool prover::do_proof_forall_rel(int step, DBM * const lhs, const ExprNode * const rhs, SubstList * const sub)
{
  /* Proof methodology:
   * first, see if \phi_1 is satisfied during the time advance.
   * If it is, check that phi_2 is true both at and before those
   * times (time predecessor).
   * If this is not satisfactory, then do a regular FORALL proof
   * without a placeholder. */

  bool retVal = false;

  /* First, see if \exists(phi_1) is true. The common case is that it
   * will not be. */
  lhs->cf();
  DBM ph(*lhs);
  ph.suc();

  DBMList * tPlace = new DBMList(*INFTYDBM);
  invs_chk(input_pes.invariants(), tPlace, *sub);
  retPlaceDBM = do_proof_place(step, &ph, tPlace,
                               rhs->getLeft(), sub);
  // Reset place parent to NULL
  parentPlaceRef = NULL;
  retPlaceDBM->cf();
  if(retPlaceDBM->emptiness()){
    if (debug) {
      print_sequentCheck(cout, step - 1, retVal, lhs, retPlaceDBM, sub, rhs->getOpType());

      cout <<"----() Empty Relativization Placeholder: phi1 is never true -----" << endl << endl;
    }
    delete tPlace;
    /* Since here, \forall phi_2 must be true */
    lhs->cf();
    /* DBM lhs is copied because it is changed by suc() and invs_chk().
     * The copying here assures that lhs is unchanged when it is returned,
     * allowing multiple branches of AND and OR to have the same lhs. */
    DBM ph(*lhs);
    ph.suc();
    invs_chk(input_pes.invariants(), &ph, *sub);

    retVal = do_proof(step, &ph, rhs->getRight(), sub);
  }
  else {
    /* For improved performance, first ask if the formula
     * is true with no time elapse. */
    retVal = true;
    /* First check for the simplest case: no time elapse is needed */
    if((*retPlaceDBM) >= (*lhs)) {

#if DEBUG
      if (debug) {
        print_sequentCheck(cout, step - 1, retVal, lhs, retPlaceDBM, sub, rhs->getOpType());
        cout <<"----(Valid) Placeholder indicates no time elapse is needed (Check Only)-----" << endl
        << "----With Placeholder := {";
        retPlaceDBM->print_constraint(cout);
        cout << "} ----"<< endl << endl;

      }
#endif

      // If here, we neither need a placeholder nor to elapse time
      DBM phb(*lhs);
      retVal = do_proof(step, &phb, rhs->getRight(), sub);
    }
    else {
      // This is the more complicated case that requires a placeholder
      // for the FORALL
      /* Now check that we can elapse to the placeholder. */
      // Store the set of times that satisfy phi1
      DBMList phi1Place(*retPlaceDBM);

#if DEBUG
      if (debug) {
        cout <<"----() Relativization \\phi_1 placeholder obtained as {";
        phi1Place.print_constraint(cout);
        cout << "} ----"<< endl << endl;

      }
#endif

      /* We omit the check that we can elapse to the placeholder;
       * We will check that once at the end */
      DBMList *fPlace = new DBMList(*INFTYDBM);
      DBM ph(*lhs);
      ph.suc();
      DBM phb(ph);
      retPlaceDBM = do_proof_place(step, &phb, fPlace,
                                   rhs->getRight(), sub);
      retPlaceDBM->cf();
      DBMList phi2Place(*retPlaceDBM);
#if DEBUG
      if (debug) {
        cout <<"----() Formula \\phi_2 placeholder obtained as {";
        phi2Place.print_constraint(cout);
        cout << "} ----"<< endl << endl;

      }
#endif
      // Reset place parent to NULL
      parentPlaceRef = NULL;
      if(retPlaceDBM->emptiness()) {
        retVal = false;
      }
      else if ((*retPlaceDBM) >= ph) {
        /* In this simple case, all possible times satisfy \phi_2
         * so we can avoid many checks. */
        retVal = true;

      }
      else {
        /* Now do a succ check on phi_2 to get \phi_forall
         * and a predCheck using both phi_1 and phi_2 to get phi_exists */
        /* we also note that the times satisfying \phi_1
         * (the relativization formula condition) are neither empty
         * nor everything. */

        DBMList invCompPlace(*INFTYDBM);
        bool hasInv = invs_chk(input_pes.invariants(), &invCompPlace, *sub);
        if(hasInv) {
          invCompPlace.cf();
          !invCompPlace;
          invCompPlace.cf();
          retPlaceDBM->addDBMList(invCompPlace);
          retPlaceDBM->cf();
        }

        DBMList currPlace(*retPlaceDBM);
        retPlaceDBM = succCheckRule(lhs, &currPlace);
        retPlaceDBM->cf();
        DBMList forallPlace(*retPlaceDBM);

#if DEBUG
        if (debug) {
          print_sequentCheck(cout, step - 1, retVal, &phb, fPlace, sub, rhs->getOpType());
          cout <<"----() FORALL (of FORALL_REL) Placeholder Check obtained  FA Placeholder := {";
          forallPlace.print_constraint(cout);
          cout <<"} ----" << endl << endl;
        }
#endif

        /* Now we do the pred check to find the exists placeholder;
         * This involves the predCheck method and checking that time can
         * can elapse. Note that the exists is a simplified version
         * where \phi_2 (the right) is the relativized clause and
         * \phi_1 (the left) is the formula. By using the placeholders
         * computed previously, we save time by not having to recompute
         * the formulas. */
        DBMList currRetPlaceDBM(*retPlaceDBM);
        DBMList * phi1PredPlace = new DBMList(phi1Place);
        phi1PredPlace->pre();
        phi1PredPlace->cf();
        /*--- PredCheck code----*/
        retPlaceDBM = predCheckRule(lhs, &ph, NULL, &phi2Place, &phi1Place, phi1PredPlace);
        retPlaceDBM->cf();
#if DEBUG
        if(debug) {
          cout <<"----() FORALL Rel Exists predCheck placeholder obtained as := {";
          retPlaceDBM->print_constraint(cout);
          cout << "} ----"<< endl << endl;
        }
#endif
        if(retPlaceDBM->emptiness()) {

        }
        else {
          /* if it is nonempty, it passes the second check and we continue
           * Given the FORALL rule rewrite, do not allow the instance
           * after the time elapse */
          /* Extract the new refined placeholder. */
          *retPlaceDBM & phi1Place;
          retPlaceDBM->cf();


          /* Now check that it works. */
          /* Since we are not using retPlace anymore, we do not
           * need to copy it for the check. */
          retPlaceDBM->pre();
          /* This cf() is needed. */
          retPlaceDBM->cf();
          // Need we intersect this with succ(Gamma) or
          // do we need to perform an elapse check?
          // what if this is empty?
#if DEBUG
          if (debug) {
            print_sequentCheck(cout, step - 1, retVal, lhs, retPlaceDBM, sub, rhs->getOpType());

            cout <<"----() FORALL Rel Exists placeholder after time elapse check is := {";
            retPlaceDBM->print_constraint(cout);
            cout << "} ----"<< endl << endl;
          }
#endif
        }
        // retPlaceDBM is existsPlace
        /* Last, we do an or check on the two placeholders */
        bool forallEmpty = forallPlace.emptiness();
        bool existsEmpty = retPlaceDBM->emptiness();
        if(forallEmpty && existsEmpty) {
          retPlaceDBM->makeEmpty();
          retVal = false;
        }
        else { // nested else to handle case when retPlaceDBM is empty
          if(forallEmpty) {

          }
          else if (existsEmpty) {
            *retPlaceDBM = forallPlace;
          }
          else {
            if(forallPlace <= *retPlaceDBM) {

            }
            else if (*retPlaceDBM <= forallPlace) {
              *retPlaceDBM = forallPlace;
            }
            else {
              /* This case requires us to union the two placeholders. */
              retPlaceDBM->addDBMList(forallPlace);
            }
          }
          retVal = *retPlaceDBM >= *lhs;
        }
        // Debug information here?
#if DEBUG
        if (debug) {
          print_sequentCheck(cout, step - 1, retVal, lhs, retPlaceDBM, sub, rhs->getOpType());
          cout <<"----() Final FORALL REL Placeholder is := {";
          retPlaceDBM->print_constraint(cout);
          cout << "} ----"<< endl << endl;
        }
#endif
        delete phi1PredPlace;
      }
      delete fPlace;

    }
    delete tPlace;
  }
  return retVal;
}

bool prover::do_proof_exists(int step, DBM * const lhs, const ExprNode * const rhs, SubstList * const sub)
{
  bool retVal = false;

  /* Support for exists(), written by Peter Fontana */
  // This support gives a placeholder variable
  // and uses a similar method do_proof_place
  // which recursively uses (slightly more complex rules)
  // to solve for the placeholders.

  /* First Try to get a placeholder value that works */
  lhs->cf();
  DBM ph(*lhs);
  ph.suc();


  /* The proper derivation for EXISTS is to incorporate the invariant
   * in the placeholder, and not the LHS. */
  DBMList tPlace(*INFTYDBM);
  invs_chk(input_pes.invariants(), &tPlace, *sub);

  retPlaceDBM = do_proof_place(step, &ph, &tPlace,
                               rhs->getQuant(), sub);
  // Reset place parent to NULL
  parentPlaceRef = NULL;
  retPlaceDBM->cf();
  if(retPlaceDBM->emptiness()){
    retVal = false;
    if (debug) {
      print_sequentCheck(cout, step - 1, retVal, lhs, retPlaceDBM, sub, rhs->getOpType());

      cout <<"----(Invalid) Empty Placeholder: No Need for Placeholder Check-----" << endl << endl;
    }
    return retVal;
  }
  retVal = true;
  /* Now check that it works. */
  /* Since we are not using retPlace anymore, we do not
   * need to copy it for the check. */
  retPlaceDBM->pre();
  /* This cf() is needed. */
  retPlaceDBM->cf();
  retVal = (*retPlaceDBM) >= (*lhs);

#if DEBUG
  if (debug) {
    print_sequentCheck(cout, step - 1, retVal, lhs, retPlaceDBM, sub, rhs->getOpType());
    if(retVal) {
      cout <<"----(Valid) Placeholder Check Passed (Check Only)-----" << endl
      << "----With Placeholder := {";
      retPlaceDBM->print_constraint(cout);
      cout << "} ----"<< endl << endl;

    }
    else {
      cout <<"----(Invalid) Placeholder Check Failed-----" << endl << endl;

    }
  }
#endif
  return retVal;
}

bool prover::do_proof_exists_rel(int step, DBM * const lhs, const ExprNode * const rhs, SubstList * const sub)
{
  bool retVal = false;

  /* First Try to get a placeholder value that works */
  lhs->cf();
  DBM ph(*lhs);
  // Note: lhs is unchanged
  ph.suc();
  DBM phb(ph);

  DBMList * tPlace = new DBMList(*INFTYDBM);
  invs_chk(input_pes.invariants(), tPlace, *sub);

  retPlaceDBM = do_proof_place(step, &ph, tPlace,
                               rhs->getRight(), sub);
  // Reset place parent to NULL
  parentPlaceRef = NULL;
  retPlaceDBM->cf();
  if(retPlaceDBM->emptiness()){
    retVal = false;
    if (debug) {
      print_sequentCheck(cout, step - 1, retVal, lhs, retPlaceDBM, sub, rhs->getOpType());

      cout <<"----(Invalid) Empty First Placeholder: No Need for additional Placeholder Checks-----" << endl << endl;
    }
    //delete retPlace;
    delete tPlace;
    return retVal;
  }
  retVal = true;
  /* Now check for the relativization.
   * First, find the subset of the predecessor_< of the placeholder
   * that satisfies the left clause.
   * Second: utilize a pred_check() method to further tighten the
   * placeholder in order that the entire predecessor does satisfy
   * the relativization formaula.  */
  /* First step */
  DBMList * phi2PredPlace = new DBMList(*retPlaceDBM);
  phi2PredPlace->pre();
  // pred Closure makes sure that the exact valuation for the placeholder
  // is excluded.
  phi2PredPlace->predClosureRev();
  phi2PredPlace->cf();
  /* At this point, phi2PredPlace is the time predecessor_{<} of
   * the placeholders that satisfy phi_2, the right hand formula */

  /* We find all the times that satisfy phi_1, and then intersect it
   * with the time predecessor of the phi_2 placeholders. */
  DBMList * phi2Place = new DBMList(*retPlaceDBM);
  DBMList place1Temp(*INFTYDBM);
  // Since invariants are past closed, we do not need to intersect
  // this placeholder with the invariant.
  retPlaceDBM = do_proof_place(step, &phb, &place1Temp, rhs->getLeft(), sub);
  /* Second step: tighten and check the predecessor */
  // Must check for emptiness to handle the corner case when it is empty
  DBMList phi1Place(*retPlaceDBM);
#if DEBUG
  if(debug) {
    cout <<"----() Placeholder of times where \\phi_1 is true----- {";
    phi1Place.print_constraint(cout);
    cout << "} ----"<< endl << endl;
  }
#endif
  // This provides a preliminary check.
  *retPlaceDBM & *phi2PredPlace;
  retPlaceDBM->cf();
  if(retPlaceDBM->emptiness()) {
    retVal = false;
#if DEBUG
    if(debug) {
      print_sequentCheck(cout, step - 1, retVal, &phb, retPlaceDBM, sub, rhs->getOpType());

      cout <<"----() Empty Second Placeholder: Relativization Formula \\phi_1 is never true-----" << endl << endl;
    }
#endif
    /* Now determine if $\phi_2$ is true without a time elapse.
     * If so, make a non-empty placeholder. In this case, the third
     * Check will be true by default and can be skipped.
     * Else, return empty and break */
    *phi2Place & *lhs; // lhs here is before the time elapse
    phi2Place->cf();
    if(phi2Place->emptiness()) {
      retVal = false;
#if DEBUG
      if(debug) {

        cout << "----(Invalid) Time Elapsed required for formula to be true; hence, relativized formula cannot always be false." << endl << endl;
      }
#endif
    }
    else {
      /* While a time elapse is not required, the placeholder
       * must span all of lhs */
      retVal = (*phi2Place) >= (*lhs);

#if DEBUG
      if(debug) {
        if(retVal) {
          cout <<"----(Valid) Time Elapse not required and placeholder spans lhs; hence, formula is true-----" << endl
          << "----With resulting Placeholder := {";
          phi2Place->print_constraint(cout);
          cout << "} ----"<< endl << endl;
        }
        else {
          cout <<"----(Invalid) While Time Elapse not required, placeholder is not large enough-----" << endl
          << "----With resulting Placeholder := {";
          phi2Place->print_constraint(cout);
          cout << "} ----"<< endl << endl;
        }

      }
#endif
    }


    delete phi2Place;
    delete phi2PredPlace;
    delete tPlace;
    return retVal;
  }

  DBMList currRetPlaceDBM(*retPlaceDBM);
  /*--- PredCheck code----*/
  retPlaceDBM = predCheckRule(lhs, &ph, NULL, &phi1Place, phi2Place, phi2PredPlace);
  if(retPlaceDBM->emptiness()) {
    retVal = false;
#if DEBUG
    if(debug) {
      cout <<"----(Invalid) Relativization placeholder failed-----" << endl
      << "----With resulting Placeholder := {";
      retPlaceDBM->print_constraint(cout);
      cout << "} ----"<< endl << endl;
    }
#endif
    delete phi2Place;
    delete phi2PredPlace;
    delete tPlace;
    return retVal;
  }
  // if it is nonempty, it passes the second check and we continue



#if DEBUG
  if(debug) {
    print_sequent_place(std::cout, step - 1,  retVal, &phb, phi2PredPlace, rhs->getLeft(), sub, rhs->getOpType());
    cout <<"----(Valid) Relativization Placeholder Check Passed (Check Only)-----" << endl
    << "----With resulting Placeholder := {";
    retPlaceDBM->print_constraint(cout);
    cout << "} ----"<< endl << endl;
  }
#endif

  // Allow for the possibility of the time instant after the elapse
  retPlaceDBM->closure();
  /* Extract the new refined placeholder. */
  *retPlaceDBM & *phi2Place;
  retPlaceDBM->cf();


  /* Now check that it works. */
  /* Since we are not using retPlace anymore, we do not
   * need to copy it for the check. */
  retPlaceDBM->pre();
  /* This cf() is needed. */
  retPlaceDBM->cf();
  retVal = (*retPlaceDBM) >= (*lhs);


#if DEBUG
  if (debug) {
    print_sequentCheck(cout, step - 1, retVal, lhs, retPlaceDBM, sub, rhs->getOpType());
    if(retVal) {
      cout <<"----(Valid) Last Placeholder Check Passed (Check Only)-----" << endl
      << "----With Placeholder := {";
      retPlaceDBM->print_constraint(cout);
      cout << "} ----"<< endl << endl;

    }
    else {
      cout <<"----(Invalid) Last Placeholder Check Failed-----" << endl << endl;

    }
  }
#endif
  delete phi2Place;
  delete phi2PredPlace;
  delete tPlace;
  return retVal;
}

bool prover::do_proof_allact(int step, DBM * const lhs, const ExprNode * const rhs, SubstList * const sub)
{
  bool retVal = true;
  /* Enumerate through all transitions */
#if DEBUG
  if(debug) {
    cout << "\t Proving ALLACT Transitions:----\n" << endl;
  }
#endif
  for(vector<Transition *>::const_iterator it = input_pes.transitions().begin();
      it != input_pes.transitions().end(); it++ ) {
    Transition * tempT = *it;
    /* Obtain the entire ExprNode and prove it */
    DBM tempLHS(*lhs);

    bool tempBool = comp_ph(&tempLHS, *(tempT->getLeftExpr()), *sub);
    if(tempBool == false) {
#if DEBUG
      if (debug) {
        cout << "Transition: ";
        print_Transition(tempT, cout);
        cout << " cannot be taken." << endl;
      }
#endif
      continue;
    }

    /* Now check the invariant */
    DBM invCons(*INFTYDBM);
    const SubstList * sl = tempT->getEnteringLocation(sub);
    bool isInv = invs_chk(input_pes.invariants(), &invCons, *sl);
    delete sl;
    if(isInv) {
      invCons.cf();
      const ClockSet * st = tempT->getCSet();
      if(st != NULL) {
        invCons.preset(st);
      }
      invCons.cf();
      /* Now perform clock assignments sequentially: perform the
       * front assignments first */
      const vector<pair<short int, short int> > * av = tempT->getAssignmentVector();
      if(av != NULL) {
        // Iterate over the vector and print it
        for(vector<pair<short int, short int> >::const_iterator it=av->begin(); it != av->end(); it++) {
          invCons.preset((*it).first, (*it).second);
          invCons.cf();
        }
      }
      tempLHS & invCons;
      tempLHS.cf();
      if(tempLHS.emptiness()) {
#if DEBUG
        if (debug) {
          cout << "Transition: ";
          print_Transition(tempT, cout);
          cout << " cannot be taken; entering invariant is false." << endl;
          cout << "\tExtra invariant condition: ";
          invCons.print_constraint(cout);
          cout << endl;
        }
#endif
        continue;
      }
    }

    tempT->getNewTrans(rhs->getQuant());


    /* Constraints are bounded by MAXC */
    /* This is to extend the LHS to make sure that
     * the RHS is satisfied by any zone that satisfies
     * the LHS by expanding the zone so it contains
     * all the proper regions where the clocks
     * exceed a certain constant value. */
    tempLHS.cf();
    tempLHS.bound(MAXC);
    SubstList tempSub(*sub);

#if DEBUG
    if (debug) {
      cout << "Executing transition (with destination) ";
      print_Transition(tempT, cout);
      cout << endl;
      cout << "\tExtra invariant condition: ";
      invCons.print_constraint(cout);
      cout << endl;
    }
#endif
    numLocations++;
    retVal = do_proof(step, &tempLHS, tempT->getRightExpr(), &tempSub);
    if(retVal == false) {
#if DEBUG
      if (debug) {
        cout << "Trainsition: ";
        print_Transition(tempT, cout);
        cout << endl;
        cout << "\tinvalidates property and breaks transition executions. ";
        cout << endl;
      }
#endif
      break;
    }

  }
#if DEBUG
  if(debug) {
    cout << "\t --- end of ALLACT." << endl;
  }
#endif
  return retVal;
}

bool prover::do_proof_existact(int step, DBM * const lhs, const ExprNode * const rhs, SubstList * const sub)
{
  bool retVal = false;
  /* Enumerate through all transitions */
#if DEBUG
  if(debug) {
    cout << "\t Proving EXISTACT Transitions:----\n" << endl;
  }
#endif
  /* Use placeholders to split rules */
  bool emptyPartialPlace = true;
  DBMList * partialPlace;
  for(vector<Transition *>::const_iterator it = input_pes.transitions().begin();
      it != input_pes.transitions().end(); it++ ) {
    Transition * tempT = *it;

    /* Obtain the entire ExprNode and prove it */


    // Make a similar comp function for exists so
    // because the entire zone must be able to transition
    // or split by placeholders
    DBMList tempPlace(*INFTYDBM);
    lhs->cf();
    DBM tempLHS(*lhs);
    bool tempBool = comp_ph_exist_place(&tempLHS, &tempPlace, *(tempT->getLeftExpr()), *sub);
    if(tempBool == false) {
#if DEBUG
      if (debug) {
        cout << "Transition: ";
        print_Transition(tempT, cout);
        cout << " cannot be taken." << endl;
      }
#endif
      continue;
    }

    /* Now check the invariant */
    DBM invCons(*INFTYDBM);
    const SubstList * sl = tempT->getEnteringLocation(sub);
    bool isInv = invs_chk(input_pes.invariants(), &invCons, *sl);
    delete sl;
    if(isInv) {
      invCons.cf();
      const ClockSet * st = tempT->getCSet();
      if(st != NULL) {
        invCons.preset(st);
      }
      invCons.cf();
      /* Now perform clock assignments sequentially: perform the
       * front assignments first */
      const vector<pair<short int, short int> > * av = tempT->getAssignmentVector();
      if(av != NULL) {
        // Iterate over the vector and print it
        for(vector<pair<short int, short int> >::const_iterator it=av->begin(); it != av->end(); it++) {
          invCons.preset((*it).first, (*it).second);
          invCons.cf();
        }
      }
      /* Check if invariant preset is satisfied by the lhs.
       * If not, tighten the placeholder */
      if(!(tempLHS <= invCons)) {
        // for performance reasons, also tighten the left hand side
        tempPlace & invCons;
        tempPlace.cf();
        if(tempPlace.emptiness()) {
#if DEBUG
          if (debug) {
            cout << "Transition: ";
            print_Transition(tempT, cout);
            cout << " cannot be taken; entering invariant is false." << endl;
            cout << "\tExtra invariant condition: ";
            invCons.print_constraint(cout);
            cout << endl;
          }
#endif
          continue;
        }
        tempLHS & invCons;
        tempLHS.cf();

      }
    }

    tempT->getNewTrans(rhs->getQuant());
    /* Constraints are bounded by MAXC */
    /* This is to extend the LHS to make sure that
     * the RHS is satisfied by any zone that satisfies
     * the LHS by expanding the zone so it contains
     * all the proper regions where the clocks
     * exceed a certain constant value. */

    tempLHS.bound(MAXC);
    SubstList tempSub(*sub);
    // Above placeholder restricted to satisfy incoming invariant
    //DBMList *retPlace;
#if DEBUG
    if (debug) {
      cout << "Executing transition (with destination) ";
      print_Transition(tempT, cout);
      cout << endl;
    }
#endif
    numLocations++;
    retPlaceDBM = do_proof_place(step, &tempLHS, &tempPlace, tempT->getRightExpr(), &tempSub);

    // Reset place parent to NULL
    parentPlaceRef = NULL;
    if(retPlaceDBM->emptiness()) {

    }
    else if(*retPlaceDBM >= *lhs) {
      retVal = true;
      //delete retPlace;
      break;
    }
    else { /* The rare case that involves splitting */
      if(emptyPartialPlace) {
        partialPlace = new DBMList(*retPlaceDBM);
        emptyPartialPlace = false;
      }
      else {
        partialPlace->addDBMList(*retPlaceDBM);
      }
    }
    // delete retPlace;


  }
  if(retVal == false && !emptyPartialPlace) {
    /* Here compare to make sure our partial places are enough */
    retVal = (*partialPlace >= *lhs);
    delete partialPlace;
  }
  else if(!emptyPartialPlace) {
    delete partialPlace;
  }

#if DEBUG
  if(debug) {
    cout << "\t --- end of EXISTACT." << endl;
  }
#endif
  return retVal;
}

bool prover::do_proof_imply(int step, DBM * const lhs, const ExprNode * const rhs, SubstList * const sub)
{
  bool retVal = false;
  /* Here is the one call to comp_ph(...) outside of copm_ph(...) */
  DBM tempLHS(*lhs);
  if(comp_ph(&tempLHS, *(rhs->getLeft()), *sub)){
    /* Constraints are bounded by MAXC */
    /* This is to extend the LHS to make sure that
     * the RHS is satisfied by any zone that satisfies
     * the LHS by expanding the zone so it contains
     * all the proper regions where the clocks
     * exceed a certain constant value. */
    tempLHS.cf();
    tempLHS.bound(MAXC);

    retVal = do_proof(step, &tempLHS, rhs->getRight(), sub);
  }
  else  {
    /* The set of states does not satisfy the premises of the IF
     * so thus the proof is true */
    retVal = true;
#if DEBUG
    if (debug) {
      cout << "---(Valid) Leaf IMPLY Reached, Premise Not Satisfied----" << endl << endl;
    }
#endif
  }
  return retVal;
}

bool prover::do_proof_constraint(int step, DBM * const lhs, const ExprNode * const rhs, SubstList * const sub)
{
  lhs->cf();
  /* The line: (rhs->dbm())->cf(); is not needed */
  bool retVal = (*lhs <= *(rhs->dbm()));
#if DEBUG
  if (debug && retVal) {
    cout << "---(Valid) Leaf DBM (CONSTRAINT) Reached----" << endl << endl;
  }
  if (debug && !retVal) {
    cout << "---(Invalid) Leaf DBM (CONSTRAINT) Reached----" << endl << endl;
  }
#endif
  return retVal;
}

bool prover::do_proof_bool(int step, DBM * const lhs, const ExprNode * const rhs, SubstList * const sub)
{
  bool retVal = (rhs->getBool());
#if DEBUG
  if (debug && retVal) {
    cout << "---(Valid) Leaf BOOL Reached----" << endl << endl;
  }
  if (debug && !retVal) {
    cout << "---(Invalid) Leaf BOOL Reached----" << endl << endl;
  }
#endif
  return retVal;
}

bool prover::do_proof_atomic(int step, DBM * const lhs, const ExprNode * const rhs, SubstList * const sub)
{
  bool retVal = (sub->operator[](rhs->getAtomic()) == rhs->getIntVal());
#if DEBUG
  if (debug && retVal) {
    cout << "---(Valid) Leaf ATOMIC == Reached----" << endl << endl;
  }
  if (debug && !retVal) {
    cout << "---(Invalid) Leaf ATOMIC == Reached----" << endl << endl;
  }
#endif
  return retVal;
}

bool prover::do_proof_atomic_not(int step, DBM * const lhs, const ExprNode * const rhs, SubstList * const sub)
{
  bool retVal = (sub->operator[](rhs->getAtomic()) != rhs->getIntVal());
#if DEBUG
  if (debug && retVal) {
    cout << "---(Valid) Leaf ATOMIC != Reached----" << endl << endl;
  }
  if (debug && !retVal) {
    cout << "---(Invalid) Leaf ATOMIC != Reached----" << endl << endl;
  }
#endif
  return retVal;
}

bool prover::do_proof_atomic_lt(int step, DBM * const lhs, const ExprNode * const rhs, SubstList * const sub)
{
  bool retVal = (sub->operator[](rhs->getAtomic()) < rhs->getIntVal());
#if DEBUG
  if (debug && retVal) {
    cout << "---(Valid) Leaf ATOMIC < Reached----" << endl << endl;
  }
  if (debug && !retVal) {
    cout << "---(Invalid) Leaf ATOMIC < Reached----" << endl << endl;
  }
#endif
  return retVal;
}

bool prover::do_proof_atomic_gt(int step, DBM * const lhs, const ExprNode * const rhs, SubstList * const sub)
{
  bool retVal = (sub->operator[](rhs->getAtomic()) > rhs->getIntVal());
#if DEBUG
  if (debug && retVal) {
    cout << "---(Valid) Leaf ATOMIC > Reached----" << endl << endl;
  }
  if (debug && !retVal) {
    cout << "---(Invalid) Leaf ATOMIC > Reached----" << endl << endl;
  }
#endif
  return retVal;
}

bool prover::do_proof_atomic_le(int step, DBM * const lhs, const ExprNode * const rhs, SubstList * const sub)
{
  bool retVal = (sub->operator[](rhs->getAtomic()) <= rhs->getIntVal());
#if DEBUG
  if (debug && retVal) {
    cout << "---(Valid) Leaf ATOMIC < Reached----" << endl << endl;
  }
  if (debug && !retVal) {
    cout << "---(Invalid) Leaf ATOMIC < Reached----" << endl << endl;
  }
#endif
  return retVal;
}
bool prover::do_proof_atomic_ge(int step, DBM * const lhs, const ExprNode * const rhs, SubstList * const sub)
{
  bool retVal = (sub->operator[](rhs->getAtomic()) >= rhs->getIntVal());
#if DEBUG
  if (debug && retVal) {
    cout << "---(Valid) Leaf ATOMIC > Reached----" << endl << endl;
  }
  if (debug && !retVal) {
    cout << "---(Invalid) Leaf ATOMIC > Reached----" << endl << endl;
  }
#endif
  return retVal;
}

bool prover::do_proof_sublist(int step, DBM * const lhs, const ExprNode * const rhs, SubstList * const sub)
{
  SubstList st(rhs->getSublist(), sub );
  return do_proof(step, lhs, rhs->getExpr(), &st);
}

bool prover::do_proof_reset(int step, DBM * const lhs, const ExprNode * const rhs, SubstList * const sub)
{
  lhs->cf();
  DBM ph(*lhs);
  const ClockSet *rs = rhs->getClockSet();
  ph.reset(rs);

  return do_proof(step, &ph, rhs->getExpr(), sub);
}

bool prover::do_proof_assign(int step, DBM * const lhs, const ExprNode * const rhs, SubstList * const sub)
{
  lhs->cf();
  DBM ph(*lhs);
  /* Here the DBM zone is where the value of
   * clock x is reset to clock y, which is possibly
   * a constant or a value*/
  short int cX = rhs->getcX();
  short int cY = rhs->getcY();

  ph.reset(cX, cY);

  return do_proof(step, &ph, rhs->getExpr(), sub);
}

bool prover::do_proof_replace(int step, DBM * const lhs, const ExprNode * const rhs, SubstList * const sub)
{
  sub->operator[](rhs->getcX()) = sub->operator[](rhs->getcY());
  return do_proof(step, lhs, rhs->getExpr(), sub);
}

bool prover::do_proof_ablewaitinf(int step, DBM * const lhs, const ExprNode * const rhs, SubstList * const sub)
{
  lhs->cf();
  DBM ph(*lhs);
  ph.suc();
  invs_chk(input_pes.invariants(), &ph, *sub);
  ph.cf();
  /* Time can diverge if and only if there are no upper bound
   * constraints in the successor */
  bool retVal = !(ph.hasUpperConstraint());
#if DEBUG
  if (debug && retVal) {
    cout << "---(Valid) Time able to diverge to INFTY in current location----" << endl << endl;
  }
  if (debug && !retVal) {
    cout << "---(Invalid) Time unable to diverge to INFTY in current location---" << endl << endl;
  }
#endif
  return retVal;
}

bool prover::do_proof_unablewaitinf(int step, DBM * const lhs, const ExprNode * const rhs, SubstList * const sub)
{
  lhs->cf();
  DBM ph(*lhs);
  ph.suc();
  invs_chk(input_pes.invariants(), &ph, *sub);
  ph.cf();
  /* Time cannot diverge if and only if there is an upper bound
   * constraint in the successor */
  bool retVal = ph.hasUpperConstraint();
#if DEBUG
  if (debug && retVal) {
    cout << "---(Valid) Time unable to diverge to INFTY in current location----" << endl << endl;
  }
  if (debug && !retVal) {
    cout << "---(Invalid) Time able to diverge to INFTY in current location---" << endl << endl;
  }
#endif
  return retVal;
}


/** The prover function to prove whether a sequent is true or false.
 * @param step The "tree level" of the sequent in the proof tree.
 * A lower number is closer to the root, and a higher level is close
 * to "leaf" sequents. The main() method
 * that calls this feeds in 0.
 * @param lhs (*) The initial DBM of clock constraints (Sequent Premise)
 * @param rhs (*) The Expression/Consequent (root of the Expression Tree)
 * that the prover
 * needs to determine if it is true or false.
 * @param sub (*) The current substitution list of variables and their
 * substituted values, used to represent the current
 * atomic "state" of the Sequent.
 * @return True if the expression evaluates to True given the other parameters
 * and False otherwise (if the expression evaluates to False).*/
bool prover::do_proof(int step, DBM * const lhs, const ExprNode * const rhs, SubstList * const sub)
{
  bool retVal = false;
#if DEBUG
  if (debug){
    lhs->cf();
    print_sequent(std::cout, step, retVal, lhs, rhs, sub, rhs->getOpType());
  }
#endif
  step++;

  switch(rhs->getOpType()){
    case PREDICATE:{
      retVal = do_proof_predicate(step, lhs, rhs, sub);
      break;
    }
    case AND:
    {
      retVal = do_proof_and(step, lhs, rhs, sub);
      break;
    }
    case OR:{
      retVal = do_proof_or(step, lhs, rhs, sub);
      break;
    }
    case OR_SIMPLE:{
      retVal = do_proof_or_simple(step, lhs, rhs, sub);
      break;
    }
    case FORALL:{
      retVal = do_proof_forall(step, lhs, rhs, sub);
      break;
    }
    case FORALL_REL: {
      retVal = do_proof_forall_rel(step, lhs, rhs, sub);
      break;
    }
    case EXISTS:{
      retVal = do_proof_exists(step, lhs, rhs, sub);
      break;
    }
    case EXISTS_REL: {
      retVal = do_proof_exists_rel(step, lhs, rhs, sub);
      break;
    }
    case ALLACT: {
      retVal = do_proof_allact(step, lhs, rhs, sub);
      break;
    }
    case EXISTACT: {
      retVal = do_proof_existact(step, lhs, rhs, sub);
      break;
    }
    case IMPLY:{
      retVal = do_proof_imply(step, lhs, rhs, sub);
      break;
    }
    case CONSTRAINT:{
      retVal = do_proof_constraint(step, lhs, rhs, sub);
      break;
    }
    case BOOL:{
      retVal = do_proof_bool(step, lhs, rhs, sub);
      break;
    }
    case ATOMIC:{
      retVal = do_proof_atomic(step, lhs, rhs, sub);
      break;
    }
    case ATOMIC_NOT:{
      retVal = do_proof_atomic_not(step, lhs, rhs, sub);
      break;
    }
    case ATOMIC_LT:{
      retVal = do_proof_atomic_lt(step, lhs, rhs, sub);
      break;
    }
    case ATOMIC_GT:{
      retVal = do_proof_atomic_gt(step, lhs, rhs, sub);
      break;
    }
    case ATOMIC_LE:{
      retVal = do_proof_atomic_le(step, lhs, rhs, sub);
      break;
    }
    case ATOMIC_GE:{
      retVal = do_proof_atomic_ge(step, lhs, rhs, sub);
      break;
    }
    case SUBLIST:{
      retVal = do_proof_sublist(step, lhs, rhs, sub);
      break;
    }
    case RESET:{
      retVal = do_proof_reset(step, lhs, rhs, sub);
      break;
    }
    case ASSIGN:{
      retVal = do_proof_assign(step, lhs, rhs, sub);
      break;
    }
    case REPLACE:{
      retVal = do_proof_replace(step, lhs, rhs, sub);
      break;
    }
    case ABLEWAITINF:{
      retVal = do_proof_ablewaitinf(step, lhs, rhs, sub);
      break;
    }
    case UNABLEWAITINF:{
      retVal = do_proof_unablewaitinf(step, lhs, rhs, sub);
      break;
    }
    default:
    {
      cout <<"Error, operator not defined." << endl;
      assert(false);
    }
  }

  return retVal;
}

/** The prover function that handles placeholders.
 * @param step The "tree level" of the sequent in the proof tree.
 * A lower number is closer to the root, and a higher level is close
 * to "leaf" sequents. The main() method
 * that calls this feeds in 0.
 * @param lhs (*) The initial DBM of clock constraints (Sequent Premise)
 * @param place (*) The current zone union of the Placeholder DBM.
 * @param rhs (*) The Expression/Consequent (root of the Expression Tree)
 * that the prover
 * needs to determine if it is true or false.
 * @param sub (*) The current substitution list of variables and their
 * substituted values, used to represent the current
 * atomic "state" of the Sequent.
 * @return The DBM Value of the placeholder constraint or an empty DBM if
 * no valid value for the placeholder exists (thus proof is Invalid). */
DBMList * prover::do_proof_place(int step, DBM * const lhs, DBMList * const place,
                         const ExprNode * const rhs, SubstList * const sub)
{
  /* do_proof_place() written by Peter Fontana, needed for support
   * of EXISTS Quantifiers. */
  bool retVal = false;

#if DEBUG
  if (debug) {
    lhs->cf();
    place->cf();
    print_sequent_place(std::cout, step, retVal, lhs, place, rhs, sub, rhs->getOpType());
  }
#endif
  step++;

  switch(rhs->getOpType()){
    case PREDICATE:{

      ExprNode *e = input_pes.lookup_equation(rhs->getPredicate());
      if (e == NULL){
        cerr << "open predicate variable found: "<< rhs->getPredicate()<<endl;
        exit(-1);
      }

      // Get Predicate Index for Hashing
      int pInd = input_pes.lookup_predicate(rhs->getPredicate())->getIntVal() - 1;

      prevParityGfp = currParityGfp;
      currParityGfp = rhs->get_Parity();

      lhs->cf();

      place->cf();
      /* First look in known true and false sequent tables */

      /* First look in known False Sequent tables.
       * Note: The False sequents with placeholders do not
       * need to store placeholders. */
      if(useCaching) {
        SequentPlace *tf = new SequentPlace(rhs, sub);
        SequentPlace *hf = Xlist_false_ph.look_for_sequent(tf->sub(), pInd);
        if(hf != NULL && tabled_false_sequentPlace(hf, lhs, place)) {
          // Found known false
          retVal = false;
          retPlaceDBM->makeEmpty();
#if DEBUG
          if (debug) {
            cout << "---(Invalid) Located a Known False Sequent ----" << endl << endl;
          }
#endif
          /* Update backpointers to add possible pointer for parent
           * This is a bit conservative */
          /* Now that we have a proven sequent, add the backpointer
           * from the child to the parent */
          if(parentPlaceRef != NULL) {
            hf->parSequentPlace.push_back(parentPlaceRef);
          }
          else { // Parent is regular sequent
            hf->parSequent.push_back(parentRef);
          }
          // Do not delete if tf is the same sequent as hf
          if(tf != hf) {
            delete tf;
          }
          break;
        }
        if(tf != hf) {
          delete tf;
        }
      }

      /* Now look in known true cache */
      if(useCaching) {
        SequentPlace *tfb = new SequentPlace(rhs, sub);
        SequentPlace *hfb = Xlist_true_ph.look_for_sequent(tfb->sub(), pInd);
        DBMList tempPlace(*place);
        /* Note: tempPlace is changed by tabled_sequentPlace() */
        if(hfb != NULL && tabled_sequentPlace(hfb, lhs, &tempPlace)) {
          // Found known true
          if(tempPlace.emptiness()) {
            // returning placeholder must be non-empty for the sequent
            // to be valid
            break;
          }
          retVal = true;
          *retPlaceDBM = (tempPlace);
          // Note: we intersect the current found placeholder
          // with the placeholder stored in the sequent.

#if DEBUG
          if (debug) {
            cout << "---(Valid) Located a Known True Sequent ----" << endl << endl;
          }
#endif
          /* Update backpointers to add possible pointer for parent
           * This is a bit conservative */
          /* Now that we have a proven sequent, add the backpointer
           * in the cache from the child to the parent */
          if(parentPlaceRef != NULL) {
            hfb->parSequentPlace.push_back(parentPlaceRef);
          }
          else { // Parent is regular sequent
            hfb->parSequent.push_back(parentRef);
          }

          if(tfb != hfb) {
            delete tfb;
          }
          break;
        }
        if(tfb != hfb) {
          delete tfb;
        }
      }

      /* Now deal with greatest fixpoint and least fixpoint circularity */
      SequentPlace *t = new SequentPlace(rhs, sub);
      SequentPlace *h;
      if(currParityGfp) { // Thus a Greatest Fixpoint
        /* Already looked in known false so no need to do so */
        h = Xlist_pGFP_ph.locate_sequent(t, pInd);
        if((!newSequent) && tabled_sequent_gfpPlace(h, lhs, place)) {
          // Found gfp Circularity - thus valid
          retVal = true;
          *retPlaceDBM = (*place);
#if DEBUG
          if (debug) {
            cout << "---(Valid) Located True Sequent or gfp Circularity ----" << endl << endl;
          }
#endif
          /* Now update backpointer for greatest fixpoint circularity */
          if(parentPlaceRef != NULL) {
            h->parSequentPlace.push_back(parentPlaceRef);
          }
          else { // Parent is regular sequent
            h->parSequent.push_back(parentRef);
          }

          // Add sequent to known true cache
          if(useCaching) {
            SequentPlace *t7 = new SequentPlace(rhs, sub);
            SequentPlace *h7 = Xlist_true_ph.locate_sequent(t7, pInd);
            update_sequentPlace(h7, lhs, place);
          }
          break;
        }


        pair <DBM *, DBMList *> p (new DBM(*lhs),new DBMList(*place));
        h->ds.push_back(p);
      }
      else { // Thus, a least fixpoint
        // Now look in lfp circularity cache
        h = Xlist_pLFP_ph.locate_sequent(t, pInd);
        if((!newSequent) && tabled_sequent_lfpPlace(h, lhs, place)) {
          // Found lfp circularity - thus invalid
          retVal = false;
          retPlaceDBM->makeEmpty();

#if DEBUG
          if (debug) {
            cout << "---(Invalid) Located lfp Circularity ----" << endl << endl;
          }
#endif

          /* Now update backpointer for least fixpoint circularity */
          if(parentPlaceRef != NULL) {
            h->parSequentPlace.push_back(parentPlaceRef);
          }
          else { // Parent is regular sequent
            h->parSequent.push_back(parentRef);
          }

          // Now Put Sequent in False Cache
          if(useCaching) {
            SequentPlace *t7 = new SequentPlace(rhs, sub);
            SequentPlace *h7 = Xlist_false_ph.locate_sequent(t7, pInd);
            update_false_sequentPlace(h7, lhs, place);
          }
          break;
        }

        pair <DBM *, DBMList *> p (new DBM(*lhs), new DBMList(*place));
        h->ds.push_back(p);
      }

      /* Assign parent value after caching since during caching we may have
       * to use the previous parent */
      SequentPlace * tempParentPlace = parentPlaceRef;
      /* Get the current variable */
      parentPlaceRef = h;

      //delete retPlaceDBM;
      retPlaceDBM = do_proof_place(step, lhs, place, e, sub);

      lhs->cf();


      /* Now update the parent so it points to the previous parent, and not this
       * predicate */
      parentPlaceRef = tempParentPlace;

      pair <DBM *, DBMList *> tempP = h->ds.back();
      DBM * tempF = tempP.first;
      delete tempF;
      DBMList * tempS = tempP.second;
      delete tempS;
      h->ds.pop_back();
      // ds might be empty, but we leave it in


      // Now Purge updated premise
      retPlaceDBM->cf();

      /* Key Concept of Purging:
       * If Was True, discovered false, check that
       *		Z_now_false <= Z_cached_true | or | Z_cached_true >= Z_now_false
       * If Was False, discovered true, check that
       *		Z_now_true >= Z_cached_false | or | Z_cached_false <= Z_now_true
       * This Must be done regardless of how the tabling
       * is done for that specific cache */
      if(useCaching && !(retPlaceDBM->emptiness())) {
        /* First look in opposite parity Caches */
        SequentPlace *t2c = new SequentPlace(rhs, sub);
        SequentPlace *t2s;
        bool madeEmpty = false;
        t2s = Xlist_false_ph.look_for_and_purge_rhs_sequent(std::make_pair(lhs, retPlaceDBM), t2c, pInd, false, &madeEmpty);


        /* Now purge backpointers */
        if(t2s != NULL) {
          look_for_and_purge_rhs_backStack(&(t2s->parSequent),
                                           &(t2s->parSequentPlace));
          // Delete t2s later to prevent double deletion

        }
        // Now update in proper Cache
        SequentPlace *t5 = new SequentPlace(rhs, sub);
        SequentPlace *h5 = Xlist_true_ph.locate_sequent(t5, pInd);
        update_sequentPlace(h5, lhs, retPlaceDBM);

        // Now make deletions for Memory Cleanup
        if(t2c != t2s) {
          delete t2c;
        }
        // this delete is necessary for memory management but problematic
        if(madeEmpty) {
          delete t2s;
        }


      }
      else if(useCaching) { /* retPlaceDBM is empty */
        /* First look in opposite parity Cache */
        // Now look in placeholder caches
        SequentPlace *t2b2 = new SequentPlace(rhs, sub);
        SequentPlace *t2bs;
        bool madeEmpty = false;
        t2bs = Xlist_true_ph.look_for_and_purge_rhs_sequent(std::make_pair(lhs, retPlaceDBM), t2b2, pInd, true, &madeEmpty);


        /* Now purge backpointers.
         * Ignore circularity booleans because they do not form backpointers */
        if(t2bs != NULL) {
          look_for_and_purge_rhs_backStack(&(t2bs->parSequent),
                                           &(t2bs->parSequentPlace));
          // delete t2bs later to prevent double deletion.
        }
        // Now update in proper Cache
        SequentPlace *t5 = new SequentPlace(rhs, sub);
        SequentPlace *h5 = Xlist_false_ph.locate_sequent(t5, pInd);
        update_false_sequentPlace(h5, lhs, retPlaceDBM);

        // Now make deletions for Memory Cleanup
        if(t2b2 != t2bs) {
          delete t2b2;
        }
        // This delete is necessary for memory management but problematic
        if(madeEmpty) {
          delete t2bs;
        }

      }

      break; }
    case AND:{
      retPlaceDBM = do_proof_place(step, lhs, place, rhs->getLeft(), sub);
      retPlaceDBM->cf();
      if(!(retPlaceDBM->emptiness())) {
        place->cf();
        DBMList tPlace(*place);
        tPlace & (*retPlaceDBM);
        DBMList tempDBM2(*retPlaceDBM);
        retPlaceDBM = do_proof_place(step, lhs, &tPlace, rhs->getRight(), sub);
        *retPlaceDBM & tempDBM2;

      }
      break;
    }
    case OR:{
      place->cf();
      DBMList placeB(*place);
      // delete retPlaceDBM;
      retPlaceDBM = do_proof_place(step, lhs, place, rhs->getLeft(), sub);
      // Now do the right proof, and take the right if its placeholder is
      // larger that from the left side.
      bool emptyLeft = retPlaceDBM->emptiness();
      if((!emptyLeft) && (*retPlaceDBM >= placeB)) {
        /* Here, the current transition successful;
         * we are done */
        retVal = true;
        break;
      }

      retPlaceDBM->cf();
      DBMList leftPlace(*retPlaceDBM);
      retPlaceDBM = do_proof_place(step, lhs, &placeB, rhs->getRight(), sub);
      retPlaceDBM->cf();

#if DEBUG
      if(debug) {
        // Check Debugging Here to make sure it is giving the right output
        print_sequentCheck(cout, step - 1, retVal, lhs, place, sub, rhs->getOpType());
        cout << "Left Placeholder of OR (P): ";
        leftPlace.print_constraint(cout);
        cout << "\nRight Placeholder of OR (P): ";
        retPlaceDBM->print_constraint(cout);
        cout << endl;
      }
#endif

      /* Note: <= >= Not clearly working if empty DBMs */
      if(emptyLeft) { // we already checked the emptiness of the previous DBM
        // Do Nothing
      }
      else if(retPlaceDBM->emptiness()) {
        // Take previous DBM
        *retPlaceDBM = leftPlace;
      }
      else if(leftPlace <= (*retPlaceDBM)) {
        // do nothing

      }
      else if (*retPlaceDBM <= leftPlace) {
        *retPlaceDBM = leftPlace;
        retVal = retPlaceDBM->emptiness();
      }
      else { /* Corner Case: make DBM Union*/
        retPlaceDBM->addDBMList(leftPlace);
        retPlaceDBM->cf();
      }
      retVal = !(retPlaceDBM->emptiness());

#if DEBUG
      if(debug) {
        cout << "Final Placeholder of OR (P): ";
        retPlaceDBM->print_constraint(cout);
        cout << endl << endl;
      }
#endif
      break;}
    case OR_SIMPLE:{
      /* In OR_SIMPLE, the placeholder will either be empty or completely full
       * in one of the two cases. Hence, fewer comparisons with unions of zones
       * are needed. */
      place->cf();
      DBMList placeB(*place);
      //delete retPlaceDBM;
      retPlaceDBM = do_proof_place(step, lhs, place, rhs->getLeft(), sub);
      // Now do the right proof, and take the right if its placeholder is
      // larger that from the left side.
      bool emptyLeft = retPlaceDBM->emptiness();
      if(!emptyLeft && (*retPlaceDBM >= *place)) {
        /* Here, the current transition successful;
         * we are done */
        retVal = true;
        break;
      }

      retPlaceDBM->cf();
      //DBMList * leftPlace = retPlaceDBM;
      DBMList leftPlace(*retPlaceDBM);
      // no delete since assigning the value
      retPlaceDBM = do_proof_place(step, lhs, &placeB, rhs->getRight(), sub);
      retPlaceDBM->cf();
      /* If the left is simple, then we have an empty left or
       * left is the entire placeholder. */
      if(emptyLeft) { // we already checked for emptiness of the previous DBM
        // Do Nothing
      }
      else if(retPlaceDBM->emptiness()) {
        // Take previous DBM
        *retPlaceDBM = leftPlace;
      }
      /* If neither the if or the else if clauses were taken,
       * then both are non-empty and the left is not the
       * entire placeholder. Hence, the left was not the simple
       * disjunct. Therefore, the right must be the simple disjunct
       * and must be the entire placeholder. */

      retVal = !(retPlaceDBM->emptiness());
      break;}
    case FORALL:{
      /* Here the model checker looks at the zone of
       * all time sucessors and then substitutes in
       * the substitued constraints and sees if the
       * zone satifies the constraints */
      lhs->cf();
      DBM ph(*lhs);
      ph.suc();
      /* Per proof rules with the placeholder,
       * do not incorporate the invariant into the FORALL here */

      DBMList tPlace(*INFTYDBM);

      retPlaceDBM = do_proof_place(step, &ph, &tPlace, rhs->getQuant(), sub);
      retPlaceDBM->cf();
      //must we consider not the invariant even if the placeholder is empty. (?)
      if(!(retPlaceDBM->emptiness())) { // Only do if a nonempty placeholder
        /* Now do the second proof rule to compute the first placeholder
         */

        /* Note; we union retPlaceDBM with the complement of the invariant.
         * should we do this if retPlaceDBM is nonempty? */
        DBMList invCompPlace(*INFTYDBM);
        bool hasInv = invs_chk(input_pes.invariants(), &invCompPlace, *sub);
        if(hasInv) {
          invCompPlace.cf();
          !invCompPlace;
          invCompPlace.cf();
          retPlaceDBM->addDBMList(invCompPlace);
          retPlaceDBM->cf();
        }

        DBMList currPlace(*retPlaceDBM);
        retPlaceDBM = succCheckRule(lhs, &currPlace);

        if(!(retPlaceDBM->emptiness())){
          retVal = true;
        }
        else {/* proof is false */
          retVal = false;
        }
#if DEBUG
        if (debug) {
          // This work is done in the succCheck method.
          // Perhaps I should move the debug rule there?
          DBM succLHS(*lhs);
          succLHS.suc();
          succLHS.cf();
          DBMList succRuleConseq(*lhs);
          succRuleConseq & *retPlaceDBM;
          succRuleConseq.cf();
          succRuleConseq.suc();
          succRuleConseq.cf();
          print_sequentCheck(cout, step - 1, retVal, &succLHS, &succRuleConseq, sub, rhs->getOpType());
          if(retVal) {
            cout <<"----(Valid) Placeholder Check Passed-----" << endl
            <<"--With Placeholder := {";
            retPlaceDBM->print_constraint(cout);
            cout <<"} ----" << endl << endl;
          }
          else {
            cout <<"----(Invalid) Placeholder Check Failed-----" << endl << endl;

          }
        }
#endif

      }
      break;}
    case FORALL_REL: {

      /* Proof methodology:
       * first, see if \phi_1 is satisfied during the time advance.
       * If it is, check that phi_2 is true both at and before those
       * times (time predecessor).
       * If this is not satisfactory, then do a regular FORALL proof
       * without a placeholder. */

      /* First, see if \exists(phi_1) is true. The common case is that it
       * will not be. */
      /* First try to get a new placeholder value that works */
      lhs->cf();
      place->cf();
      DBM ph(*lhs);
      ph.suc();

      DBMList * tPlace = new DBMList(*INFTYDBM);
      invs_chk(input_pes.invariants(), tPlace, *sub);
      retPlaceDBM = do_proof_place(step, &ph, tPlace,
                                   rhs->getLeft(), sub);
      retPlaceDBM->cf();
      if(retPlaceDBM->emptiness()){
        if (debug) {
          print_sequentCheck(cout, step - 1, retVal, &ph, retPlaceDBM, sub, rhs->getOpType());
          cout <<"--------() Empty Relativization Placeholder: phi1 is never true ----------" << endl << endl;
        }
        delete tPlace;
        /* Since here, \forall phi_2 computes the entire placeholder */
        /* Here the model checker looks at the zone of
         * all time sucessors and then substitutes in
         * the substitued constraints and sees if the
         * zone satifies the constraints */
        lhs->cf();
        DBM ph(*lhs);
        ph.suc();

        DBMList newPlace(*INFTYDBM);
        retPlaceDBM = do_proof_place(step, &ph, &newPlace, rhs->getRight(), sub);
        retPlaceDBM->cf();
        if(!(retPlaceDBM->emptiness())){ // Only do if a nonempty placeholder
          /* Now do the second proof rule to compute the first placeholder
           */

          DBMList invCompPlace(*INFTYDBM);
          bool hasInv = invs_chk(input_pes.invariants(), &invCompPlace, *sub);
          if(hasInv) {
            invCompPlace.cf();
            !invCompPlace;
            invCompPlace.cf();
            retPlaceDBM->addDBMList(invCompPlace);
            retPlaceDBM->cf();
          }

          DBMList currPlace(*retPlaceDBM);
          retPlaceDBM = succCheckRule(lhs, &currPlace);

          if(!(retPlaceDBM->emptiness())){
            retVal = true;
          }
          else {/* proof is false */
            retVal = false;
          }
#if DEBUG
          if (debug) {
            // This work is done in the succCheck method.
            // Perhaps I should move the debug rule there?
            DBM succLHS(*lhs);
            succLHS.suc();
            succLHS.cf();
            DBMList succRuleConseq(*lhs);
            succRuleConseq & *retPlaceDBM;
            succRuleConseq.cf();
            succRuleConseq.suc();
            succRuleConseq.cf();
            print_sequentCheck(cout, step - 1, retVal, &succLHS, &succRuleConseq, sub, rhs->getOpType());
            if(retVal) {
              cout <<"----(Valid) FORALL (FORALL_REL) Placeholder Check Passed-----" << endl
              <<"--With Placeholder := {";
              retPlaceDBM->print_constraint(cout);
              cout <<"} ----" << endl << endl;
            }
            else {
              cout <<"----(Invalid) FORALL (FORALL_REL) Placeholder Check Failed-----" << endl << endl;

            }
          }
#endif
        }
      }
      else {
        // First check for the simplest case: no time elapse is needed
        /* Perhaps we can reduce *INFTYDBM to be *place
         * given the proof rules. */
        if((*retPlaceDBM) == (*INFTYDBM)) {
#if DEBUG
          if (debug) {
            print_sequentCheck(cout, step - 1, retVal, lhs, retPlaceDBM, sub, rhs->getOpType());
            cout <<"----(Valid) EXISTS (in FORALL_REL) Placeholder indicates no time elapse is needed (Check Only)-----" << endl
            << "----With Placeholder := {";
            retPlaceDBM->print_constraint(cout);
            cout << "} ----"<< endl << endl;

          }
#endif

          // If here, we neither need a placeholder nor to elapse time
          DBM phb(*lhs);
          DBMList infPlace(*INFTYDBM);
          retPlaceDBM = do_proof_place(step, &phb, &infPlace, rhs->getRight(), sub);
          retPlaceDBM->cf();
          if(!(retPlaceDBM->emptiness())){ // Only do if a nonempty placeholder
            /* Now do the second proof rule to compute the first placeholder */


            // No Successor Check required since this is for no time elapse
            infPlace.cf();
            infPlace & *retPlaceDBM;
            infPlace.cf();
            /* Now do the containment check
             * and use to compute the value of the place holder *place */
            if(!(infPlace.emptiness())){
              retVal = true;
              *retPlaceDBM = infPlace;
            }
            else {/* proof is false */
              retVal = false;
              retPlaceDBM->makeEmpty();
            }
#if DEBUG
            if (debug) {
              print_sequentCheck(cout, step - 1, retVal, &phb, &infPlace, sub, rhs->getOpType());
              if(retVal) {
                cout <<"----(Valid) Placeholder Check Passed-----" << endl
                <<"--With Placeholder := {";
                retPlaceDBM->print_constraint(cout);
                cout <<"} ----" << endl << endl;
              }
              else {
                cout <<"----(Invalid) Placeholder Check Failed-----" << endl << endl;

              }
            }
#endif
          }

        }
        else {
          // This is the more complicated case that requires a placeholder
          // for the FORALL
          /* Now check that we can elapse to the placeholder. */
          // Store the set of times that satisfy phi1
          DBMList phi1Place(*retPlaceDBM);

#if DEBUG
          if (debug) {
            cout <<"----() Relativization \\phi_1 placeholder obtained as {";
            phi1Place.print_constraint(cout);
            cout << "} ----"<< endl << endl;

          }
#endif

          /* We omit the check that we can elapse to the placeholder;
           * We will check that once at the end */
          DBMList *fPlace = new DBMList(*INFTYDBM);
          DBM ph(*lhs);
          ph.suc();
          DBM phb(ph);
          retPlaceDBM = do_proof_place(step, &phb, fPlace,
                                       rhs->getRight(), sub);
          retPlaceDBM->cf();
          DBMList phi2Place(*retPlaceDBM);
#if DEBUG
          if (debug) {
            cout <<"----() Formula \\phi_2 placeholder obtained as {";
            phi2Place.print_constraint(cout);
            cout << "} ----"<< endl << endl;

          }
#endif
          // Reset place parent to NULL
          parentPlaceRef = NULL;

          if(retPlaceDBM->emptiness()) {
            retVal = false;
          }
          else if ((*retPlaceDBM) >= ph) {
            /* In this simple case, all possible times satisfy \phi_2
             * so we can avoid many checks. */
            retVal = true;

          }
          else {
            /* Now do a succ check on phi_2 to get \phi_forall
             * and a predCheck using both phi_1 and phi_2 to get phi_exists */
            /* we also note that the times satisfying \phi_1
             * (the relativization formula condition) are neither empty
             * nor everything. */

            DBMList invCompPlace(*INFTYDBM);
            // Do I worry about the invariants here?
            bool hasInv = invs_chk(input_pes.invariants(), &invCompPlace, *sub);
            if(hasInv) {
              invCompPlace.cf();
              !invCompPlace;
              invCompPlace.cf();
              retPlaceDBM->addDBMList(invCompPlace);
              retPlaceDBM->cf();
            }

            DBMList currPlace(*retPlaceDBM);
            retPlaceDBM = succCheckRule(lhs, &currPlace);
            retPlaceDBM->cf();
            DBMList forallPlace(*retPlaceDBM);

#if DEBUG
            if (debug) {
              print_sequentCheck(cout, step - 1, retVal, &phb, fPlace, sub, rhs->getOpType());
              cout <<"----() FORALL (of FORALL_REL) Placeholder Check obtained  FA Placeholder := {";
              forallPlace.print_constraint(cout);
              cout <<"} ----" << endl << endl;
            }
#endif

            /* Now we do the pred check to find the exists placeholder;
             * This involves the predCheck method and checking that time can
             * can elapse. Note that the exists is a simplified version
             * where \phi_2 (the right) is the relativized clause and
             * \phi_1 (the left) is the formula. By using the placeholders
             * computed previously, we save time by not having to recompute
             * the formulas. */
            DBMList currRetPlaceDBM(*retPlaceDBM);
            DBMList phi1PredPlace(phi1Place);
            phi1PredPlace.pre();
            phi1PredPlace.cf();
            /*--- PredCheck code----*/
            retPlaceDBM = predCheckRule(lhs, &ph, NULL, &phi2Place, &phi1Place, &phi1PredPlace);
            retPlaceDBM->cf();
#if DEBUG
            if(debug) {
              cout <<"----() FORALL Rel Exists placeholder obtained as := {";
              retPlaceDBM->print_constraint(cout);
              cout << "} ----"<< endl << endl;
            }
#endif
            if(retPlaceDBM->emptiness()) {

            }
            else {
              /* if it is nonempty, it passes the second check and we continue
               * Given the FORALL rule rewrite, do not allow the instance
               * after the time elapse. */
              /* Extract the new refined placeholder. */
              *retPlaceDBM & phi1Place;
              retPlaceDBM->cf();


              /* Now check that it works. */
              /* Since we are not using retPlace anymore, we do not
               * need to copy it for the check. */
              retPlaceDBM->pre();
              /* This cf() is needed. */
              retPlaceDBM->cf();
              // check elapse further?
#if DEBUG
              if (debug) {
                print_sequentCheck(cout, step - 1, retVal, lhs, retPlaceDBM, sub, rhs->getOpType());

                cout <<"----() FORALL Rel Exists placeholder after time elapse check is := {";
                retPlaceDBM->print_constraint(cout);
                cout << "} ----"<< endl << endl;
              }
#endif
            }
            // retPlaceDBM is existsPlace
            /* Last, we do an "or" check on the two placeholders */
            bool forallEmpty = forallPlace.emptiness();
            bool existsEmpty = retPlaceDBM->emptiness();
            retVal = true;
            if(forallEmpty && existsEmpty) {
              retPlaceDBM->makeEmpty();
              retVal = false;
            }
            else if(forallEmpty) {

            }
            else if (existsEmpty) {
              *retPlaceDBM = forallPlace;
            }
            else {
              if(forallPlace <= *retPlaceDBM) {

              }
              else if (*retPlaceDBM <= forallPlace) {
                *retPlaceDBM = forallPlace;
              }
              else {
                /* This case requires us to union the two placeholders. */
                retPlaceDBM->addDBMList(forallPlace);
              }
            }
            // retVal is computed above
          }
#if DEBUG
          if(debug) {
            cout << "Final Placeholder of FORALL_REL (P): ";
            retPlaceDBM->print_constraint(cout);
            cout << endl << endl;
          }
#endif

          delete fPlace;
        }
        delete tPlace;
      }
      break;
    }
    case EXISTS:{

      /* First try to get a new placeholder value that works */
      lhs->cf();
      place->cf();
      DBM ph(*lhs);
      ph.suc();
      // The invariant goes into the placeholder, not the left hand side
      DBMList tPlace(*INFTYDBM);
      invs_chk(input_pes.invariants(), &tPlace, *sub);

      //DBMList * tempPlace = new DBMList(*retPlaceDBM);
      retPlaceDBM = do_proof_place(step, &ph, &tPlace,
                                   rhs->getQuant(), sub);
      retPlaceDBM->cf();
      if(retPlaceDBM->emptiness()){
        if (debug) {
          print_sequentCheck(cout, step - 1, retVal, &ph, retPlaceDBM, sub, rhs->getOpType());

          cout <<"----(Invalid) Empty First Placeholder: No Need for additional Placeholder Checks-----" << endl << endl;
        }
        retVal = false;
        break;
      }
      /* Now check that it works (the new placeholder can be
       * obtained from the old
       * For the placeholder rule, we use this check
       * to give us the value of the old placeholder */
      retPlaceDBM->pre();
      (*place) & (*retPlaceDBM);
      place->cf();
      *retPlaceDBM = (*place);
      if(place->emptiness()) {
        retVal = false;
      }
      else {
        retVal = true;
      }
#if DEBUG
      if (debug) {
        print_sequent_placeCheck(cout, step - 1, retVal, lhs, place, retPlaceDBM, sub, rhs->getOpType());
        if(retVal) {
          cout <<"----(Valid) Placeholder Check Passed-----" << endl
          <<"--With Placeholder := {";
          retPlaceDBM->print_constraint(cout);
          cout <<"} ----" << endl << endl;
        }
        else {
          cout <<"----(Invalid) Placeholder Check Failed-----" << endl << endl;

        }
      }
#endif

      break;
    }
    case EXISTS_REL: {
      /* First Try to get a placeholder value that works */
      lhs->cf();
      place->cf();
      DBM ph(*lhs);
      ph.suc();
      DBM phb(ph);

      DBMList * tPlace = new DBMList(*INFTYDBM);
      invs_chk(input_pes.invariants(), tPlace, *sub);

      retPlaceDBM = do_proof_place(step, &ph, tPlace,
                                   rhs->getRight(), sub);
      // Reset place parent to NULL
      parentPlaceRef = NULL;
      retPlaceDBM->cf();
      if(retPlaceDBM->emptiness()){
        retVal = false;
        if (debug) {
          print_sequentCheck(cout, step - 1, retVal, lhs, retPlaceDBM, sub, rhs->getOpType());

          cout <<"----(Invalid) Empty First Placeholder: No Need for additional Placeholder Checks-----" << endl << endl;
        }
        delete tPlace;
        break;
      }
      retVal = true;
      /* Now check for the relativization.
       * First, find the subset of the predecessor_< of the placeholder
       * that satisfies the left clause.
       * Second: utilize a pred_check() method to further tighten the
       * placeholder in order that all  */
      /* First step */
      DBMList * phi2PredPlace = new DBMList(*retPlaceDBM);
      phi2PredPlace->pre();
      // pred Closure makes sure that the exact valuation for the placeholder
      // is excluded.
      phi2PredPlace->predClosureRev();
      phi2PredPlace->cf();
      /* At this point, phi2PredPlace is the time predecessor_{<} of the placeholders
       * that satisfy phi_2, the right hand formula */

      /* We find all the times that satisfy phi_1, and then intersect it
       * with the time predecessor of the phi_2 placeholders. */
      DBMList * phi2Place = new DBMList(*retPlaceDBM);
      DBMList place1Temp(*INFTYDBM);
      retPlaceDBM = do_proof_place(step, &phb, &place1Temp, rhs->getLeft(), sub);
      /* Second step: tighten and check the predecessor */
      // Must check for emptiness to handle the corner case when it is empty
      DBMList phi1Place(*retPlaceDBM);
#if DEBUG
      if(debug) {
        cout <<"----() Placeholder of times where \\phi_1 is true----- {";
        phi1Place.print_constraint(cout);
        cout << "} ----"<< endl << endl;
      }
#endif
      *retPlaceDBM & *phi2PredPlace;
      retPlaceDBM->cf();
      if(retPlaceDBM->emptiness()) {
        retVal = false;
#if DEBUG
        if(debug) {
          print_sequentCheck(cout, step - 1, retVal, &phb, retPlaceDBM, sub, rhs->getOpType());

          cout <<"----() Empty Second Placeholder: Relativization Formula \\phi_1 is never true-----" << endl << endl;
        }
#endif
        /* Now determine if $\phi_2$ is true without a time elapse.
         * If so, make a non-empty placeholder. In this case, the third
         * Check will be true by default and can be skipped.
         * Else, return empty and break */
        *phi2Place & *lhs; // lhs here is before the time elapse
        phi2Place->cf();
        if(phi2Place->emptiness()) {
          retVal = false;
#if DEBUG
          if(debug) {

            cout << "----(Invalid) Time Elapsed required for formula to be true; hence, relativized formula cannot always be false." << endl << endl;
          }
#endif
        }
        else {
          /* While a time elapse is not required, the placeholder
           * must span all of lhs */
          retVal = (*phi2Place) >= (*lhs);

#if DEBUG
          if(debug) {
            if(retVal) {
              cout <<"----(Valid) Time Elapse not required and placeholder spans lhs; hence, formula is true-----" << endl
              << "----With resulting Placeholder := {";
              phi2Place->print_constraint(cout);
              cout << "} ----"<< endl << endl;
            }
            else {
              cout <<"----(Invalid) While Time Elapse not required, placeholder is not large enough-----" << endl
              << "----With resulting Placeholder := {";
              phi2Place->print_constraint(cout);
              cout << "} ----"<< endl << endl;
            }

          }
#endif
        }


        delete phi2Place;
        delete phi2PredPlace;
        delete tPlace;
        break;
      }

      DBMList currRetPlaceDBM(*retPlaceDBM);
      /*--- PredCheck code----*/
      retPlaceDBM = predCheckRule(lhs, &ph, NULL, &phi1Place, phi2Place, phi2PredPlace);
      if(retPlaceDBM->emptiness()) {
        retVal = false;
#if DEBUG
        if(debug) {
          cout <<"----(Invalid) Relativization placeholder failed-----" << endl
          << "----With resulting Placeholder := {";
          retPlaceDBM->print_constraint(cout);
          cout << "} ----"<< endl << endl;
        }
#endif
        delete phi2Place;
        delete phi2PredPlace;
        delete tPlace;
        break;
      }

      // if it is still nonempty, it passes the second check and we continue

      //}
#if DEBUG
      if(debug) {
        print_sequent_place(std::cout, step - 1,  retVal, &phb, phi2PredPlace, rhs->getLeft(), sub, rhs->getOpType());
        cout <<"----(Valid) Relativization Placeholder Check Passed (Check Only)-----" << endl
        << "----With resulting Placeholder := {";
        retPlaceDBM->print_constraint(cout);
        cout << "} ----"<< endl << endl;
      }
#endif

      // Allow for the possibility of the time instant after the elapse
      retPlaceDBM->closure();
      /* Extract the new refined placeholder */
      *phi2Place & *retPlaceDBM;
      phi2Place->cf();

      /* Now check that it works (the new placeholder can be
       * obtained from the old
       * For the placeholder rule, we use this check
       * to give us the value of the old placeholder */
      phi2Place->pre();
      (*place) & (*phi2Place);
      place->cf();
      *retPlaceDBM = (*place);
      if(retPlaceDBM->emptiness()) {
        retVal = false;
      }
      else {
        retVal = true;
      }
#if DEBUG
      if (debug) {
        print_sequent_placeCheck(cout, step - 1, retVal, lhs, place, retPlaceDBM, sub, rhs->getOpType());
        if(retVal) {
          cout <<"----(Valid) Final Placeholder Check Passed-----" << endl
          <<"--With Placeholder := {";
          retPlaceDBM->print_constraint(cout);
          cout <<"} ----" << endl << endl;
        }
        else {
          cout <<"----(Invalid) Final Placeholder Check Failed-----" << endl << endl;

        }
      }
#endif




      delete phi2PredPlace;
      delete phi2Place;
      delete tPlace;
      break;
    }
    case ALLACT: {

      retVal = true;
      *retPlaceDBM = (*place);
      /* Enumerate through all transitions */
#if DEBUG
      if(debug) {
        cout << "\t Proving ALLACT Transitions:----\n" << endl;
      }
#endif
      /* For reasons to avoid convexity until the end, find all of the
       * placeholders for each clause individually. For all transitions
       * that can be executed, store the resulting placeholders with transitions
       * so that we only need to give a non-convex placeholder when finished */
      vector<DBMList * > transPlaceHolders;
      bool emptyRetPlace = false;
      for(vector<Transition *>::const_iterator it = input_pes.transitions().begin();
          it != input_pes.transitions().end(); it++ ) {
        Transition * tempT = *it;

        /* Obtain the entire ExprNode and prove it */
        DBM tempLHS(*lhs);

        DBMList guardPlace(*place);
        bool tempBool = comp_ph_all_place(&tempLHS, &guardPlace, *(tempT->getLeftExpr()), *sub);
        if(tempBool == false) {
#if DEBUG
          if (debug) {
            cout << "Transition: ";
            print_Transition(tempT, cout);
            cout << " cannot be taken." << endl;
          }
#endif
          continue;
        }
        /* Now guardPlace has the largest placeholder satisfying the
         * guard. Note that we use tempPlace for the proof. guardPlace
         * is used later to restrict the placeholder if needed. */

        /* Now check the invariant */
        DBMList transPlace(*place);
        DBM phLHS(tempLHS);
        DBM invPlace(*INFTYDBM);
        SubstList tSub(*sub);
        const SubstList * sl = tempT->getEnteringLocation(&tSub);
        bool isInv = invs_chk(input_pes.invariants(), &invPlace, *sl);
        delete sl;
        if(isInv) {
          invPlace.cf();
          const ClockSet * st = tempT->getCSet();
          if(st != NULL) {
            invPlace.preset(st);
          }
          invPlace.cf();
          /* Now perform clock assignments sequentially: perform the
           * front assignments first */
          const vector<pair<short int, short int> > * av = tempT->getAssignmentVector();
          if(av != NULL) {
            // Iterate over the vector and print it
            for(vector<pair<short int, short int> >::const_iterator it=av->begin(); it != av->end(); it++) {
              invPlace.preset((*it).first, (*it).second);
              invPlace.cf();
            }
          }
          // Now invPlace has the largest placeholder satisfying
          // the invariant

          /* Check if invariant preset is satisfied by the lhs.
           * If not, tighten the placeholder */

          if(!(phLHS <= invPlace)) {
            phLHS & invPlace;
            phLHS.cf();
            if(phLHS.emptiness()) {
#if DEBUG
              if (debug) {
                cout << "Transition: ";
                print_Transition(tempT, cout);
                cout << " cannot be taken; entering invariant is false." << endl;
                cout << "\tExtra invariant condition: ";
                invPlace.print_constraint(cout);
                cout << endl;
              }
#endif
              continue;
            }
            transPlace & invPlace;
            transPlace.cf();
          }
        }


        tempT->getNewTrans(rhs->getQuant());
        /* Constraints are bounded by MAXC */
        /* This is to extend the LHS to make sure that
         * the RHS is satisfied by any zone that satisfies
         * the LHS by expanding the zone so it contains
         * all the proper regions where the clocks
         * exceed a certain constant value. */
        phLHS.cf();
        phLHS.bound(MAXC);
        SubstList tempSub(*sub);
        // The transition RHS handles resets and substitutions
#if DEBUG
        if (debug) {
          cout << "Executing transition (with destination) ";
          print_Transition(tempT, cout);
          cout << endl;
        }
#endif
        // use phLHS since the lhs is tightened to satisfy
        // the invariant
        numLocations++;
        retPlaceDBM = do_proof_place(step, &phLHS, &transPlace, tempT->getRightExpr(), &tempSub);
        retPlaceDBM->cf();
        /* Given ALLAct, this segment may require zone unions. */
        if(retPlaceDBM->emptiness()) {
          // Code here
          DBMList * newPlace;
          DBMList invList(invPlace);
          !invList;
          invList.cf();
          !guardPlace;
          guardPlace.cf();
          // Now combine the placeholders
          bool invEmpty = invList.emptiness();
          bool guardEmpty = guardPlace.emptiness();
          if(invEmpty && guardEmpty) {
            // This means that no such placeholder is possible
            retPlaceDBM->makeEmpty();
            emptyRetPlace = true;
            break;
          }
          else if(invEmpty) {
            newPlace = new DBMList(guardPlace);
          }
          else if(guardEmpty) {
            newPlace = new DBMList(invList);
          }
          else if(invList <= guardPlace) {
            newPlace = new DBMList(guardPlace);
          }
          else if(guardPlace <= invList) {
            newPlace = new DBMList(invList);
          }
          else {
            /* This is the bad case, because zone unions are required */
            newPlace = new DBMList(guardPlace);
            newPlace->addDBMList(invList);
          }
          transPlaceHolders.push_back(newPlace);
          continue;
        }
        DBMList tempPlace(transPlace);
        tempPlace & phLHS;
        tempPlace.cf();
        if (*retPlaceDBM >= tempPlace) {
          /* This is the good case, since our placeholder need not
           * be restricted. Hence, we need not do anything here */

        }
        else {
          // Here tempRetDBM (retPlaceDBM) < tempLHSCp, meaning a restricted placeholder
          // Same code as when empty, but we have another placeholder
          DBMList * newPlace;
          DBMList invList(invPlace);
          !invList;
          invList.cf();
          !guardPlace;
          guardPlace.cf();
          // Now combine the placeholders
          bool invEmpty = invList.emptiness();
          bool guardEmpty = guardPlace.emptiness();
          // we know that tempPlace is not empty
          if(invEmpty && guardEmpty) {
            // This means that no such placeholder is possible
            newPlace = new DBMList(transPlace);
          }
          else {
            if(invEmpty) {
              newPlace = new DBMList(guardPlace);
            }
            else if(guardEmpty) {
              newPlace = new DBMList(invList);
            }
            else if(invList <= guardPlace) {
              newPlace = new DBMList(guardPlace);
            }
            else if(guardPlace <= invList) {
              newPlace = new DBMList(invList);
            }
            else {
              /* This is the bad case, because zone unions are required */
              newPlace = new DBMList(guardPlace);
              newPlace->addDBMList(invList);
            }
            /* Like OR, we now handle the tempPlace.
             * However, we know that both are not empty */
            if(tempPlace <= *newPlace) {
              // nothing needs to be done here
            }
            else if(*newPlace <= tempPlace) {
              delete newPlace;
              newPlace = new DBMList(tempPlace);
            }
            else {
              /* This is the bad case, because zone unions are required */
              newPlace->addDBMList(transPlace);
            }
          }
          transPlaceHolders.push_back(newPlace);
        }
      }
      /* Handle the vector */
      if(!(transPlaceHolders.empty()) && !(emptyRetPlace)) {
        /* If the vector is empty, then there is nothing to do
         * since retPlaceDBM = place already; hence, we only
         * handle the case with a non-empty placeholder. */
        // For now, just intersect the placeholders
        *retPlaceDBM = *place;
        for(  vector<DBMList * >::iterator it = transPlaceHolders.begin(); it != transPlaceHolders.end(); it++) {
          /* Intersecting alone is not good enough, so need to do both */
          *retPlaceDBM & *(*it);
          retPlaceDBM->cf();
        }

      }
      if(retPlaceDBM->emptiness()) {
        retVal = false;

      }
      else {
        retVal = true;
      }
      // Now go through the vector and delete everything in the vector
      // (Don't delete the transitions since we passed references,
      // but do delete the DBMLists since we passed copies)
      for(  vector< DBMList * >::iterator it = transPlaceHolders.begin(); it != transPlaceHolders.end(); it++) {
        delete (*it);
      }
      transPlaceHolders.clear();

#if DEBUG
      if(debug) {
        cout << "\t --- end of ALLACT. Returned plhold: ";
        retPlaceDBM->print_constraint(cout);
        cout << endl;
      }
#endif

      break;
    }
    case EXISTACT: {
      retVal = false;
      retPlaceDBM->makeEmpty();
      /* Enumerate through all transitions */
#if DEBUG
      if(debug) {
        cout << "\t Proving EXISTACT Transitions:----\n" << endl;
      }
#endif
      for(vector<Transition *>::const_iterator it = input_pes.transitions().begin();
          it != input_pes.transitions().end(); it++ ) {
        Transition * tempT = *it;

        /* Obtain the entire ExprNode and prove it */

        DBMList tempPlace(*place);
        DBM tempLHS(*lhs);
        // Method tightens lhs and place
        bool tempBool = comp_ph_exist_place(&tempLHS, &tempPlace, *(tempT->getLeftExpr()), *sub);
        if(tempBool == false) {
#if DEBUG
          if (debug) {
            cout << "Transition: ";
            print_Transition(tempT, cout);
            cout << " cannot be taken." << endl;
          }
#endif
          continue;
        }

        /* Now check the invariant */
        DBM invCons(*INFTYDBM);
        SubstList tSub(*sub);
        const SubstList * sl = tempT->getEnteringLocation(&tSub);
        bool isInv = invs_chk(input_pes.invariants(), &invCons, *sl);
        delete sl;
        if(isInv) {
          invCons.cf();
          const ClockSet * st = tempT->getCSet();
          if(st != NULL) {
            invCons.preset(st);
          }
          invCons.cf();
          /* Now perform clock assignments sequentially: perform the
           * front assignments first */
          const vector<pair<short int, short int> > * av = tempT->getAssignmentVector();
          if(av != NULL) {
            // Iterate over the vector and print it
            for(vector<pair<short int, short int> >::const_iterator it=av->begin(); it != av->end(); it++) {
              invCons.preset((*it).first, (*it).second);
              invCons.cf();
            }
          }
          /* Check if invariant preset is satisfied by the lhs.
           * If not, tighten the placeholder */
          // For performace reasons, also tighten the left hand side
          if(!(tempLHS <= invCons)) {
            tempPlace & invCons;
            tempPlace.cf();
            if(tempPlace.emptiness()) {
#if DEBUG
              if (debug) {
                cout << "Transition: ";
                print_Transition(tempT, cout);
                cout << " cannot be taken; entering invariant is false." << endl;
                cout << "\tExtra invariant condition: ";
                invCons.print_constraint(cout);
                cout << endl;
              }
#endif
              continue;
            }
            tempLHS & invCons;
            tempLHS.cf();
          }
        }

        tempT->getNewTrans(rhs->getQuant());
        /* Constraints are bounded by MAXC */
        /* This is to extend the LHS to make sure that
         * the RHS is satisfied by any zone that satisfies
         * the LHS by expanding the zone so it contains
         * all the proper regions where the clocks
         * exceed a certain constant value. */

        // for performance reasons, also tighten LHS with invariant

        tempLHS.bound(MAXC);
        SubstList tempSub(*sub);
        DBMList tPlace1(tempPlace);
        DBMList prevDBM(*retPlaceDBM);
#if DEBUG
        if (debug) {
          cout << "Executing transition (with destination) ";
          print_Transition(tempT, cout);
          cout << endl;
          cout << "\tExtra invariant condition: ";
          invCons.print_constraint(cout);
          cout << endl;
        }
#endif
        numLocations++;
        retPlaceDBM = do_proof_place(step, &tempLHS, &tPlace1, tempT->getRightExpr(), &tempSub);
        retPlaceDBM->cf();
        /* placeholder logic partially incomplete
         * due to not addressing when new placeholder
         * is incomparable to the previous */
        if(retPlaceDBM->emptiness()) {
          *retPlaceDBM = (prevDBM);
        }
        else if(*retPlaceDBM >= *place) {
          /* Here, the current transition successful;
           * we are done */
          retVal = true;
          break;
        }
        else if(prevDBM.emptiness()){
        }
        else if(*retPlaceDBM <= prevDBM) {
          *retPlaceDBM = (prevDBM);
        }
        else if (prevDBM <= *retPlaceDBM) {
          retVal = true;
          /* here, we keep retPlaceDBM as our current. */
        }
        else { /* Corner Case: make a union of DBMLists */
          retPlaceDBM->addDBMList(prevDBM);
          retPlaceDBM->cf();
        }


      }
#if DEBUG
      if(debug) {
        cout << "\t --- end of EXISTACT. Returned plhold: ";
        retPlaceDBM->print_constraint(cout);
        cout << endl;
      }
#endif
      break;
    }
    case IMPLY:{
      DBM tempLHS(*lhs);
      /* call comp_ph() for efficient proving of IMPLY's left. */
      if(comp_ph(&tempLHS, *(rhs->getLeft()), *sub)){
        /* Constraints are bounded by MAXC */
        /* This is to extend the LHS to make sure that
         * the RHS is satisfied by any zone that satisfies
         * the LHS by expanding the zone so it contains
         * all the proper regions where the clocks
         * exceed a certain constant value. */
        tempLHS.cf();
        tempLHS.bound(MAXC);
        retPlaceDBM = do_proof_place(step, &tempLHS, place, rhs->getRight(), sub);
      }
      else  {
        /* The set of states does not satisfy the premises of the IF
         * so thus the proof is true */
        retVal = true;
        *retPlaceDBM = (*place);
#if DEBUG
        if (debug) {
          cout << "---(Valid) Leaf IMPLY Reached, Premise Not Satisfied----" << endl << endl;
        }
#endif
      }
      break;}
    case CONSTRAINT:{
      lhs->cf();
      // The line: (rhs->dbm())->cf(); is not needed.
      retVal = (*lhs <= *(rhs->dbm()));
      if(retVal == true) {
        *retPlaceDBM = (*place);

#if DEBUG
        if (debug && retVal) {
          cout << "---(Valid) Leaf DBM (CONSTRAINT) Reached with no need for Placeholder----" << endl << endl;
        }
        if (debug && !retVal) {
          cout << "---(Valid, Placeholder) Leaf DBM (CONSTRAINT) Reached and Placeholder Computed----" << endl <<
          "----Placeholder := {";
          retPlaceDBM->print_constraint(cout);
          cout << "}----" << endl << endl;
        }
#endif
      }
      else {
        /* Here, since we only have a single constrait here,
         * DBM will tighten only to match the single constraint
         * Since multiple constraints are represented as an
         * AND of Constraints */
        *retPlaceDBM = (*place);
        *retPlaceDBM & (*(rhs->dbm()));
        retPlaceDBM->cf();

        // Now test constraint
        DBMList tPlace(*retPlaceDBM);
        tPlace & *lhs;

        tPlace.cf();
        retVal = !(tPlace.emptiness());
        if(!retVal)
        {
          // New Combined DBM Does not satisfy Constraint
          retPlaceDBM->makeEmpty();
        }
#if DEBUG
        if (debug && retVal) {
          cout << "---(Valid, Placeholder) Leaf DBM (CONSTRAINT) Reached and Placeholder Computed----" << endl <<
          "----Placeholder := {";
          retPlaceDBM->print_constraint(cout);
          cout << "}----" << endl << endl;
        }
        if (debug && !retVal) {
          cout << "---(Invalid, Placeholder) Leaf DBM (CONSTRAINT) Unsatisfied regardless of placeholder----" << endl << endl;
        }
#endif
      }

      break;}
    case BOOL:{
      retVal = (rhs->getBool());
      if(retVal) {
        *retPlaceDBM = (*place);
      }
      else{
        retPlaceDBM->makeEmpty();
      }
#if DEBUG
      if (debug && retVal) {
        cout << "---(Valid) Leaf BOOL Reached----" << endl << endl;
      }
      if (debug && !retVal) {
        cout << "---(Invalid) Leaf BOOL Reached----" << endl << endl;
      }
#endif
      break;}
    case ATOMIC:{
      retVal = (sub->at(rhs->getAtomic()) == rhs->getIntVal());
      if(retVal) {
        *retPlaceDBM = (*place);
      }
      else{
        retPlaceDBM->makeEmpty();
      }
#if DEBUG
      if (debug && retVal) {
        cout << "---(Valid) Leaf ATOMIC == Reached----" << endl << endl;
      }
      if (debug && !retVal) {
        cout << "---(Invalid) Leaf ATOMIC == Reached----" << endl << endl;
      }
#endif
      break;}
    case ATOMIC_NOT:{
      retVal = (sub->at(rhs->getAtomic()) != rhs->getIntVal());
      if(retVal) {
        *retPlaceDBM = (*place);
      }
      else{
        retPlaceDBM->makeEmpty();
      }
#if DEBUG
      if (debug && retVal) {
        cout << "---(Valid) Leaf ATOMIC != Reached----" << endl << endl;
      }
      if (debug && !retVal) {
        cout << "---(Invalid) Leaf ATOMIC != Reached----" << endl << endl;
      }
#endif
      break;}
    case ATOMIC_LT:{
      retVal = (sub->at(rhs->getAtomic()) < rhs->getIntVal());
      if(retVal) {
        *retPlaceDBM = (*place);
      }
      else{
        retPlaceDBM->makeEmpty();
      }
#if DEBUG
      if (debug && retVal) {
        cout << "---(Valid) Leaf ATOMIC < Reached----" << endl << endl;
      }
      if (debug && !retVal) {
        cout << "---(Invalid) Leaf ATOMIC < Reached----" << endl << endl;
      }
#endif
      break;}
    case ATOMIC_GT:{
      retVal = (sub->at(rhs->getAtomic()) > rhs->getIntVal());
      if(retVal) {
        *retPlaceDBM = (*place);
      }
      else{
        retPlaceDBM->makeEmpty();
      }
#if DEBUG
      if (debug && retVal) {
        cout << "---(Valid) Leaf ATOMIC > Reached----" << endl << endl;
      }
      if (debug && !retVal) {
        cout << "---(Invalid) Leaf ATOMIC > Reached----" << endl << endl;
      }
#endif
      break;}
    case ATOMIC_LE:{
      retVal = (sub->at(rhs->getAtomic()) <= rhs->getIntVal());
      if(retVal) {
        *retPlaceDBM = (*place);
      }
      else{
        retPlaceDBM->makeEmpty();
      }
#if DEBUG
      if (debug && retVal) {
        cout << "---(Valid) Leaf ATOMIC < Reached----" << endl << endl;
      }
      if (debug && !retVal) {
        cout << "---(Invalid) Leaf ATOMIC < Reached----" << endl << endl;
      }
#endif
      break;}
    case ATOMIC_GE:{
      retVal = (sub->at(rhs->getAtomic()) >= rhs->getIntVal());
      if(retVal) {
        *retPlaceDBM = (*place);
      }
      else{
        retPlaceDBM->makeEmpty();
      }
#if DEBUG
      if (debug && retVal) {
        cout << "---(Valid) Leaf ATOMIC > Reached----" << endl << endl;
      }
      if (debug && !retVal) {
        cout << "---(Invalid) Leaf ATOMIC > Reached----" << endl << endl;
      }
#endif
      break;}
    case SUBLIST:{
      SubstList st(rhs->getSublist(), sub );
      retPlaceDBM = do_proof_place(step, lhs, place, rhs->getExpr(), &st);
      break;}
    case RESET:{
      // Bound the LHS to prevent infinite proofs
      lhs->cf();
      lhs->bound(MAXC);
      lhs->cf();
      DBM ph(*lhs);
      const ClockSet *rs = rhs->getClockSet();
      ph.reset(rs);

      DBMList tPlace(*INFTYDBM);
      retPlaceDBM = do_proof_place(step, &ph, &tPlace, rhs->getExpr(), sub);
      retPlaceDBM->cf();
      if(!(retPlaceDBM->emptiness())) {
        /* Now do the check that the new placeholder follows from
         * the previous placeholder. by setting it to such */
        DBMList p2Copy(*retPlaceDBM);
        // Apply the reset (weakest precondition operator)
        const ClockSet *rsb = rhs->getClockSet();
        p2Copy.preset(rsb);

        // Use the rule to compute what the old place holder should be
        (*place) & p2Copy;
        place->cf();
        if(place->emptiness()){
          retVal = false;
          retPlaceDBM->makeEmpty();
        }
        else{
          retVal = true;
          *retPlaceDBM = (*place);
        }
#if DEBUG
        if (debug) {
          print_sequent_placeCheck(cout, step - 1, retVal, lhs, retPlaceDBM, &p2Copy, sub, rhs->getOpType());
          if(retVal) {
            cout <<"----(Valid) Placeholder Check Passed-----" << endl
            <<"--With Placeholder := {";
            retPlaceDBM->print_constraint(cout);
            cout <<"} ----" << endl << endl;
          }
          else {
            cout <<"----(Invalid) Placeholder Check Failed-----" << endl << endl;

          }
        }
#endif
      }
      break;}
    case ASSIGN:{
      // use lhs->cf() for more efficiency
      lhs->cf();
      DBM ph(*lhs);
      /* Here the DBM zone is where the value of
       * clock x is reset to clock y, which is possibly
       * a constant or a value*/
      short int cX = rhs->getcX();
      short int cY = rhs->getcY();
      ph.reset(cX, cY);
      DBMList placeB(*INFTYDBM);
      retPlaceDBM = do_proof_place(step, &ph, &placeB, rhs->getExpr(), sub);
      retPlaceDBM->cf();
      if(!(retPlaceDBM->emptiness())) {
        // Double Check that the new placeholder follows from the first
        DBMList tmp2(*retPlaceDBM);
        tmp2.preset(cX, cY);

        // Now assign the old placeholder accordingly
        (*place) & tmp2;
        place->cf();
        if(!(place->emptiness())){ // If so, return old place holder with solved value
          retVal = true;
          *retPlaceDBM = (*place);
        }
        else{
          retVal = false;
          retPlaceDBM->makeEmpty();
        }
#if DEBUG
        if (debug) {
          print_sequent_placeCheck(cout, step - 1, retVal, lhs, place, &tmp2, sub, rhs->getOpType());
          if(retVal) {
            cout <<"----(Valid) Placeholder Check Passed-----" << endl
            <<"--With Placeholder := {";
            retPlaceDBM->print_constraint(cout);
            cout <<"} ----" << endl << endl;
          }
          else {
            cout <<"----(Invalid) Placeholder Check Failed-----" << endl << endl;

          }
        }
#endif
      }
      break; }
    case REPLACE:{
      sub->operator[](rhs->getcX()) = sub->at(rhs->getcY());
      retPlaceDBM = do_proof_place(step, lhs, place, rhs->getExpr(), sub);
      break; }
    case ABLEWAITINF:{
      lhs->cf();
      DBMList ph(*lhs);
      ph & *place;
      ph.cf();
      ph.suc();
      invs_chk(input_pes.invariants(), &ph, *sub);
      ph.cf();
      /* Time can diverge if and only if there are no upper bound
       * constraints in the successor. By design of succ() and invariants,
       * either all DBMs have an upper bound constraint, or none
       * of them do. Hence, checking the first is always good enough. */
      vector <DBM *> * currList = ph.getDBMList();
      DBM * currDBM = (*currList)[0];
      retVal = !(currDBM->hasUpperConstraint());
      if(retVal) {
        *retPlaceDBM = (*place);
      }
      else{
        retPlaceDBM->makeEmpty();
      }
#if DEBUG
      if (debug && retVal) {
        cout << "---(Valid) Time able to diverge to INFTY in current location----" << endl << endl;
      }
      if (debug && !retVal) {
        cout << "---(Invalid) Time unable to diverge to INFTY in current location---" << endl << endl;
      }
#endif
      break;}
    case UNABLEWAITINF:{
      lhs->cf();
      DBMList ph(*lhs);
      ph & *place;
      ph.cf();
      ph.suc();
      invs_chk(input_pes.invariants(), &ph, *sub);
      ph.cf();
      /* Time canot diverge if and only if there is an upper bound
       * constraint in the successor. By design of succ() and invariants,
       * either all DBMs have an upper bound constraint, or none
       * of them do. Hence, checking the first is always good enough. */
      vector <DBM *> * currList = ph.getDBMList();
      DBM * currDBM = (*currList)[0];
      retVal = currDBM->hasUpperConstraint();
      if(retVal) {
        *retPlaceDBM = (*place);
      }
      else{
        retPlaceDBM->makeEmpty();
      }
#if DEBUG
      if (debug && retVal) {
        cout << "---(Valid) Time unable to diverge to INFTY in current location----" << endl << endl;
      }
      if (debug && !retVal) {
        cout << "---(Invalid) Time able to diverge to INFTY in current location---" << endl << endl;
      }
#endif
      break;}
    default:
      cout <<"ERROR, OPERATOR NOT DEFINED" << endl;
  }

  return retPlaceDBM;
}
