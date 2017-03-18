/** \file proof.hh
 * Header file for proof
 * @author Jeroen Keiren
 * @version 1.21
 * @date June 21, 2016 */

#ifndef PROOF_HH
#define PROOF_HH

#include "cpplogging/logger.h"
#include "pes.hh"
#include "DBM.hh"
#include "ExprNode.hh"
#include "transition.hh"
#include "comp_ph.hh"
#include "sequent_cache.hh"

class prover
{
protected:
  const pes& input_pes;

  bool currParityGfp;
  bool prevParityGfp;
  bool useCaching;

  long int numLocations;

  /** This parameter is the size of the maximum
   * constant (in the clock constraints).  There
   * is one constant for all of the clocks
   * This is modified by the program and the parser. */
  const int MAXC;

  /** This DBM is a copy of a DBM initially
   * that represents the unconstrained DBM in
   * canonical form. */
  DBM *INFTYDBM;

  /** DBMList used as the value of the returned placeholder.
   * this is initialized outside of do_proof_place() to prevent
   * multiple re-initializations of it. */
  DBMList * retPlaceDBM;

  /** Global variable that keeps track of the parent sequent
   * of the current sequent in the proof tree. Used for sequents
   * without placeholder parents, and used to help generate backpointers
   * in the proof tree. */
  Sequent * parentRef;

  /** Global variable that keeps track of the parent placeholder sequent
   * of the current sequent in the proof tree. Used for sequents
   * with placeholder parents, and used to help generate backpointers
   * in the proof tree. */
  SequentPlace * parentPlaceRef;

  /** A boolean used to tell if the located sequent was
   * newly-added to the cache. If it is true, then that sequent
   * has no left-hand clock states, and is empty; hence, it need
   * not be examined by table-sequent.*/
  bool newSequent;

  /** Cache for storing sequents. This incorporates true and false sequents, as
   * well as sequents for predicate variables in order to detect cycles.
   */
  sequent_cache cache;

public:
  prover(const pes& input_pes,
         bool currParityGfp, bool prevParityGfp, bool useCaching,
         int nHash, bool debug, int MAXC,
         int nbits) :
  input_pes(input_pes),
  currParityGfp(currParityGfp),
  prevParityGfp(prevParityGfp),
  useCaching(useCaching),
  numLocations(1),
  MAXC(MAXC),
  cache(input_pes, nbits, input_pes.predicates().size()*nHash, nHash, newSequent)
  {
    cpplogging::logger::register_output_policy(cpplogging::plain_output_policy());
    cpplogging::logger::unregister_output_policy(cpplogging::default_output_policy());

    if(debug)
    {
      cpplogging::logger::set_reporting_level(cpplogging::debug);
    }

    /* This is initialized to be the largest (loosest)
     * possible DBM
     * @see DBM Constructor (Default Constructor). */
    INFTYDBM = new DBM(input_pes.spaceDimension(), input_pes.clocks());
    INFTYDBM->cf();

    retPlaceDBM = new DBMList(*INFTYDBM);

    /* Initialize parent sequents to NULL */
    parentRef = NULL;
    parentPlaceRef = NULL;

    newSequent = true;
  };

  ~prover()
  {
    delete INFTYDBM;
    delete retPlaceDBM;
  };

  long int getNumLocations() const
  {
    return numLocations;
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
  __attribute__((flatten))
  bool do_proof(int step, DBM * const lhs, const ExprNode * const rhs, SubstList * const sub)
  {
    bool retVal = false;
    if (cpplogEnabled(cpplogging::debug)){
      lhs->cf(); // FIXME: why do we transform the DBM to canonical form just for this debug print?
      print_sequent(std::cerr, step, retVal, lhs, rhs, sub, rhs->getOpType());
    }
    step++;

    switch(rhs->getOpType()){
      case PREDICATE:{
        return do_proof_predicate(step, lhs, rhs, sub);
      }
      case AND:
      {
        return do_proof_and(step, lhs, rhs, sub);
      }
      case OR:{
        return do_proof_or(step, lhs, rhs, sub);
      }
      case OR_SIMPLE:{
        return do_proof_or_simple(step, lhs, rhs, sub);
      }
      case FORALL:{
        return do_proof_forall(step, lhs, rhs, sub);
      }
      case FORALL_REL: {
        return do_proof_forall_rel(step, lhs, rhs, sub);
      }
      case EXISTS:{
        return do_proof_exists(step, lhs, rhs, sub);
      }
      case EXISTS_REL: {
        return do_proof_exists_rel(step, lhs, rhs, sub);
      }
      case ALLACT: {
        return do_proof_allact(step, lhs, rhs, sub);
      }
      case EXISTACT: {
        return do_proof_existact(step, lhs, rhs, sub);
      }
      case IMPLY:{
        return do_proof_imply(step, lhs, rhs, sub);
      }
      case CONSTRAINT:{
        return do_proof_constraint(lhs, rhs);
      }
      case BOOL:{
        return do_proof_bool(rhs);
      }
      case ATOMIC:{
        return do_proof_atomic(rhs, sub);
      }
      case ATOMIC_NOT:{
        return do_proof_atomic_not(rhs, sub);
      }
      case ATOMIC_LT:{
        return do_proof_atomic_lt(rhs, sub);
      }
      case ATOMIC_GT:{
        return do_proof_atomic_gt(rhs, sub);
      }
      case ATOMIC_LE:{
        return do_proof_atomic_le(rhs, sub);
      }
      case ATOMIC_GE:{
        return do_proof_atomic_ge(rhs, sub);
      }
      case SUBLIST:{
        return do_proof_sublist(step, lhs, rhs, sub);
      }
      case RESET:{
        return do_proof_reset(step, lhs, rhs, sub);
      }
      case ASSIGN:{
        return do_proof_assign(step, lhs, rhs, sub);
      }
      case REPLACE:{
        return do_proof_replace(step, lhs, rhs, sub);
      }
      case ABLEWAITINF:{
        return do_proof_ablewaitinf(lhs, sub);
      }
      case UNABLEWAITINF:{
        return do_proof_unablewaitinf(lhs, sub);
      }
    }
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
   * no valid value for the placeholder exists (thus proof is Invalid).
   * The sequent is valid for the clock valuations in the intersection of lhs
   * and the return value. */
  __attribute__((flatten))
  DBMList * do_proof_place(int step, DBM * const lhs, DBMList * const place,
                                   const ExprNode * const rhs, SubstList * const sub)
  {
    /* do_proof_place() written by Peter Fontana, needed for support
     * of EXISTS Quantifiers. */

    if (cpplogEnabled(cpplogging::debug)) {
      lhs->cf();
      place->cf();
      print_sequent_place(std::cerr, step, false, lhs, place, rhs, sub, rhs->getOpType());
    }

    step++;

    switch(rhs->getOpType()){
      case PREDICATE:{
        return do_proof_place_predicate(step, lhs, place, rhs, sub);
      }
      case AND:{
        return do_proof_place_and(step, lhs, place, rhs, sub);
      }
      case OR:{
        return do_proof_place_or(step, lhs, place, rhs, sub);
      }
      case OR_SIMPLE:{
        return do_proof_place_or_simple(step, lhs, place, rhs, sub);
      }
      case FORALL:{
        return do_proof_place_forall(step, lhs, rhs, sub);
      }
      case FORALL_REL: {
        return do_proof_place_forall_rel(step, lhs, place, rhs, sub);
      }
      case EXISTS:{
        return do_proof_place_exists(step, lhs, place, rhs, sub);
      }
      case EXISTS_REL: {
        return do_proof_place_exists_rel(step, lhs, place, rhs, sub);
      }
      case ALLACT: {
        return do_proof_place_allact(step, lhs, place, rhs, sub);
      }
      case EXISTACT: {
        return do_proof_place_existact(step, lhs, place, rhs, sub);
      }
      case IMPLY:{
        return do_proof_place_imply(step, lhs, place, rhs, sub);
      }
      case CONSTRAINT:{
        return do_proof_place_constraint(lhs, place, rhs);
      }
      case BOOL:{
        return do_proof_place_bool(place, rhs);
      }
      case ATOMIC:{
        return do_proof_place_atomic(place, rhs, sub);
      }
      case ATOMIC_NOT:{
        return do_proof_place_atomic_not(place, rhs, sub);
      }
      case ATOMIC_LT:{
        return do_proof_place_atomic_lt(place, rhs, sub);
      }
      case ATOMIC_GT:{
        return do_proof_place_atomic_gt(place, rhs, sub);
      }
      case ATOMIC_LE:{
        return do_proof_place_atomic_le(place, rhs, sub);
      }
      case ATOMIC_GE:{
        return do_proof_place_atomic_ge(place, rhs, sub);
      }
      case SUBLIST:{
        return do_proof_place_sublist(step, lhs, place, rhs, sub);
      }
      case RESET:{
        return do_proof_place_reset(step, lhs, place, rhs, sub);
      }
      case ASSIGN:{
        return do_proof_place_assign(step, lhs, place, rhs, sub);
      }
      case REPLACE:{
        return do_proof_place_replace(step, lhs, place, rhs, sub);
      }
      case ABLEWAITINF:{
        return do_proof_place_ablewaitinf(lhs, place, sub);
      }
      case UNABLEWAITINF:{
        return do_proof_place_unablewaitinf(lhs, place, sub);
      }
    }
  }

  void printTabledSequents(std::ostream& os) const
  {
    cache.printTabledSequents(os);
  }

protected:
  bool do_proof_predicate(const int step, DBM * const lhs, const ExprNode * const rhs, SubstList * const sub);
  bool do_proof_and(const int step, DBM * const lhs, const ExprNode * const rhs, SubstList * const sub);
  bool do_proof_or(const int step, DBM * const lhs, const ExprNode * const rhs, SubstList * const sub);
  bool do_proof_or_simple(const int step, DBM * const lhs, const ExprNode * const rhs, SubstList * const sub);
  bool do_proof_forall(const int step, DBM * const lhs, const ExprNode * const rhs, SubstList * const sub);
  bool do_proof_forall_rel(const int step, DBM * const lhs, const ExprNode * const rhs, SubstList * const sub);
  bool do_proof_exists(const int step, DBM * const lhs, const ExprNode * const rhs, SubstList * const sub);
  bool do_proof_exists_rel(const int step, DBM * const lhs, const ExprNode * const rhs, SubstList * const sub);
  bool do_proof_allact(const int step, DBM * const lhs, const ExprNode * const rhs, SubstList * const sub);
  bool do_proof_existact(const int step, DBM * const lhs, const ExprNode * const rhs, SubstList * const sub);
  bool do_proof_imply(const int step, DBM * const lhs, const ExprNode * const rhs, SubstList * const sub);
  bool do_proof_constraint(DBM * const lhs, const ExprNode * const rhs);
  bool do_proof_bool(const ExprNode * const rhs);
  bool do_proof_atomic(const ExprNode * const rhs, const SubstList * const sub);
  bool do_proof_atomic_not(const ExprNode * const rhs, const SubstList * const sub);
  bool do_proof_atomic_lt(const ExprNode * const rhs, const SubstList * const sub);
  bool do_proof_atomic_gt(const ExprNode * const rhs, const SubstList * const sub);
  bool do_proof_atomic_le(const ExprNode * const rhs, const SubstList * const sub);
  bool do_proof_atomic_ge(const ExprNode * const rhs, const SubstList * const sub);
  bool do_proof_sublist(const int step, DBM * const lhs, const ExprNode * const rhs, const SubstList * const sub);
  bool do_proof_reset(const int step, DBM * const lhs, const ExprNode * const rhs, SubstList * const sub);
  bool do_proof_assign(const int step, DBM * const lhs, const ExprNode * const rhs, SubstList * const sub);
  bool do_proof_replace(const int step, DBM * const lhs, const ExprNode * const rhs, SubstList * const sub);
  bool do_proof_ablewaitinf(DBM * const lhs, SubstList * const sub);
  bool do_proof_unablewaitinf(DBM * const lhs, SubstList * const sub);

  DBMList* do_proof_place_predicate(int step, DBM* const lhs, DBMList* const place,
                                            const ExprNode* const rhs, SubstList* const sub);
  DBMList* do_proof_place_and(int step, DBM* const lhs, DBMList* const place,
                                            const ExprNode* const rhs, SubstList* const sub);
  DBMList* do_proof_place_or(int step, DBM* const lhs, DBMList* const place,
                                            const ExprNode* const rhs, SubstList* const sub);
  DBMList* do_proof_place_or_simple(int step, DBM* const lhs, DBMList* const place,
                                            const ExprNode* const rhs, SubstList* const sub);
  DBMList* do_proof_place_forall(int step, DBM* const lhs,
                                            const ExprNode* const rhs, SubstList* const sub);
  DBMList* do_proof_place_forall_rel(int step, DBM* const lhs, DBMList* const place,
                                            const ExprNode* const rhs, SubstList* const sub);
  DBMList* do_proof_place_exists(int step, DBM* const lhs, DBMList* const place,
                                            const ExprNode* const rhs, SubstList* const sub);
  DBMList* do_proof_place_exists_rel(int step, DBM* const lhs, DBMList* const place,
                                            const ExprNode* const rhs, SubstList* const sub);
  DBMList* do_proof_place_allact(int step, DBM* const lhs, DBMList* const place,
                                            const ExprNode* const rhs, SubstList* const sub);
  DBMList* do_proof_place_existact(int step, DBM* const lhs, DBMList* const place,
                                            const ExprNode* const rhs, SubstList* const sub);
  DBMList* do_proof_place_imply(int step, DBM* const lhs, DBMList* const place,
                                            const ExprNode* const rhs, SubstList* const sub);
  DBMList* do_proof_place_constraint(DBM* const lhs, DBMList* const place,
                                            const ExprNode* const rhs);
  DBMList* do_proof_place_bool(DBMList* const place, const ExprNode* const rhs);
  DBMList* do_proof_place_atomic(DBMList* const place,
                                            const ExprNode* const rhs, SubstList* const sub);
  DBMList* do_proof_place_atomic_not(DBMList* const place,
                                            const ExprNode* const rhs, SubstList* const sub);
  DBMList* do_proof_place_atomic_lt(DBMList* const place,
                                            const ExprNode* const rhs, SubstList* const sub);
  DBMList* do_proof_place_atomic_gt(DBMList* const place,
                                            const ExprNode* const rhs, SubstList* const sub);
  DBMList* do_proof_place_atomic_le(DBMList* const place,
                                            const ExprNode* const rhs, SubstList* const sub);
  DBMList* do_proof_place_atomic_ge(DBMList* const place,
                                            const ExprNode* const rhs, SubstList* const sub);
  DBMList* do_proof_place_sublist(int step, DBM* const lhs, DBMList* const place,
                                            const ExprNode* const rhs, SubstList* const sub);
  DBMList* do_proof_place_reset(int step, DBM* const lhs, DBMList* const place,
                                            const ExprNode* const rhs, SubstList* const sub);
  DBMList* do_proof_place_assign(int step, DBM* const lhs, DBMList* const place,
                                            const ExprNode* const rhs, SubstList* const sub);
  DBMList* do_proof_place_replace(int step, DBM* const lhs, DBMList* const place,
                                            const ExprNode* const rhs, SubstList* const sub);
  DBMList* do_proof_place_ablewaitinf(DBM* const lhs, DBMList* const place, SubstList* const sub);
  DBMList* do_proof_place_unablewaitinf(DBM* const lhs, DBMList* const place, SubstList* const sub);

  /** Method to compute the predecessor check of relativized exists operators.
   * This method is inlined for performance reasons.
   * @param lhs (*) the left-hand clock set
   * @param lhsSucc (*) the sucessor of the left-hand clock constraint, after
   * applying invariants.
   * @param origPlace (*) a reference to the DBMList placeholder or NULL if
   * there is no placeholder.
   * @param phi1Place (*) the set of clock valuations that satisfy phi1, the
   * left hand formula (the relativized formula).
   * @param phi2Place (*) the set of clock valuations that satisfy phi2, the
   * right hand formula.
   * @param phi2PredPlace (*) the time predecessor of phi2Place; this predecessor
   * may by <= or <, depending on the proof rule that calls this method.
   * @return the output placeholder, which is also retPlaceDBM. */
  inline DBMList * predCheckRule(const DBM * const lhs, const DBM * const lhsSucc,
                                 const DBMList * const origPlace, const DBMList * const phi1Place,
                                 const DBMList * const phi2Place, const DBMList * const phi2PredPlace ) {

    retPlaceDBM->makeEmpty();
    /* Iterate through each DBM of phi2Place and union the results. */
    std::vector<DBM *> * phi2PlaceList = phi2Place->getDBMList();
    DBMList compPhi1(*phi1Place);
    !compPhi1;
    compPhi1.cf();
    bool previouslyUpdated = false;
    for(unsigned int i = 0; i < phi2PlaceList->size(); i++) {
      DBM * currPhi2 = (*phi2PlaceList)[i];
      DBM predPhi2(*currPhi2);
      predPhi2.pre();
      predPhi2.cf();

      DBMList currDBMList(compPhi1);
      currDBMList & predPhi2;
      currDBMList & *lhsSucc;  // Intersect with the successor of the lhs


      DBMList compPhi2(*currPhi2);
      !compPhi2;
      compPhi2.cf();

      currDBMList & compPhi2;
      currDBMList.cf();
      currDBMList.pre();
      currDBMList & *lhsSucc;
      currDBMList.cf();
      // currDBMList currently is the set of bad times; LHS must have
      // no such times in this.
      if(currDBMList.emptiness()) { // no bad times, so no shrinkage
        *retPlaceDBM = *phi1Place;
        break;
      }
      /* If this is nonempty, then we have something to deal with */
      // Also, the placeholder cannot be completely contained in this
      if(origPlace == NULL) {
        currDBMList & *lhs;
        currDBMList.cf();
        if(!(currDBMList.emptiness())) {
          if(previouslyUpdated == false) {
            previouslyUpdated = true;
            *retPlaceDBM = currDBMList;
          }
          else{
            retPlaceDBM->addDBMList(currDBMList);
          }
        }
        else {
          if(previouslyUpdated == false) {
            previouslyUpdated = true;
            retPlaceDBM->makeEmpty();
          }
        }
      }
      else { /* This is the section if we have a placeholder */
        currDBMList & *origPlace;
        currDBMList.cf();
        if(currDBMList.emptiness()) {
          if(previouslyUpdated == false) {
            previouslyUpdated = true;
            retPlaceDBM->makeEmpty();
          }
        }
        else if (currDBMList >= *lhs) {
          if(previouslyUpdated == false) {
            previouslyUpdated = true;
            *retPlaceDBM = currDBMList;
          }
          else{
            retPlaceDBM->addDBMList(currDBMList);
          }
        }
        else { // this is the same as the emptiness case
          if(previouslyUpdated == false) {
            previouslyUpdated = true;
            retPlaceDBM->makeEmpty();
          }
        }
      }


    }

    /* We also need to make another placeholder check: that the phi1Place,
     * which is now retPlaceDBM, is a placeholder that can be formed
     * by taking the predecessor
     * and intersecting it with succ(\Gamma). We need phi1Place to be
     * the entire predecessor, and not just the upper part of it. */
    if(!(*retPlaceDBM >= *lhs)) {
      // simple empty case
      retPlaceDBM->makeEmpty();
    }
    else {
      // here, we just need to check for gaps in the DBM and eliminate them.
      // does this case come up due to how pred check works?
    }


    return retPlaceDBM;
  }

  /** Performs the succCheck rule of FORALL (and FORALL_REL) rules, including
   * the computing of the premise, the consequent, and the tightening of the
   * placeholder currPlace.
   * @param lhs (*) the reference to the left hand sequent
   * @param currPlace (*) the reference to the current placeholder.
   * @return the tightened placeholder that satisfies the succCheck, or an
   * empty placeholder if no such placeholder is possible. */
  inline DBMList * succCheckRule(const DBM * const lhs, const DBMList * const currPlace) {

    DBM succLHS(*lhs);
    succLHS.suc();
    // intersect with new placeholder
    DBMList conseq(*retPlaceDBM);
    conseq & succLHS;

    /* Computing Premise of Right part of proof */
    /* Compute Succ(Premise and First Placeholder) */
    // succLHS is the successor of the left-hand side, so do not repeat the work
    DBMList succPrem(*lhs);
    succPrem & *retPlaceDBM;
    succPrem.cf();
    succPrem.suc();

    // First start by setting the place holder to the value of the new placeholder
    /* Per our algorithm, initialize place as retPlaceDBM. */
    // Do we need to intersect succLHS with retPlaceDBM somewhere?
    conseq.cf(); // The consequent
    succLHS.cf(); // The succprem
    succPrem.cf();

    if(conseq >= succPrem) {
      *retPlaceDBM = *currPlace;
      return retPlaceDBM;
    }

    /* If we are here, then we have one of two cases:
     * 1. The succCheck fails (since it is not possible)
     * 2. THe placeholder needs to be tightened so it can pass.
     * Invariants make this tricky */
    // Find the bad zones;
    DBMList badVals(*currPlace);
    !badVals;
    badVals.cf();
    badVals & succPrem;
    badVals & succLHS;
    badVals.cf();
    badVals.pre();
    badVals.cf();
    // At this point, we have the bad valuations. Now intersect their
    // complement
    !badVals;
    badVals.cf();
    // Good values must be after succLHS
    badVals & succLHS;
    badVals.cf();
    *retPlaceDBM & badVals;
    retPlaceDBM->cf();
    if(retPlaceDBM->emptiness()) {
      return retPlaceDBM;
    }
    // Do one more containmnet check. If this does not work,
    // then the placeholder is empty
    succLHS = *lhs;
    succLHS.suc();

    // leave conseq unchanged, since that placeholder did not shrink
    succPrem = *lhs;
    succPrem & *retPlaceDBM;
    succPrem.cf();
    succPrem.suc();

    succLHS.cf();
    succPrem.cf();
    // use previously solved place, not new one for right hand side
    if(conseq >= succPrem) {
      return retPlaceDBM;
    }
    retPlaceDBM->makeEmpty();
    return retPlaceDBM;
  }

};



/* IMPLEMENTATION PROOF WITHOUT PLACEHOLDERS */
inline bool prover::do_proof_predicate(const int step, DBM* const lhs, const ExprNode* const rhs, SubstList* const sub)
{
  bool retVal = false;

  ExprNode *e = input_pes.lookup_equation(rhs->getPredicate());
  if (e == NULL){
    cpplog(cpplogging::error) << "open predicate variable found: "<< rhs->getPredicate() << std::endl;
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
    { // Restricted scope for looking up false sequents
      Sequent tf(rhs, sub);
      Sequent *hf = cache.Xlist_false.look_for_sequent(tf.sub(), pInd);
      if(hf != NULL && hf->tabled_false_sequent(lhs)) {
        retVal = false;
        cpplog(cpplogging::debug) << "---(Invalid) Located a Known False Sequent ----" <<  std::endl <<  std::endl;

        /* Add backpointer to parent sequent (shallow copy) */
        hf->addParent(parentRef);
        return retVal; // break out of switch
      }
    }

    /* Now look in known True Sequent table */
    { // Restricted scope for looking up true sequents
      Sequent tf(rhs, sub); //JK Can be optimised out by reusing tf?
      Sequent *hf = cache.Xlist_true.look_for_sequent(tf.sub(), pInd);
      if(hf != NULL && hf->tabled_sequent(lhs)) {
        retVal = true;
        cpplog(cpplogging::debug) << "---(Valid) Located a Known True Sequent ----" <<  std::endl <<  std::endl;

        /* Add backpointer to parent sequent (shallow copy) */
        hf->addParent(parentRef);
        return retVal; // break out of switch
      }
    }
  }

  /* Now deal with greatest fixpoint circularity and least
   * fixpoint circularity */
  Sequent *h = nullptr;
  { // Restricted scope for detecting circularities
    Sequent *t = new Sequent(rhs, sub);
    if(currParityGfp) { // Thus a Greatest Fixpoint
      h = cache.Xlist_pGFP.locate_sequent(t, pInd);
      if((!newSequent) && h->tabled_sequent(lhs)) {
        // Found gfp Circularity - thus valid
        retVal = true;

        cpplog(cpplogging::debug) << "---(Valid) Located a True Sequent or gfp Circularity ----" <<  std::endl <<  std::endl;

        /* Add backpointer to parent sequent (shallow copy) */
        h->addParent(parentRef);

        // Add sequent to known true cache
        if(useCaching) {
          Sequent *t7 = new Sequent(rhs, sub);
          Sequent *h7 = cache.Xlist_true.locate_sequent(t7, pInd);
          h7->update_sequent(lhs);
        }
        return retVal;
      }

      h->push_sequent(new DBM(*lhs));
    }
    else { // Thus, a least fixpoint
      // Now look for a Circularity
      h = cache.Xlist_pLFP.locate_sequent(t, pInd);
      if((!newSequent) && h->tabled_sequent_lfp(lhs)) {
        // Found lfp circularituy - thus invalid
        retVal = false;

        cpplog(cpplogging::debug) << "---(Invalid) Located a lfp Circularity ----" <<  std::endl <<  std::endl;

        /* Add backpointer to parent sequent (shallow copy) */
        h->addParent(parentRef);

        // Now Put Sequent in False Cache
        if(useCaching) {
          Sequent *t7 = new Sequent(rhs, sub);
          Sequent *h7 = cache.Xlist_false.locate_sequent(t7, pInd);
          h7->update_false_sequent(lhs);
        }
        return retVal;
      }

      h->push_sequent(new DBM(*lhs));
    }
  } // End scope for circularity
  assert(h != nullptr);

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
  if(useCaching) {
    if(retVal)
    {
      /* First look in opposite parity Caches */
      bool madeEmpty = false;
      Sequent *t2 = new Sequent(rhs, sub);
      /* If found, Purge Sequent from its cache */
      Sequent *t2s = cache.Xlist_false.look_for_and_purge_rhs_sequent(lhs, t2, pInd, false, &madeEmpty);

      /* Now purge backpointers */
      if(t2s != NULL) {
        cache.look_for_and_purge_rhs_backStack(t2s->parents(), t2s->parents_with_placeholders());
      }

      // Now update in proper Cache
      Sequent *t5 = new Sequent(rhs, sub);
      Sequent *h5 = cache.Xlist_true.locate_sequent(t5, pInd);
      h5->update_sequent(lhs);

      // Now make deletions for Memory Cleanup
      if(t2 != t2s) {
        delete t2;
      }
      if(madeEmpty) {
        delete t2s;
      }
    }
    else { // !retVal
      /* True cache (not gfp caches) */
      Sequent *t22 = new Sequent(rhs, sub);
      bool madeEmpty = false;
      /* If found, Purge Sequent from its cache */
      Sequent *t22s = cache.Xlist_true.look_for_and_purge_rhs_sequent(lhs, t22, pInd, true, &madeEmpty);

      /* Now purge backpointers.
       * Ignore circularity booleans because they do not form backpointers */
      if(t22s != NULL) {
        cache.look_for_and_purge_rhs_backStack(t22s->parents(), t22s->parents_with_placeholders());
      }

      // Now update in proper Cache
      Sequent *t5 = new Sequent(rhs, sub);
      Sequent *h5 = cache.Xlist_false.locate_sequent(t5, pInd);
      h5->update_false_sequent(lhs);

      // Now make deletions for Memory Cleanup
      if( t22 != t22s) {
        delete t22;
      }
      if(madeEmpty) {
        delete t22s;
      }
    }
  }

  /* The line: h->addParent(parentRef);
   * is not needed since the backpointer stored before proof. */
  h->pop_sequent();
  return retVal;
}

inline bool prover::do_proof_and(const int step, DBM * const lhs, const ExprNode * const rhs, SubstList * const sub)
{
  /* Because lhs is only changed after it is copied, it can
   * be passed to both branches. */
  bool retVal = do_proof(step, lhs, rhs->getLeft(), sub);
  if(retVal) {
    retVal = do_proof(step, lhs, rhs->getRight(), sub);
  }
  return retVal;
}

/* For an expression l || r we consider three cases, using a placeholder:
 * - the proof for l returns an empty placeholder
 * - the proof for l covers the entire DBM lhs
 * - the proof for l covers a strict, non-empty subset of lhs
 */
inline bool prover::do_proof_or(const int step, DBM * const lhs, const ExprNode * const rhs, SubstList * const sub)
{
  bool retVal = false;

  /* Use two placeholders to provide split here */
  DBMList place1(*INFTYDBM);
  retPlaceDBM = do_proof_place(step, lhs, &place1, rhs->getLeft(), sub);
  retPlaceDBM->cf();

  // Reset place parent to NULL
  parentPlaceRef = nullptr;
  if(retPlaceDBM->emptiness()) {
    retVal = do_proof(step, lhs, rhs->getRight(), sub);
  }
  else if(*retPlaceDBM >= *lhs) {
    retVal = true;
  }
  else {
    /* Here we get the corner case where we have to use the
     * OR Split rule, so we try to establish whether part of lhs is covered by
     * l, and the other part is covered by rhs. */
    place1 = *retPlaceDBM; // place1 contains the states covered by l.

    DBMList place2(*INFTYDBM);
    retPlaceDBM = do_proof_place(step, lhs, &place2, rhs->getRight(), sub);
    retPlaceDBM->cf();

    // Reset place parent to NULL
    parentPlaceRef = nullptr;
    if(retPlaceDBM->emptiness()) {
      retVal = false;
    }
    else if(*retPlaceDBM >= *lhs) {
      retVal = true;
    }
    else {
      retPlaceDBM->addDBMList(place1);
      retVal = (*retPlaceDBM) >= *lhs; // if the union of both placeholders covers the set of states, we are still happy
    }
  }
  return retVal;
}

inline bool prover::do_proof_or_simple(const int step, DBM * const lhs, const ExprNode * const rhs, SubstList * const sub)
{
  /* Simplified OR does not need to split on placeholders */
  bool retVal = do_proof(step, lhs, rhs->getLeft(), sub);
  // Reset place parent to NULL
  if(!retVal) {
    DBM lhsb(*lhs); // why do we require this copy?
    retVal  = do_proof(step, &lhsb, rhs->getRight(), sub);
  }
  return retVal;
}

inline bool prover::do_proof_forall(const int step, DBM * const lhs, const ExprNode * const rhs, SubstList * const sub)
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

inline bool prover::do_proof_forall_rel(const int step, DBM * const lhs, const ExprNode * const rhs, SubstList * const sub)
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
    if(cpplogEnabled(cpplogging::debug)) {
      print_sequentCheck(std::cerr, step - 1, retVal, lhs, retPlaceDBM, sub, rhs->getOpType());
      cpplog(cpplogging::debug) <<"----() Empty Relativization Placeholder: phi1 is never true -----" <<  std::endl <<  std::endl;
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

      if (cpplogEnabled(cpplogging::debug)) {
        print_sequentCheck(cpplogGet(cpplogging::debug), step - 1, retVal, lhs, retPlaceDBM, sub, rhs->getOpType());
        cpplog(cpplogging::debug) <<"----(Valid) Placeholder indicates no time elapse is needed (Check Only)-----" <<  std::endl
        << "----With Placeholder := {";
        retPlaceDBM->print_constraint(cpplogGet(cpplogging::debug));
        cpplog(cpplogging::debug) << "} ----"<<  std::endl <<  std::endl;

      }

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

      if (cpplogEnabled(cpplogging::debug)) {
        cpplog(cpplogging::debug) <<"----() Relativization \\phi_1 placeholder obtained as {";
        phi1Place.print_constraint(cpplogGet(cpplogging::debug));
        cpplog(cpplogging::debug) << "} ----"<<  std::endl <<  std::endl;

      }

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

      if (cpplogEnabled(cpplogging::debug)) {
        cpplog(cpplogging::debug) <<"----() Formula \\phi_2 placeholder obtained as {";
        phi2Place.print_constraint(cpplogGet(cpplogging::debug));
        cpplog(cpplogging::debug) << "} ----"<<  std::endl <<  std::endl;

      }

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

        if (cpplogEnabled(cpplogging::debug)) {
          print_sequentCheck(cpplogGet(cpplogging::debug), step - 1, retVal, &phb, fPlace, sub, rhs->getOpType());
          cpplog(cpplogging::debug) <<"----() FORALL (of FORALL_REL) Placeholder Check obtained  FA Placeholder := {";
          forallPlace.print_constraint(cpplogGet(cpplogging::debug));
          cpplog(cpplogging::debug) <<"} ----" <<  std::endl <<  std::endl;
        }

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
        if(cpplogEnabled(cpplogging::debug)) {
          cpplog(cpplogging::debug) <<"----() FORALL Rel Exists predCheck placeholder obtained as := {";
          retPlaceDBM->print_constraint(cpplogGet(cpplogging::debug));
          cpplog(cpplogging::debug) << "} ----"<<  std::endl <<  std::endl;
        }
        if(!retPlaceDBM->emptiness()) {
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

          if(cpplogEnabled(cpplogging::debug)) {
            print_sequentCheck(cpplogGet(cpplogging::debug), step - 1, retVal, lhs, retPlaceDBM, sub, rhs->getOpType());

            cpplog(cpplogging::debug) <<"----() FORALL Rel Exists placeholder after time elapse check is := {";
            retPlaceDBM->print_constraint(cpplogGet(cpplogging::debug));
            cpplog(cpplogging::debug) << "} ----"<<  std::endl <<  std::endl;
          }
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
        if(cpplogEnabled(cpplogging::debug)) {
          print_sequentCheck(cpplogGet(cpplogging::debug), step - 1, retVal, lhs, retPlaceDBM, sub, rhs->getOpType());
          cpplog(cpplogging::debug) <<"----() Final FORALL REL Placeholder is := {";
          retPlaceDBM->print_constraint(cpplogGet(cpplogging::debug));
          cpplog(cpplogging::debug) << "} ----"<<  std::endl <<  std::endl;
        }
        delete phi1PredPlace;
      }
      delete fPlace;

    }
    delete tPlace;
  }
  return retVal;
}

inline bool prover::do_proof_exists(const int step, DBM * const lhs, const ExprNode * const rhs, SubstList * const sub)
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
    if(cpplogEnabled(cpplogging::debug)) {
      print_sequentCheck(cpplogGet(cpplogging::debug), step - 1, retVal, lhs, retPlaceDBM, sub, rhs->getOpType());
      cpplog(cpplogging::debug) <<"----(Invalid) Empty Placeholder: No Need for Placeholder Check-----" <<  std::endl <<  std::endl;
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

  if (cpplogEnabled(cpplogging::debug)) {
    print_sequentCheck(cpplogGet(cpplogging::debug), step - 1, retVal, lhs, retPlaceDBM, sub, rhs->getOpType());
    if(retVal) {
      cpplog(cpplogging::debug) <<"----(Valid) Placeholder Check Passed (Check Only)-----" <<  std::endl
      << "----With Placeholder := {";
      retPlaceDBM->print_constraint(cpplogGet(cpplogging::debug));
      cpplog(cpplogging::debug) << "} ----"<<  std::endl <<  std::endl;

    }
    else {
      cpplog(cpplogging::debug) <<"----(Invalid) Placeholder Check Failed-----" <<  std::endl <<  std::endl;

    }
  }

  return retVal;
}

inline bool prover::do_proof_exists_rel(const int step, DBM * const lhs, const ExprNode * const rhs, SubstList * const sub)
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
    if (cpplogEnabled(cpplogging::debug)) {
      print_sequentCheck(cpplogGet(cpplogging::debug), step - 1, retVal, lhs, retPlaceDBM, sub, rhs->getOpType());
      cpplog(cpplogging::debug) <<"----(Invalid) Empty First Placeholder: No Need for additional Placeholder Checks-----" <<  std::endl <<  std::endl;
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

  if(cpplogEnabled(cpplogging::debug)) {
    cpplog(cpplogging::debug) <<"----() Placeholder of times where \\phi_1 is true----- {";
    phi1Place.print_constraint(cpplogGet(cpplogging::debug));
    cpplog(cpplogging::debug) << "} ----"<<  std::endl <<  std::endl;
  }

  // This provides a preliminary check.
  *retPlaceDBM & *phi2PredPlace;
  retPlaceDBM->cf();
  if(retPlaceDBM->emptiness()) {
    retVal = false;

    if(cpplogEnabled(cpplogging::debug)) {
      print_sequentCheck(cpplogGet(cpplogging::debug), step - 1, retVal, &phb, retPlaceDBM, sub, rhs->getOpType());
      cpplog(cpplogging::debug) <<"----() Empty Second Placeholder: Relativization Formula \\phi_1 is never true-----" <<  std::endl <<  std::endl;
    }

    /* Now determine if $\phi_2$ is true without a time elapse.
     * If so, make a non-empty placeholder. In this case, the third
     * Check will be true by default and can be skipped.
     * Else, return empty and break */
    *phi2Place & *lhs; // lhs here is before the time elapse
    phi2Place->cf();
    if(phi2Place->emptiness()) {
      retVal = false;
      cpplog(cpplogging::debug) << "----(Invalid) Time Elapsed required for formula to be true; hence, relativized formula cannot always be false." <<  std::endl <<  std::endl;
    }
    else {
      /* While a time elapse is not required, the placeholder
       * must span all of lhs */
      retVal = (*phi2Place) >= (*lhs);

      if(cpplogEnabled(cpplogging::debug)) {
        if(retVal) {
          cpplog(cpplogging::debug) <<"----(Valid) Time Elapse not required and placeholder spans lhs; hence, formula is true-----" <<  std::endl;
        }
        else
        {
          cpplog(cpplogging::debug) <<"----(Invalid) While Time Elapse not required, placeholder is not large enough-----" <<  std::endl;
        }
        cpplog(cpplogging::debug) << "----With resulting Placeholder := {";
        phi2Place->print_constraint(cpplogGet(cpplogging::debug));
        cpplog(cpplogging::debug) << "} ----"<<  std::endl <<  std::endl;
      }
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

    if(cpplogEnabled(cpplogging::debug)) {
      cpplog(cpplogging::debug) <<"----(Invalid) Relativization placeholder failed-----" <<  std::endl
      << "----With resulting Placeholder := {";
      retPlaceDBM->print_constraint(cpplogGet(cpplogging::debug));
      cpplog(cpplogging::debug) << "} ----"<<  std::endl <<  std::endl;
    }

    delete phi2Place;
    delete phi2PredPlace;
    delete tPlace;
    return retVal;
  }
  // if it is nonempty, it passes the second check and we continue

  if(cpplogEnabled(cpplogging::debug)) {
    print_sequent_place(std::cerr, step - 1,  retVal, &phb, phi2PredPlace, rhs->getLeft(), sub, rhs->getOpType());
    cpplog(cpplogging::debug) <<"----(Valid) Relativization Placeholder Check Passed (Check Only)-----" <<  std::endl
    << "----With resulting Placeholder := {";
    retPlaceDBM->print_constraint(cpplogGet(cpplogging::debug));
    cpplog(cpplogging::debug) << "} ----"<<  std::endl <<  std::endl;
  }

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


  if (cpplogEnabled(cpplogging::debug)) {
    print_sequentCheck(cpplogGet(cpplogging::debug), step - 1, retVal, lhs, retPlaceDBM, sub, rhs->getOpType());
    if(retVal) {
      cpplog(cpplogging::debug) <<"----(Valid) Last Placeholder Check Passed (Check Only)-----" <<  std::endl
      << "----With Placeholder := {";
      retPlaceDBM->print_constraint(cpplogGet(cpplogging::debug));
      cpplog(cpplogging::debug) << "} ----"<<  std::endl <<  std::endl;

    }
    else {
      cpplog(cpplogging::debug) <<"----(Invalid) Last Placeholder Check Failed-----" <<  std::endl <<  std::endl;

    }
  }

  delete phi2Place;
  delete phi2PredPlace;
  delete tPlace;
  return retVal;
}

inline bool prover::do_proof_allact(const int step, DBM * const lhs, const ExprNode * const rhs, SubstList * const sub)
{
  bool retVal = true;
  /* Enumerate through all transitions */
  cpplog(cpplogging::debug) << "\t Proving ALLACT Transitions:----\n" <<  std::endl;

  for(std::vector<Transition *>::const_iterator it = input_pes.transitions().begin();
      it != input_pes.transitions().end(); it++ ) {
    Transition * tempT = *it;
    /* Obtain the entire ExprNode and prove it */
    DBM tempLHS(*lhs);

    bool tempBool = comp_ph(&tempLHS, *(tempT->getLeftExpr()), *sub);
    if(!tempBool) {
      cpplog(cpplogging::debug) << "Transition: " << tempT << " cannot be taken." <<  std::endl;
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
      const std::vector<std::pair<short int, short int> > * av = tempT->getAssignmentVector();
      if(av != NULL) {
        // Iterate over the vector and print it
        for(std::vector<std::pair<short int, short int> >::const_iterator it=av->begin(); it != av->end(); it++) {
          invCons.preset((*it).first, (*it).second);
          invCons.cf();
        }
      }
      tempLHS & invCons;
      tempLHS.cf();
      if(tempLHS.emptiness()) {

        if (cpplogEnabled(cpplogging::debug)) {
          cpplog(cpplogging::debug) << "Transition: " << tempT;
          cpplog(cpplogging::debug) << " cannot be taken; entering invariant is false." <<  std::endl;
          cpplog(cpplogging::debug) << "\tExtra invariant condition: ";
          invCons.print_constraint(cpplogGet(cpplogging::debug));
          cpplog(cpplogging::debug) <<  std::endl;
        }

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

    if (cpplogEnabled(cpplogging::debug)) {
      cpplog(cpplogging::debug) << "Executing transition (with destination) " << tempT << std::endl;
      cpplog(cpplogging::debug) << "\tExtra invariant condition: ";
      invCons.print_constraint(cpplogGet(cpplogging::debug));
      cpplog(cpplogging::debug) <<  std::endl;
    }

    numLocations++;
    retVal = do_proof(step, &tempLHS, tempT->getRightExpr(), &tempSub);
    if(!retVal) {
      cpplog(cpplogging::debug) << "Trainsition: " << tempT <<  std::endl
                                << "\tinvalidates property and breaks transition executions. " <<  std::endl;

      break;
    }

  }
  cpplog(cpplogging::debug) << "\t --- end of ALLACT." <<  std::endl;
  return retVal;
}

inline bool prover::do_proof_existact(const int step, DBM * const lhs, const ExprNode * const rhs, SubstList * const sub)
{
  bool retVal = false;
  /* Enumerate through all transitions */

  cpplog(cpplogging::debug) << "\t Proving EXISTACT Transitions:----\n" <<  std::endl;

  /* Use placeholders to split rules */
  bool emptyPartialPlace = true;
  DBMList * partialPlace;
  for(std::vector<Transition *>::const_iterator it = input_pes.transitions().begin();
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
      cpplog(cpplogging::debug) << "Transition: " << tempT << " cannot be taken." << std::endl;
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
      const std::vector<std::pair<short int, short int> > * av = tempT->getAssignmentVector();
      if(av != NULL) {
        // Iterate over the vector and print it
        for(std::vector<std::pair<short int, short int> >::const_iterator it=av->begin(); it != av->end(); it++) {
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
          if(cpplogEnabled(cpplogging::debug)) {
            cpplog(cpplogging::debug) << "Transition: " << tempT;
            cpplog(cpplogging::debug) << " cannot be taken; entering invariant is false." <<  std::endl;
            cpplog(cpplogging::debug) << "\tExtra invariant condition: ";
            invCons.print_constraint(cpplogGet(cpplogging::debug));
            cpplog(cpplogging::debug) <<  std::endl;
          }

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
    cpplog(cpplogging::debug) << "Executing transition (with destination) " << tempT << std::endl;
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

  cpplog(cpplogging::debug) << "\t --- end of EXISTACT." <<  std::endl;

  return retVal;
}

inline bool prover::do_proof_imply(const int step, DBM * const lhs, const ExprNode * const rhs, SubstList * const sub)
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
    cpplog(cpplogging::debug) << "---(Valid) Leaf IMPLY Reached, Premise Not Satisfied----" <<  std::endl <<  std::endl;
  }
  return retVal;
}

inline bool prover::do_proof_constraint(DBM * const lhs, const ExprNode * const rhs)
{
  lhs->cf();
  /* The line: (rhs->dbm())->cf(); is not needed */
  bool retVal = (*lhs <= *(rhs->dbm()));
  if(retVal) {
    cpplog(cpplogging::debug) << "---(Valid) Leaf DBM (CONSTRAINT) Reached----" <<  std::endl <<  std::endl;
  }
  else {
    cpplog(cpplogging::debug) << "---(Invalid) Leaf DBM (CONSTRAINT) Reached----" <<  std::endl <<  std::endl;
  }
  return retVal;
}

inline bool prover::do_proof_bool(const ExprNode * const rhs)
{
  bool retVal = (rhs->getBool());
  if (retVal) {
    cpplog(cpplogging::debug) << "---(Valid) Leaf BOOL Reached----" <<  std::endl <<  std::endl;
  }
  else {
    cpplog(cpplogging::debug) << "---(Invalid) Leaf BOOL Reached----" <<  std::endl <<  std::endl;
  }
  return retVal;
}

inline bool prover::do_proof_atomic(const ExprNode * const rhs, const SubstList * const sub)
{
  bool retVal = (sub->at(rhs->getAtomic()) == rhs->getIntVal());
  if (retVal) {
    cpplog(cpplogging::debug) << "---(Valid) Leaf ATOMIC == Reached----" <<  std::endl <<  std::endl;
  }
  else {
    cpplog(cpplogging::debug) << "---(Invalid) Leaf ATOMIC == Reached----" <<  std::endl <<  std::endl;
  }
  return retVal;
}

inline bool prover::do_proof_atomic_not(const ExprNode * const rhs, const SubstList * const sub)
{
  bool retVal = (sub->at(rhs->getAtomic()) != rhs->getIntVal());
  if (retVal) {
    cpplog(cpplogging::debug) << "---(Valid) Leaf ATOMIC != Reached----" <<  std::endl <<  std::endl;
  }
  else {
    cpplog(cpplogging::debug) << "---(Invalid) Leaf ATOMIC != Reached----" <<  std::endl <<  std::endl;
  }
  return retVal;
}

inline bool prover::do_proof_atomic_lt(const ExprNode * const rhs, const SubstList * const sub)
{
  bool retVal = (sub->at(rhs->getAtomic()) < rhs->getIntVal());
  if (retVal) {
    cpplog(cpplogging::debug) << "---(Valid) Leaf ATOMIC < Reached----" <<  std::endl <<  std::endl;
  }
  else {
    cpplog(cpplogging::debug) << "---(Invalid) Leaf ATOMIC < Reached----" <<  std::endl <<  std::endl;
  }
  return retVal;
}

inline bool prover::do_proof_atomic_gt(const ExprNode * const rhs, const SubstList * const sub)
{
  bool retVal = (sub->at(rhs->getAtomic()) > rhs->getIntVal());
  if (retVal) {
    cpplog(cpplogging::debug) << "---(Valid) Leaf ATOMIC > Reached----" <<  std::endl <<  std::endl;
  }
  else {
    cpplog(cpplogging::debug) << "---(Invalid) Leaf ATOMIC > Reached----" <<  std::endl <<  std::endl;
  }
  return retVal;
}

inline bool prover::do_proof_atomic_le(const ExprNode * const rhs, const SubstList * const sub)
{
  bool retVal = (sub->at(rhs->getAtomic()) <= rhs->getIntVal());
  if (retVal) {
    cpplog(cpplogging::debug) << "---(Valid) Leaf ATOMIC < Reached----" <<  std::endl <<  std::endl;
  }
  else{
    cpplog(cpplogging::debug) << "---(Invalid) Leaf ATOMIC < Reached----" <<  std::endl <<  std::endl;
  }
  return retVal;
}

inline bool prover::do_proof_atomic_ge(const ExprNode * const rhs, const SubstList * const sub)
{
  bool retVal = (sub->at(rhs->getAtomic()) >= rhs->getIntVal());
  if (retVal) {
    cpplog(cpplogging::debug) << "---(Valid) Leaf ATOMIC > Reached----" <<  std::endl <<  std::endl;
  }
  else {
    cpplog(cpplogging::debug) << "---(Invalid) Leaf ATOMIC > Reached----" <<  std::endl <<  std::endl;
  }
  return retVal;
}

inline bool prover::do_proof_sublist(const int step, DBM * const lhs, const ExprNode * const rhs, const SubstList * const sub)
{
  SubstList st(rhs->getSublist(), sub );
  return do_proof(step, lhs, rhs->getExpr(), &st);
}

inline bool prover::do_proof_reset(const int step, DBM * const lhs, const ExprNode * const rhs, SubstList * const sub)
{
  //lhs->cf(); // FIXME: lhs is not used further in this proof, also, reset says the *result* is in CF, and does not require the dbm to be in CF.
  DBM ph(*lhs);
  ph.reset(rhs->getClockSet());
  return do_proof(step, &ph, rhs->getExpr(), sub);
}

inline bool prover::do_proof_assign(const int step, DBM * const lhs, const ExprNode * const rhs, SubstList * const sub)
{
  //lhs->cf(); // FIXME: see remark in do_proof_reset
  DBM ph(*lhs);
  /* Here the DBM zone is where the value of
   * clock x is reset to clock y, which is possibly
   * a constant or a value*/
  ph.reset(rhs->getcX(), rhs->getcY());
  return do_proof(step, &ph, rhs->getExpr(), sub);
}

inline bool prover::do_proof_replace(const int step, DBM * const lhs, const ExprNode * const rhs, SubstList * const sub)
{
  sub->operator[](rhs->getcX()) = sub->operator[](rhs->getcY());
  return do_proof(step, lhs, rhs->getExpr(), sub);
}

inline bool prover::do_proof_ablewaitinf(DBM * const lhs, SubstList * const sub)
{
  lhs->cf();
  DBM ph(*lhs);
  ph.suc();
  invs_chk(input_pes.invariants(), &ph, *sub);
  ph.cf();
  /* Time can diverge if and only if there are no upper bound
   * constraints in the successor */
  bool retVal = !ph.hasUpperConstraint();
  if (retVal) {
    cpplog(cpplogging::debug) << "---(Valid) Time able to diverge to INFTY in current location----" <<  std::endl <<  std::endl;
  }
  else {
    cpplog(cpplogging::debug) << "---(Invalid) Time unable to diverge to INFTY in current location---" <<  std::endl <<  std::endl;
  }
  return retVal;
}

// FIXME: eliminate duplication with do_proof_ablewaitinf
inline bool prover::do_proof_unablewaitinf(DBM * const lhs, SubstList * const sub)
{
  lhs->cf();
  DBM ph(*lhs);
  ph.suc();
  invs_chk(input_pes.invariants(), &ph, *sub);
  ph.cf();
  /* Time cannot diverge if and only if there is an upper bound
   * constraint in the successor */
  bool retVal = ph.hasUpperConstraint();
  if (retVal) {
    cpplog(cpplogging::debug) << "---(Valid) Time unable to diverge to INFTY in current location----" <<  std::endl <<  std::endl;
  }
  else {
    cpplog(cpplogging::debug) << "---(Invalid) Time able to diverge to INFTY in current location---" <<  std::endl <<  std::endl;
  }
  return retVal;
}


/* IMPLEMENTATION PROVER WITH PLACEHOLDERS */
inline DBMList* prover::do_proof_place_predicate(int step, DBM* const lhs, DBMList* const place,
                                          const ExprNode* const rhs, SubstList* const sub)
{
  ExprNode *e = input_pes.lookup_equation(rhs->getPredicate());
  if (e == NULL){
    std::cerr << "open predicate variable found: "<< rhs->getPredicate() << std::endl;
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
    SequentPlace *hf = cache.Xlist_false_ph.look_for_sequent(tf->sub(), pInd);
    if(hf != NULL && hf->tabled_false_sequent(lhs)) {
      // Found known false
      retPlaceDBM->makeEmpty();
      cpplog(cpplogging::debug) << "---(Invalid) Located a Known False Sequent ----" <<  std::endl <<  std::endl;

      /* Update backpointers to add possible pointer for parent
       * This is a bit conservative */
      /* Now that we have a proven sequent, add the backpointer
       * from the child to the parent */
      if(parentPlaceRef != NULL) {
        hf->addParent(parentPlaceRef);
      }
      else { // Parent is regular sequent
        hf->addParent(parentRef);
      }
      // Do not delete if tf is the same sequent as hf
      if(tf != hf) {
        delete tf;
      }
      return retPlaceDBM;
    }
    if(tf != hf) {
      delete tf;
    }
  }

  /* Now look in known true cache */
  if(useCaching) {
    SequentPlace *tfb = new SequentPlace(rhs, sub);
    SequentPlace *hfb = cache.Xlist_true_ph.look_for_sequent(tfb->sub(), pInd);
    DBMList tempPlace(*place);
    /* Note: tempPlace is changed by tabled_sequentPlace() */
    if(hfb != NULL && hfb->tabled_sequent(lhs, &tempPlace)) {
      // Found known true
      if(tempPlace.emptiness()) {
        // returning placeholder must be non-empty for the sequent
        // to be valid
        return retPlaceDBM;
      }
      *retPlaceDBM = (tempPlace);
      // Note: we intersect the current found placeholder
      // with the placeholder stored in the sequent.

      cpplog(cpplogging::debug) << "---(Valid) Located a Known True Sequent ----" <<  std::endl <<  std::endl;

      /* Update backpointers to add possible pointer for parent
       * This is a bit conservative */
      /* Now that we have a proven sequent, add the backpointer
       * in the cache from the child to the parent */
      if(parentPlaceRef != NULL) {
        hfb->addParent(parentPlaceRef);
      }
      else { // Parent is regular sequent
        hfb->addParent(parentRef);
      }

      if(tfb != hfb) {
        delete tfb;
      }
      return retPlaceDBM;
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
    h = cache.Xlist_pGFP_ph.locate_sequent(t, pInd);
    if((!newSequent) && h->tabled_sequent_gfp(lhs, place)) {
      // Found gfp Circularity - thus valid
      *retPlaceDBM = (*place);
      cpplog(cpplogging::debug) << "---(Valid) Located True Sequent or gfp Circularity ----" <<  std::endl <<  std::endl;

      /* Now update backpointer for greatest fixpoint circularity */
      if(parentPlaceRef != NULL) {
        h->addParent(parentPlaceRef);
      }
      else { // Parent is regular sequent
        h->addParent(parentRef);
      }

      // Add sequent to known true cache
      if(useCaching) {
        SequentPlace *t7 = new SequentPlace(rhs, sub);
        SequentPlace *h7 = cache.Xlist_true_ph.locate_sequent(t7, pInd);
        h7->update_sequent(lhs, place);
      }
      return retPlaceDBM;
    }


    std::pair <DBM *, DBMList *> p (new DBM(*lhs),new DBMList(*place));
    h->dbm_set().push_back(p);
  }
  else { // Thus, a least fixpoint
    // Now look in lfp circularity cache
    h = cache.Xlist_pLFP_ph.locate_sequent(t, pInd);
    if((!newSequent) && h->tabled_sequent_lfp(lhs, place)) {
      // Found lfp circularity - thus invalid
      retPlaceDBM->makeEmpty();

      cpplog(cpplogging::debug) << "---(Invalid) Located lfp Circularity ----" <<  std::endl <<  std::endl;

      /* Now update backpointer for least fixpoint circularity */
      if(parentPlaceRef != NULL) {
        h->addParent(parentPlaceRef);
      }
      else { // Parent is regular sequent
        h->addParent(parentRef);
      }

      // Now Put Sequent in False Cache
      if(useCaching) {
        SequentPlace *t7 = new SequentPlace(rhs, sub);
        SequentPlace *h7 = cache.Xlist_false_ph.locate_sequent(t7, pInd);
        h7->update_false_sequent(lhs);
      }
      return retPlaceDBM;
    }

    std::pair <DBM *, DBMList *> p (new DBM(*lhs), new DBMList(*place));
    h->push_sequent(p);
  }

  /* Assign parent value after caching since during caching we may have
   * to use the previous parent */
  SequentPlace * tempParentPlace = parentPlaceRef;
  /* Get the current variable */
  parentPlaceRef = h;

  retPlaceDBM = do_proof_place(step, lhs, place, e, sub);

  lhs->cf();


  /* Now update the parent so it points to the previous parent, and not this
   * predicate */
  parentPlaceRef = tempParentPlace;

  h->pop_sequent();
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
    t2s = cache.Xlist_false_ph.look_for_and_purge_rhs_sequent(std::make_pair(lhs, retPlaceDBM), t2c, pInd, false, &madeEmpty);


    /* Now purge backpointers */
    if(t2s != NULL) {
      cache.look_for_and_purge_rhs_backStack(t2s->parents(), t2s->parents_with_placeholders());
      // Delete t2s later to prevent double deletion

    }
    // Now update in proper Cache
    SequentPlace *t5 = new SequentPlace(rhs, sub);
    SequentPlace *h5 = cache.Xlist_true_ph.locate_sequent(t5, pInd);
    h5->update_sequent(lhs, retPlaceDBM);

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
    t2bs = cache.Xlist_true_ph.look_for_and_purge_rhs_sequent(std::make_pair(lhs, retPlaceDBM), t2b2, pInd, true, &madeEmpty);


    /* Now purge backpointers.
     * Ignore circularity booleans because they do not form backpointers */
    if(t2bs != NULL) {
      cache.look_for_and_purge_rhs_backStack(t2bs->parents(), t2bs->parents_with_placeholders());
      // delete t2bs later to prevent double deletion.
    }
    // Now update in proper Cache
    SequentPlace *t5 = new SequentPlace(rhs, sub);
    SequentPlace *h5 = cache.Xlist_false_ph.locate_sequent(t5, pInd);
    h5->update_false_sequent(lhs);

    // Now make deletions for Memory Cleanup
    if(t2b2 != t2bs) {
      delete t2b2;
    }
    // This delete is necessary for memory management but problematic
    if(madeEmpty) {
      delete t2bs;
    }

  }

  return retPlaceDBM;
}

inline DBMList* prover::do_proof_place_and(int step, DBM* const lhs, DBMList* const place,
                                          const ExprNode* const rhs, SubstList* const sub)
{
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
  return retPlaceDBM;
}

inline DBMList* prover::do_proof_place_or(int step, DBM* const lhs, DBMList* const place,
                                          const ExprNode* const rhs, SubstList* const sub)
{
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
    return retPlaceDBM;
  }

  retPlaceDBM->cf();
  DBMList leftPlace(*retPlaceDBM);
  retPlaceDBM = do_proof_place(step, lhs, &placeB, rhs->getRight(), sub);
  retPlaceDBM->cf();

  if(cpplogEnabled(cpplogging::debug)) {
    // Check Debugging Here to make sure it is giving the right output
    print_sequentCheck(cpplogGet(cpplogging::debug), step - 1, false, lhs, place, sub, rhs->getOpType());
    cpplog(cpplogging::debug) << "Left Placeholder of OR (P): ";
    leftPlace.print_constraint(cpplogGet(cpplogging::debug));
    cpplog(cpplogging::debug) << "\nRight Placeholder of OR (P): ";
    retPlaceDBM->print_constraint(cpplogGet(cpplogging::debug));
    cpplog(cpplogging::debug) <<  std::endl;
  }

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
  }
  else { /* Corner Case: make DBM Union*/
    retPlaceDBM->addDBMList(leftPlace);
    retPlaceDBM->cf();
  }

  if(cpplogEnabled(cpplogging::debug)) {
    cpplog(cpplogging::debug) << "Final Placeholder of OR (P): ";
    retPlaceDBM->print_constraint(cpplogGet(cpplogging::debug));
    cpplog(cpplogging::debug) <<  std::endl <<  std::endl;
  }

  return retPlaceDBM;
}

inline DBMList* prover::do_proof_place_or_simple(int step, DBM* const lhs, DBMList* const place,
                                          const ExprNode* const rhs, SubstList* const sub)
{
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
    return retPlaceDBM;
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

  return retPlaceDBM;
}

inline DBMList* prover::do_proof_place_forall(int step, DBM* const lhs,
                                          const ExprNode* const rhs, SubstList* const sub)
{
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

    if (cpplogEnabled(cpplogging::debug)) {
      // Result only used for printing the correct value below.
      bool result = !retPlaceDBM->emptiness();
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
      print_sequentCheck(cpplogGet(cpplogging::debug), step - 1, result, &succLHS, &succRuleConseq, sub, rhs->getOpType());
      if(result) {
        cpplog(cpplogging::debug) <<"----(Valid) Placeholder Check Passed-----" <<  std::endl
        <<"--With Placeholder := {";
        retPlaceDBM->print_constraint(cpplogGet(cpplogging::debug));
        cpplog(cpplogging::debug) <<"} ----" <<  std::endl <<  std::endl;
      }
      else {
        cpplog(cpplogging::debug) <<"----(Invalid) Placeholder Check Failed-----" <<  std::endl <<  std::endl;

      }
    }

  }
  return retPlaceDBM;
}

inline DBMList* prover::do_proof_place_forall_rel(int step, DBM* const lhs, DBMList* const place,
                                          const ExprNode* const rhs, SubstList* const sub)
{
  bool retVal = false;
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
    if (cpplogEnabled(cpplogging::debug)) {
      print_sequentCheck(cpplogGet(cpplogging::debug), step - 1, retVal, &ph, retPlaceDBM, sub, rhs->getOpType());
      cpplog(cpplogging::debug) <<"--------() Empty Relativization Placeholder: phi1 is never true ----------" <<  std::endl <<  std::endl;
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

      if(cpplogEnabled(cpplogging::debug)) {
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
        print_sequentCheck(cpplogGet(cpplogging::debug), step - 1, retVal, &succLHS, &succRuleConseq, sub, rhs->getOpType());
        if(retVal) {
          cpplog(cpplogging::debug) <<"----(Valid) FORALL (FORALL_REL) Placeholder Check Passed-----" <<  std::endl
          <<"--With Placeholder := {";
          retPlaceDBM->print_constraint(cpplogGet(cpplogging::debug));
          cpplog(cpplogging::debug) <<"} ----" <<  std::endl <<  std::endl;
        }
        else {
          cpplog(cpplogging::debug) <<"----(Invalid) FORALL (FORALL_REL) Placeholder Check Failed-----" <<  std::endl <<  std::endl;

        }
      }

    }
  }
  else {
    // First check for the simplest case: no time elapse is needed
    /* Perhaps we can reduce *INFTYDBM to be *place
     * given the proof rules. */
    if((*retPlaceDBM) == (*INFTYDBM)) {

      if (cpplogEnabled(cpplogging::debug)) {
        print_sequentCheck(cpplogGet(cpplogging::debug), step - 1, retVal, lhs, retPlaceDBM, sub, rhs->getOpType());
        cpplog(cpplogging::debug) <<"----(Valid) EXISTS (in FORALL_REL) Placeholder indicates no time elapse is needed (Check Only)-----" <<  std::endl
        << "----With Placeholder := {";
        retPlaceDBM->print_constraint(cpplogGet(cpplogging::debug));
        cpplog(cpplogging::debug) << "} ----"<<  std::endl <<  std::endl;

      }

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

        if (cpplogEnabled(cpplogging::debug)) {
          print_sequentCheck(cpplogGet(cpplogging::debug), step - 1, retVal, &phb, &infPlace, sub, rhs->getOpType());
          if(retVal) {
            cpplog(cpplogging::debug) <<"----(Valid) Placeholder Check Passed-----" <<  std::endl
            <<"--With Placeholder := {";
            retPlaceDBM->print_constraint(cpplogGet(cpplogging::debug));
            cpplog(cpplogging::debug) <<"} ----" <<  std::endl <<  std::endl;
          }
          else {
            cpplog(cpplogging::debug) <<"----(Invalid) Placeholder Check Failed-----" <<  std::endl <<  std::endl;

          }
        }

      }

    }
    else {
      // This is the more complicated case that requires a placeholder
      // for the FORALL
      /* Now check that we can elapse to the placeholder. */
      // Store the set of times that satisfy phi1
      DBMList phi1Place(*retPlaceDBM);

      if(cpplogEnabled(cpplogging::debug)) {
        cpplog(cpplogging::debug) <<"----() Relativization \\phi_1 placeholder obtained as {";
        phi1Place.print_constraint(cpplogGet(cpplogging::debug));
        cpplog(cpplogging::debug) << "} ----"<<  std::endl <<  std::endl;

      }

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

      if(cpplogEnabled(cpplogging::debug)) {
        cpplog(cpplogging::debug) <<"----() Formula \\phi_2 placeholder obtained as {";
        phi2Place.print_constraint(cpplogGet(cpplogging::debug));
        cpplog(cpplogging::debug) << "} ----"<<  std::endl <<  std::endl;

      }

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

        if(cpplogEnabled(cpplogging::debug)) {
          print_sequentCheck(cpplogGet(cpplogging::debug), step - 1, retVal, &phb, fPlace, sub, rhs->getOpType());
          cpplog(cpplogging::debug) <<"----() FORALL (of FORALL_REL) Placeholder Check obtained  FA Placeholder := {";
          forallPlace.print_constraint(cpplogGet(cpplogging::debug));
          cpplog(cpplogging::debug) <<"} ----" <<  std::endl <<  std::endl;
        }

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

        if(cpplogEnabled(cpplogging::debug)) {
          cpplog(cpplogging::debug) <<"----() FORALL Rel Exists placeholder obtained as := {";
          retPlaceDBM->print_constraint(cpplogGet(cpplogging::debug));
          cpplog(cpplogging::debug) << "} ----"<<  std::endl <<  std::endl;
        }

        if(!retPlaceDBM->emptiness()) {
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

          if(cpplogEnabled(cpplogging::debug)) {
            print_sequentCheck(cpplogGet(cpplogging::debug), step - 1, retVal, lhs, retPlaceDBM, sub, rhs->getOpType());

            cpplog(cpplogging::debug) <<"----() FORALL Rel Exists placeholder after time elapse check is := {";
            retPlaceDBM->print_constraint(cpplogGet(cpplogging::debug));
            cpplog(cpplogging::debug) << "} ----"<<  std::endl <<  std::endl;
          }
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

      if(cpplogEnabled(cpplogging::debug)) {
        cpplog(cpplogging::debug) << "Final Placeholder of FORALL_REL (P): ";
        retPlaceDBM->print_constraint(cpplogGet(cpplogging::debug));
        cpplog(cpplogging::debug) <<  std::endl <<  std::endl;
      }

      delete fPlace;
    }
    delete tPlace;
  }
  return retPlaceDBM;
}

inline DBMList* prover::do_proof_place_exists(int step, DBM* const lhs, DBMList* const place,
                                          const ExprNode* const rhs, SubstList* const sub)
{
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
    if(cpplogEnabled(cpplogging::debug)) {
      print_sequentCheck(cpplogGet(cpplogging::debug), step - 1, false, &ph, retPlaceDBM, sub, rhs->getOpType());
      cpplog(cpplogging::debug) <<"----(Invalid) Empty First Placeholder: No Need for additional Placeholder Checks-----" <<  std::endl <<  std::endl;
    }
    return retPlaceDBM;
  }
  /* Now check that it works (the new placeholder can be
   * obtained from the old
   * For the placeholder rule, we use this check
   * to give us the value of the old placeholder */
  retPlaceDBM->pre();
  (*place) & (*retPlaceDBM);
  place->cf();
  *retPlaceDBM = (*place);

  if(cpplogEnabled(cpplogging::debug)) {
    bool result = !place->emptiness();
    print_sequent_placeCheck(std::cerr, step - 1, result, lhs, place, retPlaceDBM, sub, rhs->getOpType());
    if(result) {
      cpplog(cpplogging::debug) <<"----(Valid) Placeholder Check Passed-----" <<  std::endl
      <<"--With Placeholder := {";
      retPlaceDBM->print_constraint(cpplogGet(cpplogging::debug));
      cpplog(cpplogging::debug) <<"} ----" <<  std::endl <<  std::endl;
    }
    else {
      cpplog(cpplogging::debug) <<"----(Invalid) Placeholder Check Failed-----" <<  std::endl <<  std::endl;

    }
  }

  return retPlaceDBM;
}

inline DBMList* prover::do_proof_place_exists_rel(int step, DBM* const lhs, DBMList* const place,
                                          const ExprNode* const rhs, SubstList* const sub)
{
  bool retVal = false;
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
    if (cpplogEnabled(cpplogging::debug)) {
      print_sequentCheck(cpplogGet(cpplogging::debug), step - 1, retVal, lhs, retPlaceDBM, sub, rhs->getOpType());
      cpplog(cpplogging::debug) <<"----(Invalid) Empty First Placeholder: No Need for additional Placeholder Checks-----" <<  std::endl <<  std::endl;
    }
    delete tPlace;
    return retPlaceDBM;
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

  if(cpplogEnabled(cpplogging::debug)) {
    cpplog(cpplogging::debug) <<"----() Placeholder of times where \\phi_1 is true----- {";
    phi1Place.print_constraint(cpplogGet(cpplogging::debug));
    cpplog(cpplogging::debug) << "} ----"<<  std::endl <<  std::endl;
  }

  *retPlaceDBM & *phi2PredPlace;
  retPlaceDBM->cf();
  if(retPlaceDBM->emptiness()) {
    retVal = false;

    if(cpplogEnabled(cpplogging::debug)) {
      print_sequentCheck(cpplogGet(cpplogging::debug), step - 1, retVal, &phb, retPlaceDBM, sub, rhs->getOpType());

      cpplog(cpplogging::debug) <<"----() Empty Second Placeholder: Relativization Formula \\phi_1 is never true-----" <<  std::endl <<  std::endl;
    }

    /* Now determine if $\phi_2$ is true without a time elapse.
     * If so, make a non-empty placeholder. In this case, the third
     * Check will be true by default and can be skipped.
     * Else, return empty and break */
    *phi2Place & *lhs; // lhs here is before the time elapse
    phi2Place->cf();
    if(phi2Place->emptiness()) {
      retVal = false;
      cpplog(cpplogging::debug) << "----(Invalid) Time Elapsed required for formula to be true; hence, relativized formula cannot always be false." <<  std::endl <<  std::endl;
    }
    else {
      /* While a time elapse is not required, the placeholder
       * must span all of lhs */
      retVal = (*phi2Place) >= (*lhs);

      if(cpplogEnabled(cpplogging::debug)) {
        if(retVal) {
          cpplog(cpplogging::debug) <<"----(Valid) Time Elapse not required and placeholder spans lhs; hence, formula is true-----" <<  std::endl;
        }
        else {
          cpplog(cpplogging::debug) <<"----(Invalid) While Time Elapse not required, placeholder is not large enough-----" <<  std::endl;
        }
        cpplog(cpplogging::debug) << "----With resulting Placeholder := {";
        phi2Place->print_constraint(cpplogGet(cpplogging::debug));
        cpplog(cpplogging::debug) << "} ----"<<  std::endl <<  std::endl;
      }
    }


    delete phi2Place;
    delete phi2PredPlace;
    delete tPlace;
    return retPlaceDBM;
  }

  DBMList currRetPlaceDBM(*retPlaceDBM);
  /*--- PredCheck code----*/
  retPlaceDBM = predCheckRule(lhs, &ph, NULL, &phi1Place, phi2Place, phi2PredPlace);
  if(retPlaceDBM->emptiness()) {
    retVal = false;

    if(cpplogEnabled(cpplogging::debug)) {
      cpplog(cpplogging::debug) <<"----(Invalid) Relativization placeholder failed-----" <<  std::endl
      << "----With resulting Placeholder := {";
      retPlaceDBM->print_constraint(std::cerr);
      cpplog(cpplogging::debug) << "} ----"<<  std::endl <<  std::endl;
    }

    delete phi2Place;
    delete phi2PredPlace;
    delete tPlace;
    return retPlaceDBM;
  }

  // if it is still nonempty, it passes the second check and we continue

  //}

  if(cpplogEnabled(cpplogging::debug)) {
    print_sequent_place(std::cerr, step - 1,  retVal, &phb, phi2PredPlace, rhs->getLeft(), sub, rhs->getOpType());
    cpplog(cpplogging::debug) <<"----(Valid) Relativization Placeholder Check Passed (Check Only)-----" <<  std::endl
    << "----With resulting Placeholder := {";
    retPlaceDBM->print_constraint(std::cerr);
    cpplog(cpplogging::debug) << "} ----"<<  std::endl <<  std::endl;
  }

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

  if (cpplogEnabled(cpplogging::debug)) {
    print_sequent_placeCheck(std::cerr, step - 1, retVal, lhs, place, retPlaceDBM, sub, rhs->getOpType());
    if(retVal) {
      cpplog(cpplogging::debug) <<"----(Valid) Final Placeholder Check Passed-----" <<  std::endl
      <<"--With Placeholder := {";
      retPlaceDBM->print_constraint(std::cerr);
      cpplog(cpplogging::debug) <<"} ----" <<  std::endl <<  std::endl;
    }
    else {
      cpplog(cpplogging::debug) <<"----(Invalid) Final Placeholder Check Failed-----" <<  std::endl <<  std::endl;

    }
  }

  delete phi2PredPlace;
  delete phi2Place;
  delete tPlace;
  return retPlaceDBM;
}

inline DBMList* prover::do_proof_place_allact(int step, DBM* const lhs, DBMList* const place,
                                          const ExprNode* const rhs, SubstList* const sub)
{
  *retPlaceDBM = (*place);
  /* Enumerate through all transitions */
  cpplog(cpplogging::debug) << "\t Proving ALLACT Transitions:----\n" <<  std::endl;

  /* For reasons to avoid convexity until the end, find all of the
   * placeholders for each clause individually. For all transitions
   * that can be executed, store the resulting placeholders with transitions
   * so that we only need to give a non-convex placeholder when finished */
  std::vector<DBMList * > transPlaceHolders;
  bool emptyRetPlace = false;
  for(std::vector<Transition *>::const_iterator it = input_pes.transitions().begin();
      it != input_pes.transitions().end(); it++ ) {
    Transition * tempT = *it;

    /* Obtain the entire ExprNode and prove it */
    DBM tempLHS(*lhs);

    DBMList guardPlace(*place);
    bool tempBool = comp_ph_all_place(&tempLHS, &guardPlace, *(tempT->getLeftExpr()), *sub);
    if(tempBool == false) {
      cpplog(cpplogging::debug) << "Transition: " << tempT << " cannot be taken." << std::endl;
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
      const std::vector<std::pair<short int, short int> > * av = tempT->getAssignmentVector();
      if(av != NULL) {
        // Iterate over the vector and print it
        for(std::vector<std::pair<short int, short int> >::const_iterator it=av->begin(); it != av->end(); it++) {
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

          if (cpplogEnabled(cpplogging::debug)) {
            cpplog(cpplogging::debug) << "Transition: " << tempT;
            cpplog(cpplogging::debug) << " cannot be taken; entering invariant is false." <<  std::endl;
            cpplog(cpplogging::debug) << "\tExtra invariant condition: ";
            invPlace.print_constraint(std::cerr);
            cpplog(cpplogging::debug) <<  std::endl;
          }

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
    cpplog(cpplogging::debug) << "Executing transition (with destination) " << tempT << std::endl;
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
    for(std::vector<DBMList * >::iterator it = transPlaceHolders.begin(); it != transPlaceHolders.end(); it++) {
      /* Intersecting alone is not good enough, so need to do both */
      *retPlaceDBM & *(*it);
      retPlaceDBM->cf();
    }

  }

  // Now go through the vector and delete everything in the vector
  // (Don't delete the transitions since we passed references,
  // but do delete the DBMLists since we passed copies)
  for(std::vector< DBMList * >::iterator it = transPlaceHolders.begin(); it != transPlaceHolders.end(); it++) {
    delete (*it);
  }
  transPlaceHolders.clear();

  if(cpplogEnabled(cpplogging::debug)) {
    cpplog(cpplogging::debug) << "\t --- end of ALLACT. Returned plhold: ";
    retPlaceDBM->print_constraint(std::cerr);
    cpplog(cpplogging::debug) <<  std::endl;
  }

  return retPlaceDBM;
}

inline DBMList* prover::do_proof_place_existact(int step, DBM* const lhs, DBMList* const place,
                                          const ExprNode* const rhs, SubstList* const sub)
{
  bool retVal = false;
  retPlaceDBM->makeEmpty();
  /* Enumerate through all transitions */
  cpplog(cpplogging::debug) << "\t Proving EXISTACT Transitions:----\n" <<  std::endl;

  for(std::vector<Transition *>::const_iterator it = input_pes.transitions().begin();
      it != input_pes.transitions().end(); it++ ) {
    Transition * tempT = *it;

    /* Obtain the entire ExprNode and prove it */

    DBMList tempPlace(*place);
    DBM tempLHS(*lhs);
    // Method tightens lhs and place
    bool tempBool = comp_ph_exist_place(&tempLHS, &tempPlace, *(tempT->getLeftExpr()), *sub);
    if(tempBool == false) {
      cpplog(cpplogging::debug) << "Transition: " << tempT << " cannot be taken." << std::endl;
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
      const std::vector<std::pair<short int, short int> > * av = tempT->getAssignmentVector();
      if(av != NULL) {
        // Iterate over the vector and print it
        for(std::vector<std::pair<short int, short int> >::const_iterator it=av->begin(); it != av->end(); it++) {
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
          if (cpplogEnabled(cpplogging::debug)) {
            cpplog(cpplogging::debug) << "Transition: " << tempT;
            cpplog(cpplogging::debug) << " cannot be taken; entering invariant is false." <<  std::endl;
            cpplog(cpplogging::debug) << "\tExtra invariant condition: ";
            invCons.print_constraint(std::cerr);
            cpplog(cpplogging::debug) <<  std::endl;
          }

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

    if (cpplogEnabled(cpplogging::debug)) {
      cpplog(cpplogging::debug) << "Executing transition (with destination) " << tempT << std::endl;
      cpplog(cpplogging::debug) << "\tExtra invariant condition: ";
      invCons.print_constraint(cpplogGet(cpplogging::debug));
      cpplog(cpplogging::debug) <<  std::endl;
    }

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

  if(cpplogEnabled(cpplogging::debug)) {
    cpplog(cpplogging::debug) << "\t --- end of EXISTACT. Returned plhold: ";
    retPlaceDBM->print_constraint(cpplogGet(cpplogging::debug));
    cpplog(cpplogging::debug) <<  std::endl;
  }

  return retPlaceDBM;
}

inline DBMList* prover::do_proof_place_imply(int step, DBM* const lhs, DBMList* const place,
                                          const ExprNode* const rhs, SubstList* const sub)
{
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
    *retPlaceDBM = (*place);
    cpplog(cpplogging::debug) << "---(Valid) Leaf IMPLY Reached, Premise Not Satisfied----" <<  std::endl <<  std::endl;
  }
  return retPlaceDBM;
}

inline DBMList* prover::do_proof_place_constraint(DBM* const lhs, DBMList* const place,
                                          const ExprNode* const rhs)
{
  lhs->cf();
  // The line: (rhs->dbm())->cf(); is not needed.
  if(*lhs <= *(rhs->dbm())) {
    *retPlaceDBM = (*place);
    cpplog(cpplogging::debug) << "---(Valid) Leaf DBM (CONSTRAINT) Reached with no need for Placeholder----" <<  std::endl <<  std::endl;
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
    if(tPlace.emptiness())
    {
      // New Combined DBM Does not satisfy Constraint
      retPlaceDBM->makeEmpty();
    }
    if(cpplogEnabled(cpplogging::debug)) {
      if(tPlace.emptiness()) {
        cpplog(cpplogging::debug) << "---(Invalid, Placeholder) Leaf DBM (CONSTRAINT) Unsatisfied regardless of placeholder----" <<  std::endl <<  std::endl;
      }
      else {
        cpplog(cpplogging::debug) << "---(Valid, Placeholder) Leaf DBM (CONSTRAINT) Reached and Placeholder Computed----" <<  std::endl <<
        "----Placeholder := {";
        retPlaceDBM->print_constraint(cpplogGet(cpplogging::debug));
        cpplog(cpplogging::debug) << "}----" <<  std::endl <<  std::endl;
      }
    }
  }
  return retPlaceDBM;
}

inline DBMList* prover::do_proof_place_bool(DBMList* const place, const ExprNode* const rhs)
{
  if(rhs->getBool()) {
    *retPlaceDBM = (*place);
    cpplog(cpplogging::debug) << "---(Valid) Leaf BOOL Reached----" <<  std::endl <<  std::endl;
  }
  else{
    retPlaceDBM->makeEmpty();
    cpplog(cpplogging::debug) << "---(Invalid) Leaf BOOL Reached----" <<  std::endl <<  std::endl;
  }

  return retPlaceDBM;
}

inline DBMList* prover::do_proof_place_atomic(DBMList* const place,
                                          const ExprNode* const rhs, SubstList* const sub)
{
  bool retVal = (sub->at(rhs->getAtomic()) == rhs->getIntVal());
  if(retVal) {
    *retPlaceDBM = (*place);
    cpplog(cpplogging::debug) << "---(Valid) Leaf ATOMIC == Reached----" <<  std::endl <<  std::endl;
  }
  else{
    retPlaceDBM->makeEmpty();
    cpplog(cpplogging::debug) << "---(Invalid) Leaf ATOMIC == Reached----" <<  std::endl <<  std::endl;
  }
  return retPlaceDBM;
}

inline DBMList* prover::do_proof_place_atomic_not(DBMList* const place,
                                          const ExprNode* const rhs, SubstList* const sub)
{
  bool retVal = (sub->at(rhs->getAtomic()) != rhs->getIntVal());
  if(retVal) {
    *retPlaceDBM = (*place);
    cpplog(cpplogging::debug) << "---(Valid) Leaf ATOMIC != Reached----" <<  std::endl <<  std::endl;
  }
  else{
    retPlaceDBM->makeEmpty();
    cpplog(cpplogging::debug) << "---(Invalid) Leaf ATOMIC != Reached----" <<  std::endl <<  std::endl;
  }
  return retPlaceDBM;
}

inline DBMList* prover::do_proof_place_atomic_lt(DBMList* const place,
                                          const ExprNode* const rhs, SubstList* const sub)
{
  bool retVal = (sub->at(rhs->getAtomic()) < rhs->getIntVal());
  if(retVal) {
    *retPlaceDBM = (*place);
    cpplog(cpplogging::debug) << "---(Valid) Leaf ATOMIC < Reached----" <<  std::endl <<  std::endl;
  }
  else{
    retPlaceDBM->makeEmpty();
    cpplog(cpplogging::debug) << "---(Invalid) Leaf ATOMIC < Reached----" <<  std::endl <<  std::endl;
  }
  return retPlaceDBM;
}

inline DBMList* prover::do_proof_place_atomic_gt(DBMList* const place,
                                          const ExprNode* const rhs, SubstList* const sub)
{
  bool retVal = (sub->at(rhs->getAtomic()) > rhs->getIntVal());
  if(retVal) {
    *retPlaceDBM = (*place);
    cpplog(cpplogging::debug) << "---(Valid) Leaf ATOMIC > Reached----" <<  std::endl <<  std::endl;
  }
  else{
    retPlaceDBM->makeEmpty();
    cpplog(cpplogging::debug) << "---(Invalid) Leaf ATOMIC > Reached----" <<  std::endl <<  std::endl;
  }
  return retPlaceDBM;
}

inline DBMList* prover::do_proof_place_atomic_le(DBMList* const place,
                                          const ExprNode* const rhs, SubstList* const sub)
{
  bool retVal = (sub->at(rhs->getAtomic()) <= rhs->getIntVal());
  if(retVal) {
    *retPlaceDBM = (*place);
    cpplog(cpplogging::debug) << "---(Valid) Leaf ATOMIC < Reached----" <<  std::endl <<  std::endl;
  }
  else{
    retPlaceDBM->makeEmpty();
    cpplog(cpplogging::debug) << "---(Invalid) Leaf ATOMIC < Reached----" <<  std::endl <<  std::endl;
  }
  return retPlaceDBM;
}

inline DBMList* prover::do_proof_place_atomic_ge(DBMList* const place,
                                          const ExprNode* const rhs, SubstList* const sub)
{
  bool retVal = (sub->at(rhs->getAtomic()) >= rhs->getIntVal());
  if(retVal) {
    *retPlaceDBM = (*place);
    cpplog(cpplogging::debug) << "---(Valid) Leaf ATOMIC > Reached----" <<  std::endl <<  std::endl;
  }
  else{
    retPlaceDBM->makeEmpty();
    cpplog(cpplogging::debug) << "---(Invalid) Leaf ATOMIC > Reached----" <<  std::endl <<  std::endl;
  }
  return retPlaceDBM;
}

inline DBMList* prover::do_proof_place_sublist(int step, DBM* const lhs, DBMList* const place,
                                          const ExprNode* const rhs, SubstList* const sub)
{
  SubstList st(rhs->getSublist(), sub );
  retPlaceDBM = do_proof_place(step, lhs, place, rhs->getExpr(), &st);
  return retPlaceDBM;
}

inline DBMList* prover::do_proof_place_reset(int step, DBM* const lhs, DBMList* const place,
                                          const ExprNode* const rhs, SubstList* const sub)
{
  bool retVal = false;
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

    if (cpplogEnabled(cpplogging::debug)) {
      print_sequent_placeCheck(std::cerr, step - 1, retVal, lhs, retPlaceDBM, &p2Copy, sub, rhs->getOpType());
      if(retVal) {
        cpplog(cpplogging::debug) <<"----(Valid) Placeholder Check Passed-----" <<  std::endl
        <<"--With Placeholder := {";
        retPlaceDBM->print_constraint(cpplogGet(cpplogging::debug));
        cpplog(cpplogging::debug) <<"} ----" <<  std::endl <<  std::endl;
      }
      else {
        cpplog(cpplogging::debug) <<"----(Invalid) Placeholder Check Failed-----" <<  std::endl <<  std::endl;

      }
    }
  }
  return retPlaceDBM;
}

inline DBMList* prover::do_proof_place_assign(int step, DBM* const lhs, DBMList* const place,
                                          const ExprNode* const rhs, SubstList* const sub)
{
  bool retVal = false;
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

    if (cpplogEnabled(cpplogging::debug)) {
      print_sequent_placeCheck(std::cerr, step - 1, retVal, lhs, place, &tmp2, sub, rhs->getOpType());
      if(retVal) {
        cpplog(cpplogging::debug) <<"----(Valid) Placeholder Check Passed-----" <<  std::endl
        <<"--With Placeholder := {";
        retPlaceDBM->print_constraint(cpplogGet(cpplogging::debug));
        cpplog(cpplogging::debug) <<"} ----" <<  std::endl <<  std::endl;
      }
      else {
        cpplog(cpplogging::debug) <<"----(Invalid) Placeholder Check Failed-----" <<  std::endl <<  std::endl;

      }
    }

  }
  return retPlaceDBM;
}

inline DBMList* prover::do_proof_place_replace(int step, DBM* const lhs, DBMList* const place,
                                          const ExprNode* const rhs, SubstList* const sub)
{
  sub->operator[](rhs->getcX()) = sub->at(rhs->getcY());
  retPlaceDBM = do_proof_place(step, lhs, place, rhs->getExpr(), sub);
  return retPlaceDBM;
}

inline DBMList* prover::do_proof_place_ablewaitinf(DBM* const lhs, DBMList* const place,
                                            SubstList* const sub)
{
  bool retVal = false;
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
  std::vector <DBM *> * currList = ph.getDBMList();
  DBM * currDBM = (*currList)[0];
  retVal = !(currDBM->hasUpperConstraint());
  if(retVal) {
    *retPlaceDBM = (*place);
    cpplog(cpplogging::debug) << "---(Valid) Time able to diverge to INFTY in current location----" <<  std::endl <<  std::endl;
  }
  else{
    retPlaceDBM->makeEmpty();
    cpplog(cpplogging::debug) << "---(Invalid) Time unable to diverge to INFTY in current location---" <<  std::endl <<  std::endl;
  }
  return retPlaceDBM;
}

inline DBMList* prover::do_proof_place_unablewaitinf(DBM* const lhs, DBMList* const place, SubstList* const sub)
{
  lhs->cf();
  DBMList ph(*lhs);
  ph & *place;
  ph.cf();
  ph.suc();
  invs_chk(input_pes.invariants(), &ph, *sub);
  ph.cf();
  /* Time cannot diverge if and only if there is an upper bound
   * constraint in the successor. By design of succ() and invariants,
   * either all DBMs have an upper bound constraint, or none
   * of them do. Hence, checking the first is always good enough. */
  std::vector <DBM *> * currList = ph.getDBMList();
  DBM * currDBM = (*currList)[0];
  if(currDBM->hasUpperConstraint()) {
    *retPlaceDBM = (*place);
    cpplog(cpplogging::debug) << "---(Valid) Time unable to diverge to INFTY in current location----" <<  std::endl <<  std::endl;
  }
  else{
    retPlaceDBM->makeEmpty();
    cpplog(cpplogging::debug) << "---(Invalid) Time able to diverge to INFTY in current location---" <<  std::endl <<  std::endl;
  }
  return retPlaceDBM;
}


#endif /* PROOF_HH */
