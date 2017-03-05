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
  bool debug;
  const pes& input_pes;

  bool currParityGfp;
  bool prevParityGfp;
  bool useCaching;

  /* The size of the Hash table of Sequents: nBits + 1 */
  int  nHash;

  long int numLocations;

  /** This parameter is the size of the maximum
   * constant (in the clock constraints).  There
   * is one constant for all of the clocks
   * This is modified by the program and the parser. */
  int MAXC;

  /** The maximum number of bits used in the hashing function
   * when storing discrete states. */
  int nbits;

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
  prover(const pes& a_input_pes,
         bool a_currParityGfp, bool a_prevParityGfp, bool a_useCaching,
         int a_nHash, bool debug, int MAXC,
         int nbits) :
  debug(debug),
  input_pes(a_input_pes),
  currParityGfp(a_currParityGfp),
  prevParityGfp(a_prevParityGfp),
  useCaching(a_useCaching),
  nHash(a_nHash),
  numLocations(1),
  MAXC(MAXC),
  nbits(nbits),
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

#endif /* PROOF_HH */
