/** \mainpage CWB-RT PES Tool pes.timed 1.0
 *
 * A proof-based timed automata model checker.
 * @author Peter Fontana, Dezhuang Zhang, and Rance Cleaveland. 
 * @version 1.21
 * @date November 8, 2013 */

/** \file demo.cc
 * The main file of the timed automata model checker. This file
 * contains the bulk of the proof engine and the model checking
 * algorithms, including the implementation of the PES proof rules.
 * @author Peter Fontana, Dezhuang Zhang, and Rance Cleaveland. 
 * @version 1.21
 * @date November 8, 2013 */

#include <iostream>
#include <string.h>
#include <stdio.h>
#include <map>
#include <set>
#include <deque>
#include <vector>
#include <list>
#include <utility>
#include <sys/timeb.h>
#include <time.h>
#include <unistd.h>
#include "ExprNode.hh"
#include "errno.h"

using namespace std;

/** Defines DEBUG mode to True (1)
 * if not already defined. */
#ifndef DEBUG
#define DEBUG 1
#endif

/** The location of the File pointer
 * for the lexer.
 * @see pes.l and pes.lex.c (lexer files). */
extern FILE *yyin;
/** The method that parses the lexed file
 * and creates the ExprNode objects.
 * @return 0 if successful, 1 if syntax error,
 * and 2 if out of memory error (usually).
 * @see pes.y pes.tab.h and pes.tab.c (parser files). */
extern int yyparse();

/** The string label of the starting predicate, which
 * should be label the root ExprNode of the expression tree.
 * @see pes.y and pes.tab.c (parser files). */
extern char * start_predicate;

/** A global variable for the predicate
 * index to represent a counter on the number
 * of predicates to allow for hashing of sequents
 * to bin by predicate label/index. 
 * By the time it reaches the demo.cc file, predicateInd's
 * value is the number of predicate variables. */
extern int predicateInd; 

/** A Hash Table of clocks used to store the clocks,
 * mapping string symbols to clock indices. 
 * @see ExprNode.cc */
extern map <string, int > clocks;
/** A Hash table of Atomic values used to store discrete state
 * variables, mapping string names to id values. 
 * @see ExprNode.cc. */
extern map <string, int > atomic;
/** A Hash table of ints storing integer 
 * substituations for atomic variables. 
 * This maps atomic ids to atomic values, representing
 * the "inital" state for each control (atomic) variable.
 * The map is represented as: (id, val).  0 is the default value. 
 * @see ExprNode.cc */
extern map <int, int> InitSub;
/** A Hash table storing the list of declared predicates,
 * matching their string label with blank PREDICATE expressions. 
 * These blank PREDICATE expressions make sequent caching and
 * proof exploration easier and faster. */
extern map <string, ExprNode *> predicates;
/** A Hash table storing a list of PES variables, with their 
 * string labels
 * and the right hand side expressions in their equations. */
extern map <string, ExprNode *> equations;


/** This is a vector (list) of all invariants with their
 * ExprNodes.
 * This is constructed by the parser while the ExprNode Trees
 * are being generated.
 * @see pes.y and pes.tab.c (parser files). */
extern vector<ExprNode *>invs;
/** This represents the number of clocks in the timed automata, which
 * is referred to the number of dimensions (the space) of the automata.
 * This number includes the dummy "zero" clock.
 * @see ExprNode.cc*/
extern int spaceDimension;

/** This is the list of transitions of the state machine
 * from the automata/PES description. */
extern vector<Transition *> *transList;

/** This defines a stack as a vector of Sequent 
 * arrays (Sequents). */
typedef vector<Sequent*>  stack;
/** Now define a stack of placeholder sequents.
 * Idea: Instead of intersecting the sequent with the placeholder,
 * store the sequents with placeholders separately. */
typedef vector<SequentPlace *> stackPlace;

/** This defines a DBMset as a vector of DBM 
 * arrays (DBM Arrays). */
typedef vector<DBM*>  DBMset;
/** Defines a vector of (DBM, DBMList) pairs. Used for lists
 * of placeholder proofs, since (for faster performance) the union
 * of clock zones is restricted to placeholders. */
typedef vector<pair<DBM *, DBMList *> > DBMPlaceSet;

/* Make Different Sequent Stacks:
 * 1) Possible GFP Circularity
 * 2) Possible LFP Circularity
 * 3) Sequents Proven True
 * 4) Sequents Proven False
 * Also make equivalent stacks for placeholder sequents.
 * Note: This engine only supports alternation-free formulas.
 */
 
/** XList_pGFP (XList) is an array of stacks, where each stack
 * is an array of sequents that
 * keeps track of all possible GFP Sequents
 * used for circularity (valid proofs). */
stack *Xlist_pGFP;
/** XList_pLFP is an array of stacks of sequents that
 * keeps track of all possible LFP Sequents
 * used for circularity (invalid proofs). */
stack *Xlist_pLFP;
/** XList_true is an array of stacks of sequents that
 * keeps track of all previously proven true sequents. */
stack *Xlist_true;
/** XList_false is an array stacks of sequents that
 * keeps track of all previously proven false sequents. */
stack *Xlist_false;

/** A Placeholder to remember the current parity;
 * false = lfp parity, true = gfp parity. */
bool currParityGfp;
/** A Placeholder to remember the previous parity;
 * false = lfp parity, true = gfp parity. */
bool prevParityGfp;

/** A boolean used to tell if the located sequent was
 * newly-added to the cache. If it is true, then that sequent
 * has no left-hand clock states, and is empty; hence, it need
 * not be examined by table-sequent.*/
bool newSequent;

/** XList_pGFP_ph (XList) is an array of stacks, where each stack
 * is an array of sequents that
 * keeps track of all possible GFP Sequents
 * used for circularity (valid proofs) when placeholders are involved. */
stackPlace *Xlist_pGFP_ph;
/** XList_pLFP_ph is an array of stacks of sequents that
 * keeps track of all possible LFP Sequents
 * used for circularity (invalid proofs) 
 * when placeholders are involved. */
stackPlace *Xlist_pLFP_ph;
/** XList_true_ph is an array of stacks of sequents that
 * keeps track of all previously proven true sequents 
 * where placeholders are involved. */
stackPlace *Xlist_true_ph;
/** XList_false_ph is an array of stacks of sequents that
 * keeps track of all previously proven false sequents 
 * where placeholders are involved. Because a false sequent
 * means that no such placeholder is possible (the placeholder
 * is empty), this structure does not need the overhead of
 * placeholders. */
stackPlace *Xlist_false_ph;

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

/** This DBM represents the initial DBM provided
 * if one is provided by the parser. */
DBM *InitC;

/** This DBM is used as a DBM with
 * the proper number of clocks and initialized
 * so that it represents the empty region 
 * (for all clocks x_i, 0 <= x_i <= 0). */
DBM *EMPTY;

/** This DBM is a copy of a DBM initially 
 * that represents the unconstrained DBM in 
 * canonical form. */
DBM *INFTYDBM;

/** DBMList used as the value of the returned placeholder.
 * this is initialized outside of do_proof_place() to prevent
 * multiple re-initializations of it. */
DBMList * retPlaceDBM;

/** True if debug mode is on, and
 * False if debug mode is off. Running the
 * program with -d sets it to true. */
bool debug = false;

/** This is the size of the atomic data, used for
 * hashing sequents.
 * This is set within the main(0) method of
 * this file (demo.cc). */
int aSize = 0;

/** This parameter is the size of the maximum
 * constant (in the clock constraints).  There
 * is one constant for all of the clocks
 * This is modified by the program and the parser. */
int MAXC = 0;

/** The maximum number of bits used in the hashing function
 * when storing discrete states. */
int nbits = 0xF;

/** Public variable that stores the number of hashing bins.
 * used for ease of locating the proper bin for each sequent,
 * especially when multiple predicate variables exist. */
int seqStSize = 0xF;


/** Debug boolean to enable or disable known true and known false caches.
 * This parameter does not influence caching of circularities. As a result,
 * correctness is guaranteed but performance is slowed if set to FALSE */
bool useCaching = true;

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
inline int hash_func(SubstList *sub){
  // From demo.7.cc (instead of from demo.cc) of previous code
	int sum = 0;
  for(int i=0; i<aSize; i++){
    sum += (sub->operator[](i) & nbits);
    sum = sum & nbits;
  }   
  return sum; 
}

long int numLocations;


/** Prints out the "help" info for the user or
 * the information that is displayed when the
 * user does not give or format the argument properly. 
 * @return none.*/
void printUsage(){
  cout << "usage: demo options input_file_name" << endl;
  cout << "\t option: -d  print debug information which includes the proof tree" << endl;
  cout << "\t option: -t print out the end caches of sequents" << endl; 
  cout << "\t option: -h  this help info" << endl;
  cout << "\t option: -n (no caching) disables performance-optimizing known true and known false caches. Circularity stack caching still used." << endl;
}

/** Prints out all of the sequents in the list; the printing (for
 * ease of implementation) prints out the set of DBMs representing the set of 
 * sequents with matching discrete location values and matching right hand
 * sides. Typically, the right hand sides will be predicate variables.
 * @param Xlist (*) The stack of sequents to print.
 * @return None. */
void print_Xlist(stack *Xlist){
	int totNumSeq = 0;
	cout << "\t--For Each Sequence, Premise sets separated by \";\" --" << endl;
  for(int i = 0; i < predicateInd*(nbits+1); i++){
    for(stack::iterator it = Xlist[i].begin(); it != Xlist[i].end(); it++){
      int conseqNumSeq = 0;
      for(DBMset::iterator ie = (*it)->ds.begin(); ie != (*it)->ds.end(); ie++){
        (*ie)->print_constraint();
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
void print_Xlist(stackPlace *Xlist){
	int totNumSeq = 0;
	cout << "\t--For Each Sequence, Premise sets separated by \";\" --" << endl;
  for(int i = 0; i < predicateInd*(nbits+1); i++){
    for(stackPlace::iterator it = Xlist[i].begin(); it != Xlist[i].end(); it++){
      int conseqNumSeq = 0;
      for(DBMPlaceSet::iterator ie = (*it)->dsp.begin(); ie != (*it)->dsp.end(); ie++){
        (*ie).first->print_constraint();
        cout << ", plhold: ";
        (*ie).second->print_constraint();
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

/** Internal prover for evaluating if the sublist satisfies
 * the atomic proposition expression as the invariant precondition
 * for each invariant conjunct.
 * @param e (*) The expression to evaluate; assumed to be the left hand side
 * of the invariant implication.
 * @param sublist (*) The discrete location of the left hand side.
 * @return true: the expression evaluates to true, false: otherwise (if
 * the set of discrete and clock states satisfying the premise is empty).*/
bool comp_ph_invs(ExprNode *e, SubstList *sublist)
{
  switch (e->getOpType())
  {
    case ATOMIC : {
      return (sublist->operator[](e->getAtomic()) == e->getIntVal());
      break; }
    case ATOMIC_NOT : {
      return (sublist->operator[](e->getAtomic()) != e->getIntVal());
      break; }
    case ATOMIC_LT : {
      return (sublist->operator[](e->getAtomic()) < e->getIntVal());
      break; }
    case ATOMIC_GT : {
      return (sublist->operator[](e->getAtomic()) > e->getIntVal());
      break; }
    case ATOMIC_LE : {
      return (sublist->operator[](e->getAtomic()) <= e->getIntVal());
      break; }
    case ATOMIC_GE : {
      return (sublist->operator[](e->getAtomic()) >= e->getIntVal());
      break; }
    case AND : {
      return (comp_ph_invs(e->getLeft(), sublist) 
              &&
              comp_ph_invs(e->getRight(), sublist));
      break; }
    case OR : {
      /* We only have atomic booleans so this simplified rule works. */
      return (comp_ph_invs(e->getLeft(), sublist) 
              ||  
              comp_ph_invs(e->getRight(), sublist));
      break; }
    case OR_SIMPLE : {
      /* We only have atomic booleans so this simplified rule works. */
      return (comp_ph_invs(e->getLeft(), sublist) 
              ||  
              comp_ph_invs(e->getRight(), sublist));
      break; }
    default: {
      cerr << "Not a valid condition" <<endl;
      exit(1); }  
  }
  return false;
}


/** Takes in the specified DBM and tightens it
 * to satisfy the invariants required of the specified
 * discrete state. When finished, any nonempty DBM now satisfies
 * the invariants. This method is used when executing transitions
 * after a time successor (FORALL operator); If DBM lhs is the
 * time successor of zone z, after this method lhs will be the
 * time successor zone of z in location sub.
 * Remember:  The INVARIANT is assumed to be a list of clauses of:
 *		Prop = Val -> DBM Constraints. 
 * @param lhs (*) The DBM to alter.
 * @param sub (*) The discrete state (location variable assignment) 
 * of the sequent.
 * @return true: the model has a non-vacuous invariant; false: otherwise. */
inline bool invs_chk(DBM *lhs, SubstList *sub){
  bool outRes = false;
  if (invs.empty()) return false;
  for (int i=0; i < sub->nElements(); i++){
    for (vector<ExprNode*>::iterator it = invs.begin(); it != invs.end(); it++){
      if (comp_ph_invs((*it), sub)) {
        (*lhs) & (*(*it)->dbm()) ;
        outRes = true;
      }
    }  
  }
  return outRes;
}

/** Takes in the specified DBMList and tightens it
 * to satisfy the invariants required of the specified
 * discrete state. When finished, any nonempty DBMList now satisfies
 * the invariants. This method is used when executing transitions
 * after a time successor (FORALL operator); If DBMList lhs is the
 * time successor of set of valuations z, after this method lhs will be the
 * time successor the set of valuations z in location sub.
 * Remember:  The INVARIANT is assumed to be a list of clauses of:
 *		Prop = Val -> DBM Constraints. (all constraints are clock zones) 
 * @param lhs (*) The DBMList to alter.
 * @param sub (*) The discrete state (location variable assignment) 
 * of the sequent.
 * @return true: the DBMList is changed; false: otherwise. */
inline bool invs_chk(DBMList * lhs, SubstList *sub){
  bool outRes = false;
  if (invs.empty()) return false;
  vector<DBM *> * lList = lhs->getDBMList();
  for(unsigned int i = 0; i < lList->size(); i++) {
    bool temp = invs_chk((*lList)[i], sub);
    outRes = temp || outRes;
  }
  return outRes;
}

/** Simplified and performance-optimized proof engine for (AllAct) transitions
 * and IMPLY nodes. This method assumes that the expression e
 * is either the left hand side of an IMPLY node or the conditions
 * of a transition. Given the assumption that its is working on the left
 * hand implication of a possible transition (potentially with an invariant),
 * it utilizes a simpler proof-rule scheme. Using comp_ph(...) instead
 * of do_proof(...) (or do_proof_place(...)) results in faster performance
 * since it can be specialized for this specific subset of PES. This prover
 * evaluates the fed in expression to true or false.
 * Since the comp_ph(...) constraints are often guards and the DBM
 * is a clock zone, to find the set of clock valuations that can execute
 * this transition from the fed in DBM, comp_ph(...)
 * tightens the DBM to satisfy the constraints (assumed to be in the left
 * hand-side of an implication). It returns false if the set of constraints 
 * is empty.
 * @param ph (*) The DBM representing the clock constraints.
 * @param e (*) The expression to evaluate; assumed to be the left hand side
 * of an implication or the conditions of a transition.
 * @param sublist (*) The discrete location of the left hand side.
 * @return true: the expression evaluates to true (and ph is
 * tightened to make the expression true), false: otherwise (if
 * the set of discrete and clock states satisfying the premise is empty).*/
bool comp_ph(DBM *ph, ExprNode *e, SubstList *sublist)
{
  switch (e->getOpType())
  {
    case CONSTRAINT : {
      (*ph) & (*(e->dbm()));
      ph->cf(); // Calls Canonical Form Here.
      return (!(ph->emptiness()));
      break; }
    case BOOL : {
      return (e->getBool());
      break; }
    case ATOMIC : {
      return (sublist->operator[](e->getAtomic()) == e->getIntVal());
      break; }
    case ATOMIC_NOT : {
      return (sublist->operator[](e->getAtomic()) != e->getIntVal());
      break; }
    case ATOMIC_LT : {
      return (sublist->operator[](e->getAtomic()) < e->getIntVal());
      break; }
    case ATOMIC_GT : {
      return (sublist->operator[](e->getAtomic()) > e->getIntVal());
      break; }
    case ATOMIC_LE : {
      return (sublist->operator[](e->getAtomic()) <= e->getIntVal());
      break; }
    case ATOMIC_GE : {
      return (sublist->operator[](e->getAtomic()) >= e->getIntVal());
      break; }
    case AND : {
      return (comp_ph(ph, e->getLeft(), sublist) 
              &&
              comp_ph(ph, e->getRight(), sublist));
      break; }
    case OR : {
      /* This OR rule only works when there is at most one constraint.
       * By definition of its input, we have a discrete state (with
       * && and || notes) conjuncted with an intersection of constraints.
       * By construction of the fed input to this function, the above
       * bad case will never occur. */
      return (comp_ph(ph, e->getLeft(), sublist) 
              ||  
              comp_ph(ph, e->getRight(), sublist));
      break; }
    case OR_SIMPLE : {
      /* This OR rule only works when there is at most one constraint.
       * By definition of its input, we have a discrete state (with
       * && and || notes) conjuncted with an intersection of constraints.
       * By construction of the fed input to this function, the above
       * bad case will never occur. */
      return (comp_ph(ph, e->getLeft(), sublist) 
              ||  
              comp_ph(ph, e->getRight(), sublist));
      break; }
    default: {
      cerr << "Not a valid condition" <<endl;
      exit(1); }  
  }
  return false;
}


/** Simplified and performance-optimized proof engine for (ExistAct) transitions
 * and AND nodes. This method assumes that the expression e
 * is either the left hand side of an AND node or the conditions
 * of a transition. Given the assumption that its is working on the left
 * hand implication of a possible transition (potentially with an invariant),
 * it utilizes a simpler proof-rule scheme. Using comp_ph(...) instead
 * of do_proof(...) (or do_proof_place(...)) results in faster performance
 * since it can be specialized for this specific subset of PES. This prover
 * evaluates the fed in expression to true or false.
 * For this method, the DBM must completely satisfy all clock constraints;
 * it is not tightened by the prover.
 * @param ph (*) The DBM representing the clock constraints.
 * @param e (*) The expression to evaluate; assumed to be the left hand side
 * of an implication or the conditions of a transition.
 * @param sublist (*) The discrete location of the left hand side.
 * @return true: the expression evaluates to true (and ph is
 * tightened to make the expression true), false: otherwise (if
 * the set of discrete and clock states satisfying the premise is empty).*/
bool comp_ph_exist(DBM *ph, ExprNode *e, SubstList *sublist)
{
  switch (e->getOpType())
  {
    case CONSTRAINT : {
      ph->cf();
      return (*ph) <= (*(e->dbm()));
      break; }
    case BOOL : {
      return (e->getBool());
      break; }
    case ATOMIC : {
      return (sublist->operator[](e->getAtomic()) == e->getIntVal());
      break; }
    case ATOMIC_NOT : {
      return (sublist->operator[](e->getAtomic()) != e->getIntVal());
      break; }
    case ATOMIC_LT : {
      return (sublist->operator[](e->getAtomic()) < e->getIntVal());
      break; }
    case ATOMIC_GT : {
      return (sublist->operator[](e->getAtomic()) > e->getIntVal());
      break; }
    case ATOMIC_LE : {
      return (sublist->operator[](e->getAtomic()) <= e->getIntVal());
      break; }
    case ATOMIC_GE : {
      return (sublist->operator[](e->getAtomic()) >= e->getIntVal());
      break; }
    case AND : {
      return (comp_ph_exist(ph, e->getLeft(), sublist) 
              &&
              comp_ph_exist(ph, e->getRight(), sublist));
      break; }
    case OR : {
      /* This OR rule only works when there is at most one constraint.
       * By definition of its input, we have a discrete state (with
       * && and || notes) conjuncted with an intersection of constraints.
       * By construction of the fed input to this function, the above
       * bad case will never occur. */
      return (comp_ph_exist(ph, e->getLeft(), sublist) 
              ||  
              comp_ph_exist(ph, e->getRight(), sublist));
      break; }
    case OR_SIMPLE : {
      /* This OR rule only works when there is at most one constraint.
       * By definition of its input, we have a discrete state (with
       * && and || notes) conjuncted with an intersection of constraints.
       * By construction of the fed input to this function, the above
       * bad case will never occur. */
      return (comp_ph_exist(ph, e->getLeft(), sublist) 
              ||  
              comp_ph_exist(ph, e->getRight(), sublist));
      break; }
    default: {
      cerr << "Not a valid condition" <<endl;
      exit(1); }  
  }
  return false;
}


/** Simplified and performance-optimized proof engine for (ExistAct) transitions
 * and AND nodes within placeholders. This method assumes that the expression e
 * is either the left hand side of an AND node or the conditions
 * of a transition. In both cases, there is a placeholder DBM. 
 * Given the assumption that its is working on the left
 * hand implication of a possible transition (potentially with an invariant),
 * it utilizes a simpler proof-rule scheme. Using comp_ph(...) instead
 * of do_proof(...) (or do_proof_place(...)) results in faster performance
 * since it can be specialized for this specific subset of PES. This prover
 * evaluates the fed in expression to true or false.
 * For this method, the placeholder is tightened to satisfy the constraints.
 * @param ph (*) The DBM representing the clock constraints.
 * @param place (*) The DBMList placeholder.
 * @param e (*) The expression to evaluate; assumed to be the left hand side
 * of an implication or the conditions of a transition.
 * @param sublist (*) The discrete location of the left hand side.
 * @return true: the expression evaluates to true (and ph is
 * tightened to make the expression true), false: otherwise (if
 * the set of discrete and clock states satisfying the premise is empty).*/
bool comp_ph_exist_place(DBM *ph, DBMList * place, ExprNode *e, SubstList *sublist)
{
  switch (e->getOpType())
  {
    case CONSTRAINT : {
      ph->cf();
      DBM * eDBM = e->dbm();
      bool res = (*ph) <= (*eDBM);
      (*ph) & (*eDBM);
      ph->cf(); // Calls Canonical Form Here.
      if(res) {
        return true;
      }
      // We can only tighten if the constraint is not empty
      if(ph->emptiness()) {
        return false;
      }
       /* For now, assume that the placeholder
       * becomes the entire constraint.
       * It may be necessary to make placeholder looser than
       * the constraint to not have inequalities that ph satisfies. */
      *place & (*(e->dbm()));
      place->cf();
      return !(place->emptiness());
      break; }
    case BOOL : {
      return (e->getBool());
      break; }
    case ATOMIC : {
      return (sublist->operator[](e->getAtomic()) == e->getIntVal());
      break; }
    case ATOMIC_NOT : {
      return (sublist->operator[](e->getAtomic()) != e->getIntVal());
      break; }
    case ATOMIC_LT : {
      return (sublist->operator[](e->getAtomic()) < e->getIntVal());
      break; }
    case ATOMIC_GT : {
      return (sublist->operator[](e->getAtomic()) > e->getIntVal());
      break; }
    case ATOMIC_LE : {
      return (sublist->operator[](e->getAtomic()) <= e->getIntVal());
      break; }
    case ATOMIC_GE : {
      return (sublist->operator[](e->getAtomic()) >= e->getIntVal());
      break; }
    case AND : {
      return (comp_ph_exist_place(ph, place, e->getLeft(), sublist) 
              &&
              comp_ph_exist_place(ph, place, e->getRight(), sublist));
      break; }
    case OR : {
      /* This OR rule only works when there is at most one constraint.
       * By definition of its input, we have a discrete state (with
       * && and || notes) conjuncted with an intersection of constraints.
       * By construction of the fed input to this function, the above
       * bad case will never occur. */
      return (comp_ph_exist_place(ph, place, e->getLeft(), sublist) 
              ||  
              comp_ph_exist_place(ph, place, e->getRight(), sublist));
      break; }
    case OR_SIMPLE : {
      /* This OR rule only works when there is at most one constraint.
       * By definition of its input, we have a discrete state (with
       * && and || notes) conjuncted with an intersection of constraints.
       * By construction of the fed input to this function, the above
       * bad case will never occur. */
      return (comp_ph_exist_place(ph, place, e->getLeft(), sublist) 
              ||  
              comp_ph_exist_place(ph, place, e->getRight(), sublist));
      break; }
    default: {
      cerr << "Not a valid condition" <<endl;
      exit(1); }  
  }
  return false;
}

/** Simplified and performance-optimized proof engine for (AllAct) transitions
 * and IMPLY nodes within placeholders. To handle potential complexities later
 * in the proof (when getting a final placeholder), this method takes the guard
 * and tightens the LHS and the placeholder, so the placeholder can be altered
 * if needed.
 * @param ph (*) The DBM representing the clock constraints.
 * @param place (*) The DBMList placeholder to tighten with the guard.
 * @param e (*) The expression to evaluate; assumed to be the left hand side
 * of an implication or the conditions of a transition.
 * @param sublist (*) The discrete location of the left hand side.
 * @return true: the expression evaluates to true (and ph is
 * tightened to make the expression true), false: otherwise (if
 * the set of discrete and clock states satisfying the premise is empty).*/
bool comp_ph_all_place(DBM *ph, DBMList * place, ExprNode *e, SubstList *sublist)
{
  switch (e->getOpType())
  {
    case CONSTRAINT : {
      (*ph) & (*(e->dbm()));
      ph->cf(); // Calls Canonical Form Here.
      bool lhEmpty;
      lhEmpty = ph->emptiness();
      if(lhEmpty) {
        return false;
      }
      *place & (*(e->dbm()));
      place->cf();
      if(place->emptiness()) {
        return false;
      }
      return true;
      break; }
    case BOOL : {
      return (e->getBool());
      break; }
    case ATOMIC : {
      return (sublist->operator[](e->getAtomic()) == e->getIntVal());
      break; }
    case ATOMIC_NOT : {
      return (sublist->operator[](e->getAtomic()) != e->getIntVal());
      break; }
    case ATOMIC_LT : {
      return (sublist->operator[](e->getAtomic()) < e->getIntVal());
      break; }
    case ATOMIC_GT : {
      return (sublist->operator[](e->getAtomic()) > e->getIntVal());
      break; }
    case ATOMIC_LE : {
      return (sublist->operator[](e->getAtomic()) <= e->getIntVal());
      break; }
    case ATOMIC_GE : {
      return (sublist->operator[](e->getAtomic()) >= e->getIntVal());
      break; }
    case AND : {
      return (comp_ph_all_place(ph, place, e->getLeft(), sublist) 
              &&
              comp_ph_all_place(ph, place, e->getRight(), sublist));
      break; }
    case OR : {
      /* This OR rule only works when there is at most one constraint.
       * By definition of its input, we have a discrete state (with
       * && and || notes) conjuncted with an intersection of constraints.
       * By construction of the fed input to this function, the above
       * bad case will never occur. */
      return (comp_ph_all_place(ph, place, e->getLeft(), sublist) 
              ||  
              comp_ph_all_place(ph, place, e->getRight(), sublist));
      break; }
    case OR_SIMPLE : {
      /* This OR rule only works when there is at most one constraint.
       * By definition of its input, we have a discrete state (with
       * && and || notes) conjuncted with an intersection of constraints.
       * By construction of the fed input to this function, the above
       * bad case will never occur. */
      return (comp_ph_all_place(ph, place, e->getLeft(), sublist) 
              ||  
              comp_ph_all_place(ph, place, e->getRight(), sublist));
      break; }
    default: {
      cerr << "Not a valid condition" <<endl;
      exit(1); }  
  }
  return false;
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
 * @param Xlist (*&) The cache of sequents to look in.
 * @param pInd The index of the predicate; used to find the proper hashing bin.
 * @return The reference to the sequent with the three components
 * specified as parameters. */
Sequent * locate_sequent(Sequent *s, stack *& Xlist, int pInd){
  int indexH = hash_func(s->sub());
  int index = pInd*seqStSize + indexH;
  for(stack::iterator it = Xlist[index].begin(); it != Xlist[index].end(); it++){
    Sequent *ls = (*it);
    bool matched = true;
    for(int j = 0; j < aSize; j++){
      if (s->sub()->operator[](j) != ls->sub()->operator[](j)){
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
 * @param Xlist (*&) The cache of placeholder sequents to look in.
 * @param pInd The index of the predicate; used to find the proper hashing bin.
 * @return The reference to the sequent with the three components
 * specified as parameters. */
SequentPlace * locate_sequentPlace(SequentPlace *s, stackPlace *& Xlist, int pInd){
  int indexH = hash_func(s->sub());
  int index = pInd*seqStSize + indexH;
  for(stackPlace::iterator it = Xlist[index].begin(); it != Xlist[index].end(); it++){
    SequentPlace *ls = (*it);
    bool matched = true;
    for(int j = 0; j < aSize; j++){
      if (s->sub()->operator[](j) != ls->sub()->operator[](j)){
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
 * @param Xlist (*&) The cache of sequents to look in.
 * @param pInd The index of the predicate; used to find the proper hashing bin.
 * @return The reference to the sequent with the three components
 * specified as parameters. */
Sequent * look_for_sequent(SubstList *subs, stack *& Xlist, int pInd){
  int indexH = hash_func(subs);
  int index = pInd*seqStSize + indexH;
  for(stack::iterator it = Xlist[index].begin(); it != Xlist[index].end(); it++){
    Sequent *ls = (*it);
    bool matched = true;
    for(int j = 0; j < aSize; j++){
      if (subs->operator[](j) != ls->sub()->operator[](j)){
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
 * @param Xlist (*&) The cache of placeholder sequents to look in.
 * @param pInd The index of the predicate; used to find the proper hashing bin.
 * @return The reference to the sequent with the three components
 * specified as parameters. */
SequentPlace * look_for_sequentPlace(DBMList *lhsPlace, SubstList *subs, stackPlace *& Xlist, int pInd){
  int indexH = hash_func(subs);
  int index = pInd*seqStSize + indexH;
  for(stackPlace::iterator it = Xlist[index].begin(); it != Xlist[index].end(); it++){
    SequentPlace *ls = (*it);
    bool matched = true;
    for(int j = 0; j < aSize; j++){
      if (subs->operator[](j) != ls->sub()->operator[](j)){
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
Sequent * look_for_and_purge_rhs_sequent(DBM *lhs, Sequent *s, stack *& Xlist,
                                    int pInd, bool tableCheck, 
                                    bool * madeEmpty){
  int indexH = hash_func(s->sub());
  int index = pInd*seqStSize + indexH;
  bool matched = false;
  *madeEmpty = false;
  /* This assumes that location only locates one sequent in the stack */
  Sequent * foundSequent = NULL;
  for(stack::iterator it = Xlist[index].begin(); it != Xlist[index].end(); it++){
    Sequent *ls = (*it);
    matched = true; 
    
    for(int j = 0; j < aSize; j++){
      if (s->sub()->operator[](j) != ls->sub()->operator[](j)){
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
SequentPlace * look_for_and_purge_rhs_sequentPlace(DBM *lhs, DBMList *lhsPlace, 
      SequentPlace *s, stackPlace *& Xlist, int pInd, bool tableCheck,
      bool * madeEmpty){
  int indexH = hash_func(s->sub());
  int index = pInd*seqStSize + indexH;
  bool matched = false;
  *madeEmpty = false;
  /* This assumes that location only locates one sequent in the stack */
  SequentPlace * foundSequent = NULL;
  for(stackPlace::iterator it = Xlist[index].begin(); it != Xlist[index].end(); it++){
    SequentPlace *ls = (*it);
    matched = true; 
    
    for(int j = 0; j < aSize; j++){
      if (s->sub()->operator[](j) != ls->sub()->operator[](j)){
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
bool look_for_and_purge_rhs_sequent_state(Sequent *s, stack *& Xlist,
                                    int pInd, bool tableCheck){
  int indexH = hash_func(s->sub());
  int index = pInd*seqStSize + indexH;
  bool matched = false;
  bool foundMatch = false;
  for(stack::iterator it = Xlist[index].begin(); it != Xlist[index].end(); it++){
    Sequent *ls = (*it);
    matched = true; 
    
    for(int j = 0; j < aSize; j++){
      if (s->sub()->operator[](j) != ls->sub()->operator[](j)){
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
      for(vector<DBM *>::iterator itB = ls->ds.begin(); 
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
bool look_for_and_purge_rhs_sequentPlace_state(SequentPlace *s, 
                                    stackPlace *& Xlist, int pInd, bool tableCheck){
  int indexH = hash_func(s->sub());
  int index = pInd*seqStSize + indexH;
  bool matched = false;
  bool foundMatch = false;
  for(stackPlace::iterator it = Xlist[index].begin(); it != Xlist[index].end(); it++){
    SequentPlace *ls = (*it);
    matched = true; 
    
    for(int j = 0; j < aSize; j++){
      if (s->sub()->operator[](j) != ls->sub()->operator[](j)){
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

/** Using that a Sequent object is a set of sequents with matching rhs and
 *  discrete states with different clock states, determines if the specified
 * DBM is contained within one of the sequents. This is used for greatest
 * fixpoint circularity (or known true sequents), since by definition
 * of sequents, if sequent B is true and A <= B (the right hand side matches
 * and the left hand state of A is a subset of the states in B), A is also true.
 * For this method, each B *(*it) is a known sequent and lhs is the clock state
 * of A. This method assumes that the right hand side and discrete states match
 * (and is often called after locate_sequent() or look_for_sequent()); hence,
 * it only needs to compare clock states. 
 * @param s (*) The sequent that contains a set of DBMs.
 * @param lhs (*) The DBM to compare the sequent's DBMs to.
 * @return true: lhs <= some sequent in s 
 * (consequently, the sequent is true), false: otherwise.*/
bool tabled_sequent(Sequent *s, DBM *lhs){
  for(DBMset::iterator it = s->ds.begin(); it != s->ds.end(); it++) {
    if (*(*it) >= *lhs) {
      return true;
    }
  }
  return false;
  
}


/** Using that a Sequent object is a set of sequents with matching rhs and
 *  discrete states with different clock states, determines if the specified
 * clock state is contained within one of the sequents. For performance
 * reasons, if the sequent is found in here, its placeholder is restricted
 * to be the largest placeholder possible.
 * This is used for known true sequents, since by definition
 * of sequents, if sequent B is true and A <= B (the right hand side matches
 * and the left hand state of A is a subset of the states in B), A is also true.
 * For this method, each B *(*it) is a known sequent 
 * and (lhs, lhsPlace) is the clock state
 * of A. This method assumes that the right hand side and discrete states match
 * (and is often called after locate_sequentPlace() or 
 * look_for_sequentPlace()); hence,
 * it only needs to compare clock states. 
 * @param s (*) The placeholder sequent that 
 * contains a set of (DBM, DBMList) pairs.
 * @param lhs (*) The DBM of the clock state to compare the sequent's DBMs to.
 * @param lhsPlace (*) The placeholder DBMList of the clock state.
 * @return true: (lhs, lhsPlace) <= some sequent in s 
 * (consequently, the sequent is true), false: otherwise.*/
bool tabled_sequentPlace(SequentPlace *s, DBM *lhs, DBMList * lhsPlace){
  for(DBMPlaceSet::iterator it = s->dsp.begin(); it != s->dsp.end(); it++) {
    if (*((*it).first) == *lhs) {
      // Since in the cache, we have the largest placeholder where this is true
      *lhsPlace & *((*it).second);
      lhsPlace->cf();
      return true;
    }
  }
  return false;
}

/** Using that a Sequent object is a set of sequents with matching rhs and
 *  discrete states with different clock states, determines if the specified
 * DBM is contains one of the sequents. This is used for known false
 * sequents, since by definition
 * of sequents, if sequent B is false and B <= A (the right hand side matches
 * and the left hand state of B is a subset of the states in A), A is false.
 * For this method, each B *(*it) is a known sequent and lhs is the clock state
 * of A. This method assumes that the right hand side and discrete states match
 * (and is often called after locate_sequent() or look_for_sequent()); hence,
 * it only needs to compare clock states. 
 * @param s (*) The sequent that contains a set of DBMs.
 * @param lhs (*) The DBM to compare the sequent's DBMs to.
 * @return true: lhs >= some sequent in s 
 * (consequently, the sequent is false), false: otherwise.*/
bool tabled_false_sequent(Sequent *s, DBM *lhs){
  for(DBMset::iterator it = s->ds.begin(); it != s->ds.end(); it++) {
    if (*(*it) <= *lhs) {
      return true;
    }
  }
  return false;
}

/** Using that a Sequent object is a set of sequents with matching rhs and
 *  discrete states with different clock states, determines if the specified
 * clock state contains one of the sequents. 
 * This is used for known false sequents, since by definition
 * of sequents, if sequent B is false and B <= A (the right hand side matches
 * and the left hand state of B is a subset of the states in A), A is false.
 * For this method, each B *(*it) is a known sequent 
 * and (lhs, lhsPlace) is the clock state
 * of A. This method assumes that the right hand side and discrete states match
 * (and is often called after locate_sequentPlace() or 
 * look_for_sequentPlace()); hence,
 * it only needs to compare clock states. 
 * @param s (*) The placeholder sequent that 
 * contains a set of (DBM, DBMList) pairs.
 * @param lhs (*) The DBM of the clock state to compare the sequent's DBMs to.
 * @param lhsPlace (*) The placeholder DBMList of the clock state.
 * @return true: (lhs, lhsPlace) >= some sequent in s 
 * (consequently, the sequent is false), false: otherwise.*/
bool tabled_false_sequentPlace(SequentPlace *s, DBM *lhs, DBMList * lhsPlace){
  for(DBMPlaceSet::iterator it = s->dsp.begin(); it != s->dsp.end(); it++) {
    // if (*((*it).first) == *lhs && *((*it).second) <= *lhsPlace) {
    if (*((*it).first) <= *lhs) {
      return true;
    }
  }
  return false;
}

/** Using that a Sequent object is a set of sequents with matching rhs and
 *  discrete states with different clock states, determines if the specified
 * DBM equals one of the sequents. This is used for least fixpoint
 * sequents and checks for sequent equality. For least fixpoint circularity,
 * if an equal sequent is found then this sequent is false.
 * This method assumes that the right hand side and discrete states match
 * (and is often called after locate_sequent() or look_for_sequent()); hence,
 * it only needs to compare clock states. 
 * @param s (*) The sequent that contains a set of DBMs.
 * @param lhs (*) The DBM to compare the sequent's DBMs to.
 * @return true: lhs == some sequent in s, false: otherwise.*/
bool tabled_sequent_lfp(Sequent *s, DBM *lhs){
  for(DBMset::iterator it = s->ds.begin(); it != s->ds.end(); it++) {
    if (*(*it) == *lhs) {
      return true;
    }
  }
  return false;
}

/** Using that a Sequent object is a set of sequents with matching rhs and
 *  discrete states with different clock states, determines if the specified
 * DBM equals one of the sequents. This is used for least fixpoint
 * sequents and checks for sequent equality. For least fixpoint circularity,
 * if an equal sequent is found then this sequent is false.
 * This method assumes that the right hand side and discrete states match
 * (and is often called after locate_sequentPlace() or 
 * look_for_sequentPlace()); hence,
 * it only needs to compare clock states. 
 * @param s (*) The placeholder sequent that 
 * contains a set of (DBM, DBMList) pairs.
 * @param lhs (*) The DBM of the clock state to compare the sequent's DBMs to.
 * @param lhsPlace (*) The placeholder DBMList of the clock state.
 * @return true: (lhs, lhsPlace) == some sequent in s, false: otherwise.*/
bool tabled_sequent_lfpPlace(SequentPlace *s, DBM *lhs, DBMList *lhsPlace){
  for(DBMPlaceSet::iterator it = s->dsp.begin(); it != s->dsp.end(); it++) {
    /* Extra work for placeholders. For now,
     * force equality on LHS sequent and use tabling logic
     * for placeholders. */
    if ( *(it->first) == *lhs && *(it->second) == *lhsPlace) {
      return true;
    }
  }
  return false;
}

/** Using that a Sequent object is a set of sequents with matching rhs and
 *  discrete states with different clock states, determines if the specified
 * clock state is contained within one of the sequents. 
 * This is used for greatest
 * fixpoint circularity, since by definition
 * of sequents, if sequent B is true and A <= B (the right hand side matches
 * and the left hand state of A is a subset of the states in B), A is also true.
 * For this method, each B *(*it) is a known sequent 
 * and (lhs, lhsPlace) is the clock state
 * of A. This method assumes that the right hand side and discrete states match
 * (and is often called after locate_sequentPlace() or 
 * look_for_sequentPlace()); hence,
 * it only needs to compare clock states. 
 * @param s (*) The placeholder sequent that 
 * contains a set of (DBM, DBMList) pairs.
 * @param lhs (*) The DBM of the clock state to compare the sequent's DBMs to.
 * @param lhsPlace (*) The placeholder DBMList of the clock state.
 * @return true: (lhs, lhsPlace) <= some sequent in s 
 * (consequently, the sequent is true), false: otherwise.*/
bool tabled_sequent_gfpPlace(SequentPlace *s, DBM *lhs, DBMList * lhsPlace){
  for(DBMPlaceSet::iterator it = s->dsp.begin(); it != s->dsp.end(); it++) {
    /* Extra work for placeholders. For now,
     * force equality on LHS sequent and use tabling logic
     * for placeholders. */
    if (*((*it).first) == *lhs && *((*it).second) >= *lhsPlace) {
      return true;
    }
  }
  return false;
}

/** Takes in set of known true sequents (s) with a newly 
 * established true clock state (lhs) and adds clock state (lhs)
 * to the set of sequents in s. In the update, the 
 * DBM lhs is copied. By definition, a sequent B is true
 * if and only if all of its states satisfy the right hand side. Hence,
 * if any known clock state is contained in lhs (B <= lhs),
 * we can enlarge that clock
 * state (enlarge B). This is more efficient (for searching) than just adding an
 * additional sequent.
 * @param s (*) The set of known sequents to update.
 * @param lhs (*) The DBM of the newly-established clock state.
 * @return true: the clock state was incorporated into one of s's
 * sequents; false: otherwise (a new sequent was added to s). */
bool update_sequent(Sequent *s, DBM *lhs){
  for(DBMset::iterator it = s->ds.begin(); it != s->ds.end(); it++) {
    if (*(*it) <= *lhs) { 
      *(*it) = *lhs; 
      return true; 
    }
  }
  DBM *m = new DBM(*lhs);
  s->ds.push_back(m);
  return false;
}

/** Takes in set of known true sequents (s) with a newly 
 * established true clock state (lhs, lhsPlace) and adds 
 * clock state (lhs, lhsPlace)
 * to the set of sequents in s. In the update, the 
 * DBM lhs and the DBMList lhsPlace are copied. 
 * By definition, a sequent B is true
 * if and only if all of its states satisfy the right hand side. Hence,
 * if any known clock state is contained in lhs (B <= lhs),
 * we can enlarge that clock
 * state (enlarge B). This is more efficient (for searching) than just adding an
 * additional sequent.
 * @param s (*) The set of known placeholder sequents to update.
 * @param lhs (*) The DBM of the newly-established clock state.
 * @param lhsPlace (*) The DBMList of the newly-established clock state.
 * @return true: the clock state was incorporated into one of s's
 * sequents; false: otherwise (a new sequent was added to s). */
bool update_sequentPlace(SequentPlace *s, DBM *lhs, DBMList *lhsPlace){
  for(DBMPlaceSet::iterator it = s->dsp.begin(); it != s->dsp.end(); it++) {
    /* Extra work for placeholders. For now,
     * force equality on LHS sequent and use tabling logic
     * for placeholders. */
    if (*((*it).first) == *lhs && *((*it).second) <= *lhsPlace) {
      *((*it).second) = *lhsPlace; 
      return true; 
    }
  }
  DBM *m = new DBM(*lhs);
  DBMList *mp = new DBMList(*lhsPlace);
  pair <DBM *, DBMList *> p (m, mp);
  s->dsp.push_back(p);
  return false;
}

/** Takes in set of known false sequents (s) with a newly 
 * established false clock state (lhs) and adds clock state (lhs)
 * to the set of sequents in s. In the update, the 
 * DBM lhs is copied. By definition, a sequent B is false
 * if and only if it has a clocks state that does not satisfy the right
 * side. Hence,
 * if any known clock state is contains (B >= lhs),
 * we can refine that clock
 * state (shrink B). This is more efficient (for searching) than just adding an
 * additional sequent.
 * @param s (*) The set of known sequents to update.
 * @param lhs (*) The DBM of the newly-established clock state.
 * @return true: the clock state was incorporated into one of s's
 * sequents; false: otherwise (a new sequent was added to s). */
bool update_false_sequent(Sequent *s, DBM *lhs){
  for(DBMset::iterator it = s->ds.begin(); it != s->ds.end(); it++) {
    if (*(*it) >= *lhs) { 
      *(*it) = *lhs; 
      return true; 
    }
  }
  DBM *m = new DBM(*lhs);
  s->ds.push_back(m);
  return false;
}

/** Takes in set of known false sequents (s) with a newly 
 * established false clock state (lhs, lhsPlace) and adds 
 * clock state (lhs, lhsPlace)
 * to the set of sequents in s. In the update, the 
 * DBM lhs and the DBMList lhsPlace are copied. 
 * By definition, a sequent B is false
 * if and only if it has a clocks state that does not satisfy the right
 * side. Hence,
 * if any known clock state is contains (B >= lhs),
 * we can refine that clock
 * state (shrink B). This is more efficient (for searching) than just adding an
 * additional sequent.
 * @param s (*) The set of known placeholder sequents to update.
 * @param lhs (*) The DBM of the newly-established clock state.
 * @param lhsPlace (*) The DBMList of the newly-established clock state.
 * @return true: the clock state was incorporated into one of s's
 * sequents; false: otherwise (a new sequent was added to s). */
bool update_false_sequentPlace(SequentPlace *s, DBM *lhs, DBMList *lhsPlace){
  for(DBMPlaceSet::iterator it = s->dsp.begin(); it != s->dsp.end(); it++) {
    if (*((*it).first) >= *lhs) {
      *((*it).first) = *lhs; 
      return true;
    }
  }
  DBM *m = new DBM(*lhs);
  /* I would like this to be NULL, but it is checked in the program */
  DBMList *mp = new DBMList(*EMPTY);
  pair <DBM *, DBMList *> p (m,mp);
  s->dsp.push_back(p);
  return false;
}


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
bool look_for_and_purge_rhs_backStack(vector<Sequent *> * initialPtr, vector<SequentPlace *> * initialPlacePtr) 
{
  bool madeChange = false;
  
  /* Store a vector of stateBackList, where each sequent only has one DBM */
  
  /* Now iterate until the vector sequentQueue is empty,
   * purging backpointers and adding relevant ones in the queue */
  /* For now, implement purging with deques instead of vectors */
  deque <Sequent *> purgeSeqQueue(initialPtr->begin(), initialPtr->end());
  deque <SequentPlace *> purgeSeqPlaceQueue(initialPlacePtr->begin(), initialPlacePtr->end());
  
  while(!(purgeSeqPlaceQueue.empty())) {
    
    
    SequentPlace * tp = purgeSeqPlaceQueue.front();
    int pInd; 
    bool b2 = false;
    bool b2b = false;

    pInd = (lookup_predicate(tp->rhs()->getPredicate()))->getIntVal() - 1;
    /* Note: Purging parent sequents still ignores clock states. */
    
    /* Now purge the sequent and the DBM from all lists.
     * Circularity caches are correctly maintained; therefore,
     * they are not purged. */
    
    /* If found, Purge Sequent from its cache */
    b2 = look_for_and_purge_rhs_sequentPlace_state(tp, Xlist_false_ph, pInd, false);
    
    b2b = look_for_and_purge_rhs_sequentPlace_state(tp, Xlist_true_ph, pInd, false);
   
    /* Now find its backpointers to add to the queue 
     * Only add backpointers to queue if something is purged. */
    if( b2 || b2b) {
      madeChange = true;
      // Now add sequents
      for(vector<Sequent *>::iterator it = tp->parSequent.begin(); 
      it != tp->parSequent.end(); it++) {
        purgeSeqQueue.push_back(*it);  
        
      } 
      for(vector<SequentPlace *>::iterator it = tp->parSequentPlace.begin(); 
      it != tp->parSequentPlace.end(); it++) {
        purgeSeqPlaceQueue.push_back(*it);  
        
      } 
    }
    
    purgeSeqPlaceQueue.pop_front();
    

  }
  
  /* Now purge the original Sequents */
  while(!(purgeSeqQueue.empty())) {
    
    Sequent * t = purgeSeqQueue.front();
    int pInd; 
    bool b1 = false;
    bool b1b = false;
    
    pInd = (lookup_predicate(t->rhs()->getPredicate()))->getIntVal() - 1;
    /* Note: Purging parent sequents still ignores clock states */
  
    /* Now purge the sequent and the DBM from all lists.
     * Circularity caches are correctly maintained; therefore,
     * they are not purged. */
    b1 = look_for_and_purge_rhs_sequent_state(t, Xlist_false, pInd, false);
    
    /* If found, Purge Sequent from its cache */
    b1b = look_for_and_purge_rhs_sequent_state(t, Xlist_true, pInd, false);
    
    /* Now find its backpointers to add to the queue 
     * Only add backpointers to queue if something is purged. */
    if(b1 || b1b) {
      madeChange = true;
      // Now add sequents
      for(vector<Sequent *>::iterator it = t->parSequent.begin(); 
      it != t->parSequent.end(); it++) {
        purgeSeqQueue.push_back(*it);  
        
      } 
      for(vector<SequentPlace *>::iterator it = t->parSequentPlace.begin(); 
      it != t->parSequentPlace.end(); it++) {
        purgeSeqPlaceQueue.push_back(*it);  
        
      } 
    }

    purgeSeqQueue.pop_front();

  }
  // For now, do not remove backpointers from backList
  // This may be too conservative.
  
  return madeChange;

}

/** Method to compute the predecessor check of reativized exists operators.
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
inline DBMList * predCheckRule(DBM * lhs, DBM * lhsSucc, DBMList * origPlace, DBMList * phi1Place, 
  DBMList * phi2Place, DBMList * phi2PredPlace ) {
  
  retPlaceDBM->makeEmpty();
  /* Iterate through each DBM of phi2Place and union the results. */
  vector<DBM *> * phi2PlaceList = phi2Place->getDBMList();
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
 * @param (*) lhs the reference to the left hand sequent
 * @param (*) currPlace the reference to the current placeholder.
 * @return the tightened placeholder that satisfies the succCheck, or an
 * empty placeholder if no such placeholder is possible. */
inline DBMList * succCheckRule(DBM * lhs, DBMList * currPlace) {
    
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
DBMList * do_proof_place(int step, DBM *lhs, DBMList * place, ExprNode *rhs, SubstList *sub)
{	
	/* do_proof_place() written by Peter Fontana, needed for support
	 * of EXISTS Quantifiers. */    
	bool retVal = false; 
	
  #if DEBUG	   
  if (debug) {
    lhs->cf();
    place->cf();
    print_sequent_place(step, retVal, lhs, place, rhs, sub, rhs->getOpType());
  }
  #endif
  step++;
  
  switch(rhs->getOpType()){
    case PREDICATE:{
      
      ExprNode *e = lookup_equation(rhs->getPredicate());
      if (e == NULL){
        cerr << "open predicate variable found: "<< rhs->getPredicate()<<endl;
        exit(-1); 
      }
      
      // Get Predicate Index for Hashing
      int pInd = (lookup_predicate(rhs->getPredicate()))->getIntVal() - 1;
      
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
        SequentPlace *hf = look_for_sequentPlace(place, tf->sub(), Xlist_false_ph, pInd);
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
        SequentPlace *hfb = look_for_sequentPlace(place, tfb->sub(), Xlist_true_ph, pInd);
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
				h = locate_sequentPlace(t, Xlist_pGFP_ph, pInd);
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
            SequentPlace *h7 = locate_sequentPlace(t7, Xlist_true_ph, pInd);
            update_sequentPlace(h7, lhs, place);
          }
					break;
				} 
				
				
        pair <DBM *, DBMList *> p (new DBM(*lhs),new DBMList(*place));
        h->dsp.push_back(p);
      }
      else { // Thus, a least fixpoint
				// Now look in lfp circularity cache
        h = locate_sequentPlace(t, Xlist_pLFP_ph, pInd);
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
            SequentPlace *h7 = locate_sequentPlace(t7, Xlist_false_ph, pInd);
            update_false_sequentPlace(h7, lhs, place);
          }
					break;
				} 
				
        pair <DBM *, DBMList *> p (new DBM(*lhs), new DBMList(*place));
        h->dsp.push_back(p);
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
      
      pair <DBM *, DBMList *> tempP = h->dsp.back();
      DBM * tempF = tempP.first;
      delete tempF;
      DBMList * tempS = tempP.second;
      delete tempS;
      h->dsp.pop_back();
      // dsp might be empty, but we leave it in

			
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
        t2s = look_for_and_purge_rhs_sequentPlace(lhs, retPlaceDBM, t2c, Xlist_false_ph, pInd, false, &madeEmpty);
      
        
        /* Now purge backpointers */
        if(t2s != NULL) {           
          look_for_and_purge_rhs_backStack(&(t2s->parSequent),
                                           &(t2s->parSequentPlace));
          // Delete t2s later to prevent double deletion
          
        }
        // Now update in proper Cache
        SequentPlace *t5 = new SequentPlace(rhs, sub);
        SequentPlace *h5 = locate_sequentPlace(t5, Xlist_true_ph, pInd);
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
        t2bs = look_for_and_purge_rhs_sequentPlace(lhs, retPlaceDBM, t2b2, Xlist_true_ph, pInd, true, &madeEmpty);
          
        
        /* Now purge backpointers. 
         * Ignore circularity booleans because they do not form backpointers */
        if(t2bs != NULL) {
          look_for_and_purge_rhs_backStack(&(t2bs->parSequent),
                                           &(t2bs->parSequentPlace));
          // delete t2bs later to prevent double deletion.
        }
        // Now update in proper Cache
        SequentPlace *t5 = new SequentPlace(rhs, sub);
        SequentPlace *h5 = locate_sequentPlace(t5, Xlist_false_ph, pInd);
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
				DBMList * tempDBM2 = new DBMList(*retPlaceDBM);
        retPlaceDBM = do_proof_place(step, lhs, &tPlace, rhs->getRight(), sub);
        *retPlaceDBM & *tempDBM2;
        delete tempDBM2;
        
			}
      break;}
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
      DBMList * leftPlace = new DBMList(*retPlaceDBM);
      retPlaceDBM = do_proof_place(step, lhs, &placeB, rhs->getRight(), sub);
      retPlaceDBM->cf();
      
      #if DEBUG
      if(debug) {
        // Check Debugging Here to make sure it is giving the right output
        print_sequentCheck(step - 1, retVal, lhs, place, sub, rhs->getOpType());
        cout << "Left Placeholder of OR (P): ";
        leftPlace->print_constraint();
        cout << "\nRight Placeholder of OR (P): ";
        retPlaceDBM->print_constraint();
        cout << endl;
      }
      #endif
      
      /* Note: <= >= Not clearly working if empty DBMs */
      if(emptyLeft) { // we already checked the emptiness of the previous DBM
        // Do Nothing
      }
      else if(retPlaceDBM->emptiness()) {
        // Take previous DBM
        *retPlaceDBM = (*leftPlace);
      }
      else if((*leftPlace) <= (*retPlaceDBM)) {
        // do nothing
        
      }
      else if (*retPlaceDBM <= *leftPlace) {
        *retPlaceDBM = (*leftPlace);
        retVal = retPlaceDBM->emptiness();
      }
      else { /* Corner Case: make DBM Union*/
        retPlaceDBM->addDBMList(*leftPlace);
        retPlaceDBM->cf();
      }
      retVal = !(retPlaceDBM->emptiness());
      
      #if DEBUG
      if(debug) {
        cout << "Final Placeholder of OR (P): ";
        retPlaceDBM->print_constraint();
        cout << endl << endl;
      }
      #endif
      
      delete leftPlace;
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
      DBMList * leftPlace = new DBMList(*retPlaceDBM);
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
        *retPlaceDBM = (*leftPlace);
      }
      /* If neither the if or the else if clauses were taken,
       * then both are non-empty and the left is not the
       * entire placeholder. Hence, the left was not the simple
       * disjunct. Therefore, the right must be the simple disjunct
       * and must be the entire placeholder. */
        
      retVal = !(retPlaceDBM->emptiness());
      delete leftPlace;
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
      
      DBMList *tPlace = new DBMList(*INFTYDBM);
      
      retPlaceDBM = do_proof_place(step, &ph, tPlace, rhs->getQuant(), sub);
      retPlaceDBM->cf();
      //must we consider not the invariant even if the placeholder is empty. (?)
      if(!(retPlaceDBM->emptiness())) { // Only do if a nonempty placeholder
        /* Now do the second proof rule to compute the first placeholder
				 */
			
			  /* Note; we union retPlaceDBM with the complement of the invariant.
			   * should we do this if retPlaceDBM is nonempty? */
			  DBMList invCompPlace(*INFTYDBM);
			  bool hasInv = invs_chk(&invCompPlace, sub);
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
					print_sequentCheck(step - 1, retVal, &succLHS, &succRuleConseq, sub, rhs->getOpType());
					if(retVal) {
						cout <<"----(Valid) Placeholder Check Passed-----" << endl
            <<"--With Placeholder := {";
						retPlaceDBM->print_constraint();
						cout <<"} ----" << endl << endl;
					}
					else {
						cout <<"----(Invalid) Placeholder Check Failed-----" << endl << endl;
            
					}
				}
        #endif
        
      }
      delete tPlace;
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
			invs_chk(tPlace, sub); 
      retPlaceDBM = do_proof_place(step, &ph, tPlace, 		
                                       rhs->getLeft(), sub);
      retPlaceDBM->cf();
      if(retPlaceDBM->emptiness()){
        if (debug) { 
				  print_sequentCheck(step - 1, retVal, &ph, retPlaceDBM, sub, rhs->getOpType());
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
    
        DBMList *newPlace = new DBMList(*INFTYDBM);
        retPlaceDBM = do_proof_place(step, &ph, newPlace, rhs->getRight(), sub);
        retPlaceDBM->cf();
        if(!(retPlaceDBM->emptiness())){ // Only do if a nonempty placeholder
          /* Now do the second proof rule to compute the first placeholder
           */
       
          DBMList invCompPlace(*INFTYDBM);
          bool hasInv = invs_chk(&invCompPlace, sub);
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
            print_sequentCheck(step - 1, retVal, &succLHS, &succRuleConseq, sub, rhs->getOpType());
            if(retVal) {
              cout <<"----(Valid) FORALL (FORALL_REL) Placeholder Check Passed-----" << endl
              <<"--With Placeholder := {";
              retPlaceDBM->print_constraint();
              cout <<"} ----" << endl << endl;
            }
            else {
              cout <<"----(Invalid) FORALL (FORALL_REL) Placeholder Check Failed-----" << endl << endl;
          
            }
          }
          #endif
        }
        delete newPlace;
      }
      else {
        // First check for the simplest case: no time elapse is needed
        /* Perhaps we can reduce *INFTYDBM to be *place 
         * given the proof rules. */
        if((*retPlaceDBM) == (*INFTYDBM)) {
          #if DEBUG	  
          if (debug) { 
            print_sequentCheck(step - 1, retVal, lhs, retPlaceDBM, sub, rhs->getOpType());
            cout <<"----(Valid) EXISTS (in FORALL_REL) Placeholder indicates no time elapse is needed (Check Only)-----" << endl
            << "----With Placeholder := {";
            retPlaceDBM->print_constraint();
            cout << "} ----"<< endl << endl;
          
          }
          #endif
          
          // If here, we neither need a placeholder nor to elapse time
          DBM phb(*lhs);
          DBMList *infPlace = new DBMList(*INFTYDBM);
          retPlaceDBM = do_proof_place(step, &phb, infPlace, rhs->getRight(), sub);
          retPlaceDBM->cf();
          if(!(retPlaceDBM->emptiness())){ // Only do if a nonempty placeholder
            /* Now do the second proof rule to compute the first placeholder */
            
         
           // No Successor Check required since this is for no time elapse
            infPlace->cf();
            *infPlace & *retPlaceDBM;
            infPlace->cf();
            /* Now do the containment check 
             * and use to compute the value of the place holder *place */
            if(!(infPlace->emptiness())){
              retVal = true;
              *retPlaceDBM = (*infPlace);
            }
            else {/* proof is false */
              retVal = false;
              retPlaceDBM->makeEmpty();
            }
            #if DEBUG	  
            if (debug) {
              print_sequentCheck(step - 1, retVal, &phb, infPlace, sub, rhs->getOpType());
              if(retVal) {
                cout <<"----(Valid) Placeholder Check Passed-----" << endl
                <<"--With Placeholder := {";
                retPlaceDBM->print_constraint();
                cout <<"} ----" << endl << endl;
              }
              else {
                cout <<"----(Invalid) Placeholder Check Failed-----" << endl << endl;
            
              }
            }
            #endif
          }
          delete infPlace;
          
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
            phi1Place.print_constraint();
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
            phi2Place.print_constraint();
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
            bool hasInv = invs_chk(&invCompPlace, sub);
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
              print_sequentCheck(step - 1, retVal, &phb, fPlace, sub, rhs->getOpType());
                cout <<"----() FORALL (of FORALL_REL) Placeholder Check obtained  FA Placeholder := {";
                forallPlace.print_constraint();
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
              cout <<"----() FORALL Rel Exists placeholder obtained as := {";
              retPlaceDBM->print_constraint();
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
              print_sequentCheck(step - 1, retVal, lhs, retPlaceDBM, sub, rhs->getOpType());
              
                cout <<"----() FORALL Rel Exists placeholder after time elapse check is := {";
                retPlaceDBM->print_constraint();
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
      
            delete phi1PredPlace;
          }
          #if DEBUG
          if(debug) {
            cout << "Final Placeholder of FORALL_REL (P): ";
            retPlaceDBM->print_constraint();
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
      DBMList * tPlace = new DBMList(*INFTYDBM);
			invs_chk(tPlace, sub); 
			
			//DBMList * tempPlace = new DBMList(*retPlaceDBM);
      retPlaceDBM = do_proof_place(step, &ph, tPlace, 		
                                       rhs->getQuant(), sub);
      retPlaceDBM->cf();
      if(retPlaceDBM->emptiness()){
         if (debug) { 
				  print_sequentCheck(step - 1, retVal, &ph, retPlaceDBM, sub, rhs->getOpType());
				
				  cout <<"----(Invalid) Empty First Placeholder: No Need for additional Placeholder Checks-----" << endl << endl;
        }
        retVal = false;
        delete tPlace;
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
				print_sequent_placeCheck(step - 1, retVal, lhs, place, retPlaceDBM, sub, rhs->getOpType());
				if(retVal) {
					cout <<"----(Valid) Placeholder Check Passed-----" << endl
          <<"--With Placeholder := {";
					retPlaceDBM->print_constraint();
					cout <<"} ----" << endl << endl;
				}
				else {
					cout <<"----(Invalid) Placeholder Check Failed-----" << endl << endl;
          
				}
      }
      #endif
      delete tPlace;
  
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
			invs_chk(tPlace, sub); 
			
      retPlaceDBM = do_proof_place(step, &ph, tPlace, 		
                                       rhs->getRight(), sub);
      // Reset place parent to NULL
      parentPlaceRef = NULL;
      retPlaceDBM->cf();
      if(retPlaceDBM->emptiness()){
        retVal = false;
        if (debug) { 
				  print_sequentCheck(step - 1, retVal, lhs, retPlaceDBM, sub, rhs->getOpType());
				
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
          phi1Place.print_constraint();
          cout << "} ----"<< endl << endl;
      }
      #endif
      *retPlaceDBM & *phi2PredPlace;
      retPlaceDBM->cf();
      if(retPlaceDBM->emptiness()) {
        retVal = false;
        #if DEBUG
        if(debug) {
          print_sequentCheck(step - 1, retVal, &phb, retPlaceDBM, sub, rhs->getOpType());
				
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
              phi2Place->print_constraint();
              cout << "} ----"<< endl << endl;
            }
            else {
              cout <<"----(Invalid) While Time Elapse not required, placeholder is not large enough-----" << endl
              << "----With resulting Placeholder := {";
              phi2Place->print_constraint();
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
          retPlaceDBM->print_constraint();
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
        print_sequent_place(step - 1,  retVal, &phb, phi2PredPlace, rhs->getLeft(), sub, rhs->getOpType()); 
        cout <<"----(Valid) Relativization Placeholder Check Passed (Check Only)-----" << endl
          << "----With resulting Placeholder := {";
          retPlaceDBM->print_constraint();
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
				print_sequent_placeCheck(step - 1, retVal, lhs, place, retPlaceDBM, sub, rhs->getOpType());
				if(retVal) {
					cout <<"----(Valid) Final Placeholder Check Passed-----" << endl
          <<"--With Placeholder := {";
					retPlaceDBM->print_constraint();
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
      for(vector<Transition *>::iterator it = transList->begin();
        it != transList->end(); it++ ) {
        Transition * tempT = *it;
        
        /* Obtain the entire ExprNode and prove it */
        DBM tempLHS(*lhs);
        
        DBMList guardPlace(*place);
        bool tempBool = comp_ph_all_place(&tempLHS, &guardPlace, tempT->getLeftExpr(), sub);
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
        SubstList * sl = tempT->getEnteringLocation(&tSub);
        bool isInv = invs_chk(&invPlace, sl);
        delete sl;
        if(isInv) {
          invPlace.cf();
          ClockSet * st = tempT->getCSet();
          if(st != NULL) {
            invPlace.preset(st);
          }
          invPlace.cf();
          /* Now perform clock assignments sequentially: perform the
           * front assignments first */
          vector<pair<short int, short int> > * av = tempT->getAssignmentVector();
          if(av != NULL) {
            // Iterate over the vector and print it
            for(vector<pair<short int, short int> >::iterator it=av->begin(); it != av->end(); it++) {
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
                invPlace.print_constraint();
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
        retPlaceDBM->print_constraint(); 
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
      for(vector<Transition *>::iterator it = transList->begin();
        it != transList->end(); it++ ) {
        Transition * tempT = *it;
        
        /* Obtain the entire ExprNode and prove it */

        DBMList tempPlace(*place);
        DBM tempLHS(*lhs);
        // Method tightens lhs and place
        bool tempBool = comp_ph_exist_place(&tempLHS, &tempPlace, tempT->getLeftExpr(), sub);
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
        SubstList * sl = tempT->getEnteringLocation(&tSub);
        bool isInv = invs_chk(&invCons, sl);
        delete sl;
        if(isInv) {
          invCons.cf();
          ClockSet * st = tempT->getCSet();
          if(st != NULL) {
            invCons.preset(st);
          }
          invCons.cf();
          /* Now perform clock assignments sequentially: perform the
           * front assignments first */
          vector<pair<short int, short int> > * av = tempT->getAssignmentVector();
          if(av != NULL) {
            // Iterate over the vector and print it
            for(vector<pair<short int, short int> >::iterator it=av->begin(); it != av->end(); it++) {
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
                invCons.print_constraint();
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
          invCons.print_constraint();
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
        retPlaceDBM->print_constraint();
        cout << endl;
      }
      #endif
      break;
    }
    case IMPLY:{
      DBM tempLHS(*lhs);
      /* call comp_ph() for efficient proving of IMPLY's left. */
      if(comp_ph(&tempLHS, rhs->getLeft(), sub)){
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
          retPlaceDBM->print_constraint(); 
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
          retPlaceDBM->print_constraint(); 
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
      retVal = (sub->operator[](rhs->getAtomic()) == rhs->getIntVal());
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
      retVal = (sub->operator[](rhs->getAtomic()) != rhs->getIntVal());
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
      retVal = (sub->operator[](rhs->getAtomic()) < rhs->getIntVal());
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
      retVal = (sub->operator[](rhs->getAtomic()) > rhs->getIntVal());
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
      retVal = (sub->operator[](rhs->getAtomic()) <= rhs->getIntVal());
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
      retVal = (sub->operator[](rhs->getAtomic()) >= rhs->getIntVal());
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
      SubstList *st = new SubstList(rhs->getSublist(), sub );
      retPlaceDBM = do_proof_place(step, lhs, place, rhs->getExpr(), st);
      delete st;
      break;}
    case RESET:{
      // Bound the LHS to prevent infinite proofs
      lhs->cf();
			lhs->bound(MAXC);  
      lhs->cf();
      DBM ph(*lhs);
      ClockSet *rs = rhs->getClockSet();
      ph.reset(rs);
      
      DBMList * tPlace = new DBMList(*INFTYDBM);
      retPlaceDBM = do_proof_place(step, &ph, tPlace, rhs->getExpr(), sub);
      delete tPlace;
      retPlaceDBM->cf();
      if(!(retPlaceDBM->emptiness())) {
				/* Now do the check that the new placeholder follows from 
				 * the previous placeholder. by setting it to such */
				DBMList p2Copy(*retPlaceDBM);
				// Apply the reset (weakest precondition operator)
				ClockSet *rsb = rhs->getClockSet();
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
					print_sequent_placeCheck(step - 1, retVal, lhs, retPlaceDBM, &p2Copy, sub, rhs->getOpType());
					if(retVal) {
						cout <<"----(Valid) Placeholder Check Passed-----" << endl
            <<"--With Placeholder := {";
						retPlaceDBM->print_constraint();
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
      DBMList * placeB = new DBMList(*INFTYDBM);
      retPlaceDBM = do_proof_place(step, &ph, placeB, rhs->getExpr(), sub);
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
					print_sequent_placeCheck(step - 1, retVal, lhs, place, &tmp2, sub, rhs->getOpType());
					if(retVal) {
						cout <<"----(Valid) Placeholder Check Passed-----" << endl
            <<"--With Placeholder := {";
						retPlaceDBM->print_constraint();
						cout <<"} ----" << endl << endl;
					}
					else {
						cout <<"----(Invalid) Placeholder Check Failed-----" << endl << endl;
            
					}
				}
        #endif
        delete placeB;
			}
      break; }
    case REPLACE:{
      sub->operator[](rhs->getcX()) = sub->operator[](rhs->getcY());
      retPlaceDBM = do_proof_place(step, lhs, place, rhs->getExpr(), sub);
      break; }
    case ABLEWAITINF:{
      lhs->cf();
      DBMList ph(*lhs);
      ph & *place;
      ph.cf();
      ph.suc();
      invs_chk(&ph, sub);
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
      invs_chk(&ph, sub);
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
bool do_proof(int step, DBM *lhs, ExprNode *rhs, SubstList *sub)
{
  bool retVal = false; 
  #if DEBUG	   
  if (debug){ 
    lhs->cf();
    print_sequent(step, retVal, lhs, rhs, sub, rhs->getOpType());
  }
  #endif
  step++;
  
  switch(rhs->getOpType()){
    case PREDICATE:{
      
      ExprNode *e = lookup_equation(rhs->getPredicate());
      if (e == NULL){
        cerr << "open predicate variable found: "<< rhs->getPredicate()<<endl;
        exit(-1); 
      }
      
      // Get Predicate Index for Hashing
      int pInd = (lookup_predicate(rhs->getPredicate()))->getIntVal() - 1;
      prevParityGfp = currParityGfp;
      currParityGfp = rhs->get_Parity();
      lhs->cf();
      
      /* Look in Known True and Known False Sequent Caches */
      /* First look in known False Sequent table */
      if(useCaching) {
        Sequent *tf = new Sequent(rhs, sub);
        Sequent *hf = look_for_sequent(tf->sub(), Xlist_false, pInd);
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
          break;
        } 
        if(tf != hf) {
          delete tf;
        }
      }
      
      /* Now look in known True Sequent table */
      if(useCaching) {
        Sequent *tfb = new Sequent(rhs, sub);
        Sequent *hfb = look_for_sequent(tfb->sub(), Xlist_true, pInd);
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
          break;
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
				h = locate_sequent(t, Xlist_pGFP, pInd);
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
            Sequent *h7 = locate_sequent(t7, Xlist_true, pInd);
            update_sequent(h7, lhs);
          }
					break;
				} 
				
        h->ds.push_back(new DBM(*lhs));
      }
      else { // Thus, a least fixpoint
				// Now look for a Circularity
        h = locate_sequent(t, Xlist_pLFP, pInd);
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
            Sequent *h7 = locate_sequent(t7, Xlist_false, pInd);
            update_false_sequent(h7, lhs);
          }
					break;
				} 
				
        h->ds.push_back(new DBM(*lhs));
      }
      
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
        t2s = look_for_and_purge_rhs_sequent(lhs, t2, Xlist_false, pInd, false, &madeEmpty);
        
        
        /* Now purge backpointers */
        if(t2s != NULL) {
            look_for_and_purge_rhs_backStack(&(t2s->parSequent),
                                             &(t2s->parSequentPlace));
          
        }
        // Now update in proper Cache
        Sequent *t5 = new Sequent(rhs, sub);
        Sequent *h5 = locate_sequent(t5, Xlist_true, pInd);
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
        t22s = look_for_and_purge_rhs_sequent(lhs, t22, Xlist_true, pInd, true, &madeEmpty);

        
        /* Now purge backpointers. 
         * Ignore circularity booleans because they do not form backpointers */
        if(t22s != NULL) {
           
          look_for_and_purge_rhs_backStack(&(t22s->parSequent),
                                           &(t22s->parSequentPlace));
           
        }
        // Now update in proper Cache
        Sequent *t5 = new Sequent(rhs, sub);
        Sequent *h5 = locate_sequent(t5, Xlist_false, pInd);
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

      break; 
    }
    case AND:{
      /* Because lhs is only changed after it is copied, it can
       * be passed to both branches. */
      retVal = do_proof(step, lhs, rhs->getLeft(), sub);
			if(retVal == true) {
        retVal = do_proof(step, lhs, rhs->getRight(), sub);
			}
      break;}
    case OR:{
      /* Use two placeholders to provide split here */
      DBMList * place1 = new DBMList(*INFTYDBM);
      retPlaceDBM = do_proof_place(step, lhs, place1, rhs->getLeft(), sub);
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
        *place1 = *retPlaceDBM;
        DBMList * place2 = new DBMList(*INFTYDBM);
        retPlaceDBM = do_proof_place(step, lhs, place2, rhs->getRight(), sub);
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
          retPlaceDBM->addDBMList(*place1);
          retVal = (*retPlaceDBM) >= *lhs;
        }
       
        delete place2; 
      }
      delete place1; 
      break;}
    case OR_SIMPLE:{
      /* Simplified OR does not need to split on placeholders */
      retVal = do_proof(step, lhs, rhs->getLeft(), sub);
      // Reset place parent to NULL
      if(!retVal) {
        DBM lhsb(*lhs);
        retVal  = do_proof(step, &lhsb, rhs->getRight(), sub);
      }
      break;}
    case FORALL:{
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
      invs_chk(&ph, sub); 
      
      retVal = do_proof(step, &ph, rhs->getQuant(), sub);
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
      lhs->cf();
      DBM ph(*lhs);
      ph.suc();
      
      DBMList * tPlace = new DBMList(*INFTYDBM);
      invs_chk(tPlace, sub); 
      retPlaceDBM = do_proof_place(step, &ph, tPlace, 		
                                       rhs->getLeft(), sub);
      // Reset place parent to NULL
      parentPlaceRef = NULL;
      retPlaceDBM->cf();
      if(retPlaceDBM->emptiness()){
        if (debug) { 
				  print_sequentCheck(step - 1, retVal, lhs, retPlaceDBM, sub, rhs->getOpType());
				
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
        invs_chk(&ph, sub); 
      
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
            print_sequentCheck(step - 1, retVal, lhs, retPlaceDBM, sub, rhs->getOpType());
            cout <<"----(Valid) Placeholder indicates no time elapse is needed (Check Only)-----" << endl
            << "----With Placeholder := {";
            retPlaceDBM->print_constraint();
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
            phi1Place.print_constraint();
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
            phi2Place.print_constraint();
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
            bool hasInv = invs_chk(&invCompPlace, sub);
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
              print_sequentCheck(step - 1, retVal, &phb, fPlace, sub, rhs->getOpType());
                cout <<"----() FORALL (of FORALL_REL) Placeholder Check obtained  FA Placeholder := {";
                forallPlace.print_constraint();
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
              retPlaceDBM->print_constraint();
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
              print_sequentCheck(step - 1, retVal, lhs, retPlaceDBM, sub, rhs->getOpType());
              
                cout <<"----() FORALL Rel Exists placeholder after time elapse check is := {";
                retPlaceDBM->print_constraint();
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
            print_sequentCheck(step - 1, retVal, lhs, retPlaceDBM, sub, rhs->getOpType());
              cout <<"----() Final FORALL REL Placeholder is := {";
              retPlaceDBM->print_constraint();
              cout << "} ----"<< endl << endl;
            }
            #endif
            delete phi1PredPlace;
          }
          delete fPlace;
          
        }
        delete tPlace;
        
      }
      break;
    }
    case EXISTS:{
      
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
      DBMList * tPlace = new DBMList(*INFTYDBM);
			invs_chk(tPlace, sub); 
			
      retPlaceDBM = do_proof_place(step, &ph, tPlace, 		
                                       rhs->getQuant(), sub);
      // Reset place parent to NULL
      parentPlaceRef = NULL;
      retPlaceDBM->cf();
      if(retPlaceDBM->emptiness()){
        retVal = false;
        if (debug) { 
				  print_sequentCheck(step - 1, retVal, lhs, retPlaceDBM, sub, rhs->getOpType());
				
				  cout <<"----(Invalid) Empty Placeholder: No Need for Placeholder Check-----" << endl << endl;
        }
        delete tPlace;
        break;
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
				print_sequentCheck(step - 1, retVal, lhs, retPlaceDBM, sub, rhs->getOpType());
				if(retVal) {
					cout <<"----(Valid) Placeholder Check Passed (Check Only)-----" << endl
          << "----With Placeholder := {";
          retPlaceDBM->print_constraint();
          cout << "} ----"<< endl << endl;
          
				}
				else {
					cout <<"----(Invalid) Placeholder Check Failed-----" << endl << endl;
          
				}
      }
      #endif
      delete tPlace;
      
      break;
    }
    case EXISTS_REL: {
      /* First Try to get a placeholder value that works */
      lhs->cf();
      DBM ph(*lhs);
      // Note: lhs is unchanged
      ph.suc(); 
      DBM phb(ph);
      
      DBMList * tPlace = new DBMList(*INFTYDBM);
			invs_chk(tPlace, sub); 
			
      retPlaceDBM = do_proof_place(step, &ph, tPlace, 		
                                       rhs->getRight(), sub);
      // Reset place parent to NULL
      parentPlaceRef = NULL;
      retPlaceDBM->cf();
      if(retPlaceDBM->emptiness()){
        retVal = false;
        if (debug) { 
				  print_sequentCheck(step - 1, retVal, lhs, retPlaceDBM, sub, rhs->getOpType());
				
				  cout <<"----(Invalid) Empty First Placeholder: No Need for additional Placeholder Checks-----" << endl << endl;
        }
        //delete retPlace;
        delete tPlace;
        break;
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
          phi1Place.print_constraint();
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
          print_sequentCheck(step - 1, retVal, &phb, retPlaceDBM, sub, rhs->getOpType());
				
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
              phi2Place->print_constraint();
              cout << "} ----"<< endl << endl;
            }
            else {
              cout <<"----(Invalid) While Time Elapse not required, placeholder is not large enough-----" << endl
              << "----With resulting Placeholder := {";
              phi2Place->print_constraint();
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
          retPlaceDBM->print_constraint();
          cout << "} ----"<< endl << endl;
        }
        #endif
        delete phi2Place;
        delete phi2PredPlace;
        delete tPlace;
        break;
      }
        // if it is nonempty, it passes the second check and we continue
       
      
      
      #if DEBUG
      if(debug) {
        print_sequent_place(step - 1,  retVal, &phb, phi2PredPlace, rhs->getLeft(), sub, rhs->getOpType()); 
        cout <<"----(Valid) Relativization Placeholder Check Passed (Check Only)-----" << endl
          << "----With resulting Placeholder := {";
          retPlaceDBM->print_constraint();
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
				print_sequentCheck(step - 1, retVal, lhs, retPlaceDBM, sub, rhs->getOpType());
				if(retVal) {
					cout <<"----(Valid) Last Placeholder Check Passed (Check Only)-----" << endl
          << "----With Placeholder := {";
          retPlaceDBM->print_constraint();
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
      break;
    }
    case ALLACT: {
      retVal = true;
      /* Enumerate through all transitions */
      #if DEBUG	
      if(debug) {
        cout << "\t Proving ALLACT Transitions:----\n" << endl; 
      }
      #endif
      for(vector<Transition *>::iterator it = transList->begin();
        it != transList->end(); it++ ) {
        Transition * tempT = *it;
        /* Obtain the entire ExprNode and prove it */
        DBM tempLHS(*lhs);
        
        bool tempBool = comp_ph(&tempLHS, tempT->getLeftExpr(), sub);
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
        SubstList * sl = tempT->getEnteringLocation(sub);
        bool isInv = invs_chk(&invCons, sl);
        delete sl;
        if(isInv) {
          invCons.cf();
          ClockSet * st = tempT->getCSet();
          if(st != NULL) {
            invCons.preset(st);
          }
          invCons.cf();
          /* Now perform clock assignments sequentially: perform the
           * front assignments first */
          vector<pair<short int, short int> > * av = tempT->getAssignmentVector();
          if(av != NULL) {
            // Iterate over the vector and print it
            for(vector<pair<short int, short int> >::iterator it=av->begin(); it != av->end(); it++) {
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
              invCons.print_constraint();
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
          invCons.print_constraint();
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
      break;
    }
    case EXISTACT: {
      retVal = false;
      /* Enumerate through all transitions */
      #if DEBUG	
      if(debug) {
        cout << "\t Proving EXISTACT Transitions:----\n" << endl; 
      }
      #endif
      /* Use placeholders to split rules */
      bool emptyPartialPlace = true;
      DBMList * partialPlace;
      for(vector<Transition *>::iterator it = transList->begin();
        it != transList->end(); it++ ) {
        Transition * tempT = *it;

        /* Obtain the entire ExprNode and prove it */
       
       
        // Make a similar comp function for exists so 
        // because the entire zone must be able to transition
        // or split by placeholders
        DBMList tempPlace(*INFTYDBM);
        lhs->cf();
        DBM tempLHS(*lhs);
        bool tempBool = comp_ph_exist_place(&tempLHS, &tempPlace, tempT->getLeftExpr(), sub);
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
        SubstList * sl = tempT->getEnteringLocation(sub);
        bool isInv = invs_chk(&invCons, sl);
        delete sl;
        if(isInv) {
          invCons.cf();
          ClockSet * st = tempT->getCSet();
          if(st != NULL) {
            invCons.preset(st);
          }
          invCons.cf();
          /* Now perform clock assignments sequentially: perform the
           * front assignments first */
          vector<pair<short int, short int> > * av = tempT->getAssignmentVector();
          if(av != NULL) {
            // Iterate over the vector and print it
            for(vector<pair<short int, short int> >::iterator it=av->begin(); it != av->end(); it++) {
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
                invCons.print_constraint();
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
      break;
    }
    case IMPLY:{
      /* Here is the one call to comp_ph(...) outside of copm_ph(...) */
      DBM tempLHS(*lhs);
      if(comp_ph(&tempLHS, rhs->getLeft(), sub)){
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
      break;}
    case CONSTRAINT:{          
      lhs->cf();
      /* The line: (rhs->dbm())->cf(); is not needed */
      retVal = (*lhs <= *(rhs->dbm()));
      #if DEBUG	   
      if (debug && retVal) {
        cout << "---(Valid) Leaf DBM (CONSTRAINT) Reached----" << endl << endl;
      }
      if (debug && !retVal) {
        cout << "---(Invalid) Leaf DBM (CONSTRAINT) Reached----" << endl << endl;
      }
      #endif
      break;}
    case BOOL:{
      retVal = (rhs->getBool());
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
      retVal = (sub->operator[](rhs->getAtomic()) == rhs->getIntVal());
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
      retVal = (sub->operator[](rhs->getAtomic()) != rhs->getIntVal());
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
      retVal = (sub->operator[](rhs->getAtomic()) < rhs->getIntVal());
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
      retVal = (sub->operator[](rhs->getAtomic()) > rhs->getIntVal());
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
      retVal = (sub->operator[](rhs->getAtomic()) <= rhs->getIntVal());
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
      retVal = (sub->operator[](rhs->getAtomic()) >= rhs->getIntVal());
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
      SubstList *st = new SubstList(rhs->getSublist(), sub );
      retVal = do_proof(step, lhs, rhs->getExpr(), st);
      delete st;
      break;}
    case RESET:{
      lhs->cf();
      DBM ph(*lhs);
      ClockSet *rs = rhs->getClockSet();
      ph.reset(rs);
      
      retVal = do_proof(step, &ph, rhs->getExpr(), sub);
      break;}
    case ASSIGN:{
      lhs->cf();
      DBM ph(*lhs);
      /* Here the DBM zone is where the value of
       * clock x is reset to clock y, which is possibly
       * a constant or a value*/
      short int cX = rhs->getcX();
      short int cY = rhs->getcY();
      
      ph.reset(cX, cY);
      
      retVal = do_proof(step, &ph, rhs->getExpr(), sub);
      break; }
    case REPLACE:{
      sub->operator[](rhs->getcX()) = sub->operator[](rhs->getcY());
      retVal = do_proof(step, lhs, rhs->getExpr(), sub);
      break; }
    case ABLEWAITINF:{
      lhs->cf();
      DBM ph(*lhs);
      ph.suc();
      invs_chk(&ph, sub);
      ph.cf();
      /* Time can diverge if and only if there are no upper bound
       * constraints in the successor */
      retVal = !(ph.hasUpperConstraint());
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
      DBM ph(*lhs);
      ph.suc();
      invs_chk(&ph, sub);
      ph.cf();
      /* Time cannot diverge if and only if there is an upper bound
       * constraint in the successor */
      retVal = ph.hasUpperConstraint();
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
      cout <<"Error, operator not defined." << endl;
  }
         
  return retVal;
}



/** The main method that takes in an example file
 * and then does Real-Time Model Checking on it.
 * basic syntax is "demo options input_file_name".
 * @param argc The number of input arguments (the program
 * name is the first argument).
 * @param argv (**) The array of strings containing
 * the program arguments.
 * @return 0 for a normal exit, -1 for an exit upon an error. */
int main(int argc, char** argv){
  
  cout << "\n\n====Begin Program Input==============================" << endl;
  /* Get times for lexing and parsing files: */
  time_t rawtime_lp;
  time(&rawtime_lp);
  /* print Starting time */ 
  if(debug) {
    cout <<"Program start time: "<< ctime(&rawtime_lp) ;
  }
  clock_t begin_lp = clock();
  
  /* Sets parameters and looks for inputs from the command line. */
  char c;
  /* If True, use tables in the output.  Else (False),
   * print regular output. */
  bool tabled = false;
  /* The size of the Hash table of Sequents: nBits + 1 */
  int  nHash = 16;
  while ( (c = getopt(argc, argv, "dhntH:")) != -1) {
    switch (c) {
      case 'd' :
        debug = true; // Turn on Debug Mode
        break;
      case 't' : // Turn on tabled output
        /* This outputs the lists of tabled sequents
         * used in sequent caching */
        tabled = true;
        break;
      case 'H' : // change the Hash Size
        nHash = atoi(optarg);
        nbits = nHash - 1;
        if(nHash < 1) {
          cerr << "Hashed number must be greater than 0." << endl; exit(-1);
        }
        break;
      case 'n':
        useCaching = false;
        break;
      case 'h' : // Help: print the Usage.
        printUsage();
        exit(1);
    }
  }
  if (argc < 2){
    fprintf(stderr, "Must have an input file argument.\n" );
    printUsage();
    exit(-1);
  }
  
  for (int i = 0; i < argc; i++){
    cout << argv[i] << " ";
  }
  cout <<endl;
  
  /* Read and lex the input file to tokens for the parser to use. */
  char * fileName;   
  fileName = argv[argc-1];
  yyin = fopen(fileName, "r");
  if (!yyin) {
    fprintf(stderr, "\nCannot open input file %s.\n",fileName);
    exit(-1);
  }
  
 

  transList = new vector<Transition *>;
  /* Parses the Example File (and produces the ExprNode structure.)
   * Returns 0 if successful, 1 for Syntax Error, and 2 for out of Memory 
   * (usually). */
  int parseError = yyparse(); 
  
  if(parseError != 0) {
    cout << endl << "**Syntax Error: Error Parsing file.**" << endl << endl;
    cout << "==--End of Program Execution-----------------------==" << endl;
    return 1;
  }
  
  /* Inputs have now be approved and values set.  Here
   * the Real-Time Model Checking begins */
  /* Start the Model Checking */
  cout << "Program input file (timed automaton + MES): " << fileName << endl;
  cout << "max constant in clock constraints: " << MAXC << endl << endl;
  
  
  /* Find the root expression of the Expression tree generated by the parser.
   */
  ExprNode * start = lookup_predicate(start_predicate);
  
  if( start == NULL){
    cout << "Interested predicate is not properly given." << endl;
    exit(-1);}
  
  aSize = atomic.size();
  
  // get the current parity of Start and Initialize the proper parities
  currParityGfp = start->get_Parity();
  prevParityGfp = currParityGfp;
  
  /* Create the initial substituation list,
   * either empty or from the initial list 
   * that was generated by the parser. */
  SubstList *sublist = new SubstList(aSize);
  for(int i=0; i < aSize; i++){
    map <int, int>::iterator it = InitSub.find(i);
    sublist->operator[](i) = (*it).second;
  }
  
  seqStSize = nHash;
  Xlist_pGFP = new stack[predicateInd*nHash];
  Xlist_pLFP = new stack[predicateInd*nHash];
  Xlist_true = new stack[predicateInd*nHash];
  Xlist_false = new stack[predicateInd*nHash];
  Xlist_pGFP_ph = new stackPlace[predicateInd*nHash];
  Xlist_pLFP_ph = new stackPlace[predicateInd*nHash];
  Xlist_true_ph = new stackPlace[predicateInd*nHash];
  Xlist_false_ph = new stackPlace[predicateInd*nHash];
  
  /* Initialize DBMs. The initial constructor
   * indicates that the DBM is not in canonical form. 
   * We also make it so reference DBMs are in
   * canonical form (low performance cost now,
   * ease of comparisons later). */

  EMPTY = new DBM(spaceDimension);
  for (int i=1; i<spaceDimension; i++){
    EMPTY->addConstraint(i,0, 0);
    EMPTY->addConstraint(0,i, 0);
  }
  EMPTY->cf();
  
  /* This is initialized to be the largest (loosest)
   * possible DBM
   * @see DBM Constructor (Default Constructor). */
  INFTYDBM = new DBM(spaceDimension);
  INFTYDBM->cf(); 
  
  /* Give a default DBM initialization of a DBM
   * to use for the proofs, that represents
   * the current DBM if an inital one is
   * not provided. 
   * This DBM sets all clocks equal to 0. */
  DBM *dbm = new DBM(spaceDimension);
  for (int i=0; i<spaceDimension; i++) {
    dbm->addConstraint(i,0, 0x1);
  }
  dbm->cf();
  
  /* Initialize parent sequents to NULL */
  parentRef = NULL;
  parentPlaceRef = NULL;
  
  retPlaceDBM = new DBMList(*INFTYDBM);
  // This number converts system time to seconds.
  // If the runtime is not correct, you may need to change
  // this value
  double clockToSecs = 0.000001;
#ifdef __APPLE__
  // Defined so it produces the right time values
  // Find this my timing a few examples and comparing
  clockToSecs = .000001;
#elif defined __WIN32__ || defined _WIN64 
  clockToSecs = 0.001;
#elif defined __CYGWIN__
  clockToSecs = 0.001; 
#else
  // Use the default clockToSecs value as defined above
#endif
  
  /* Now finished with lexing and parsing */
  clock_t end_lp = clock();
  time(&rawtime_lp);
  
  time_t rawtime;
  time(&rawtime);
  /* print Starting time */ 
  if(debug) {
    cout << "##--Beginning of Proof==-------------------" << endl;
    cout <<"Prover start time: "<< ctime(&rawtime) ;
  }
  clock_t begin = clock();
  bool suc;
  
  #if DEBUG
  // Print Transitions
  if(debug) {
    cout << endl << "TRANSITIONS:" << endl;
    for(vector<Transition *>::iterator it = transList->begin();
        it != transList->end(); it++ ) {
        Transition * tempT = *it;
        print_Transition(tempT, cout);
        cout << endl;   
    }
    cout << endl;
  }
  #endif

  numLocations = 1;
  /* Call the Model Checker with the given ExprNode 
   * to prove or disprove the specification. */
  if (InitC != NULL) {
		InitC->setIsCfFalse();
    InitC->cf();
    suc = do_proof(0, InitC, start, sublist);
  }
  else {
    suc = do_proof(0, dbm, start, sublist);
  }
  
  /* Now finished with the proof/disproof, so output the result of the Model Checker */
  clock_t end = clock();
  time(&rawtime);
  if(debug) {
   
    cout <<"Prover end time: "<< ctime(&rawtime);
     cout << "##--End of Proof==------------------" << endl << endl;
  }
  if (suc) {
    cout << "--==Program Result:  **Valid**  ==-------------------" << endl;
    cout << "Valid proof found. The timed automaton satisfies the MES." << endl << endl;
  }
  else {
    cout << "--==Program Result:  **Invalid**  ==-----------------" << endl;
    cout << "Invalid proof found. The timed automaton does not satisfy the MES." << endl << endl;
  }
  double totalTime = clockToSecs*(end_lp + begin_lp) + clockToSecs*(end - begin);
  
  cout << "--==Program Time:  **" << clockToSecs*(end_lp + begin_lp) + clockToSecs*(end - begin) << " seconds**  ==----------" << endl;
  cout << "Lexer and parser running time: " << clockToSecs*(end_lp - begin_lp) << " seconds" << endl;
  cout << "Prover running time: " << clockToSecs*(end - begin) << " seconds" << endl; 
  cout << "Combined running time: " << totalTime  << " seconds" << endl;
  
  cout << "Number of locations: " << numLocations << endl;
  
  #if DEBUG	   
	/* If in DEBUG Mode, print out list of Tabled Sequents */
  if(tabled){ 
    cout << endl;
    cout << "##--Debug Info: Tabled Sequents===============" << endl;
    cout << "----GFP Cached Sequents---------" << endl;
    print_Xlist(Xlist_pGFP);
    // cout << "Number of GFP Sequents Tabled: " endl;
    cout << endl;
    cout << "----LFP Cached Sequents---------" << endl;
    print_Xlist(Xlist_pLFP); 
    cout << endl;
    cout << "----Known False Cached Sequents---------" << endl;
    print_Xlist(Xlist_false); 
    cout << endl;
    cout << "----Known True Cached Sequents---------" << endl;
    print_Xlist(Xlist_true); 
    cout << endl;
    cout << "##--Debug Info: Tabled Placeholder Sequents==========" << endl;
    cout << "----GFP Placeholder Cached Sequents---------" << endl;
    print_Xlist(Xlist_pGFP_ph);
    // cout << "Number of GFP Sequents Tabled: " endl;
    cout << endl;
    cout << "----LFP Placeholder Cached Sequents---------" << endl;
    print_Xlist(Xlist_pLFP_ph); 
    cout << endl;
    cout << "----Known False (Placeholder) Cached Sequents---------" << endl;
    print_Xlist(Xlist_false_ph); 
    cout << endl;
    cout << "----Known True (Placeholder) Cached Sequents---------" << endl;
    print_Xlist(Xlist_true_ph); 
  }
  #endif
  
  
	// Clean Up Dynamic Memory to eliminate Memory Leaks
  delete dbm;
  delete InitC;
  delete EMPTY;
  delete INFTYDBM;
  delete retPlaceDBM;
  // Since Vectors and Maps do not call the destructors of its elements
  // We must iterate and delete
  
	for(int i = 0; i < predicateInd*nHash; i++) {
		// Now Iterate and delete for each vector
    for(stack::iterator it = Xlist_pGFP[i].begin(); it != Xlist_pGFP[i].end(); it++) {
			Sequent *ls = (*it);
			delete ls;
    }
    for(stack::iterator it = Xlist_pLFP[i].begin(); it != Xlist_pLFP[i].end(); it++) {
			Sequent *ls = (*it);
			delete ls;
    }
    for(stack::iterator it = Xlist_true[i].begin(); it != Xlist_true[i].end(); it++) {
			Sequent *ls = (*it);
			delete ls;
    }
    for(stack::iterator it = Xlist_false[i].begin(); it != Xlist_false[i].end(); it++) {
			Sequent *ls = (*it);
			delete ls;
    }
    for(stackPlace::iterator it = Xlist_pGFP_ph[i].begin(); it != Xlist_pGFP_ph[i].end(); it++) {
			SequentPlace *ls = (*it);
			delete ls;
    }
    for(stackPlace::iterator it = Xlist_pLFP_ph[i].begin(); it != Xlist_pLFP_ph[i].end(); it++) {
			SequentPlace *ls = (*it);
			delete ls;
    }
    for(stackPlace::iterator it = Xlist_true_ph[i].begin(); it != Xlist_true_ph[i].end(); it++) {
			SequentPlace *ls = (*it);
			delete ls;
    }
    for(stackPlace::iterator it = Xlist_false_ph[i].begin(); it != Xlist_false_ph[i].end(); it++) {
			SequentPlace *ls = (*it);
			delete ls;
    }
		
		
    
  }
  delete []Xlist_pGFP;
  delete []Xlist_pLFP;
  delete []Xlist_true;
  delete []Xlist_false;
  delete []Xlist_pGFP_ph;
  delete []Xlist_pLFP_ph;
  delete []Xlist_true_ph;
  delete []Xlist_false_ph;
  

  //delete start;
  // Do Extra Work to Delete Elements at the End
	for(vector<ExprNode *>::iterator it = invs.begin(); 
    	it != invs.end(); it++) {
    ExprNode *ls = (*it);
    delete ls;
  }
  // Clear Vectors to free up dynamic memory
  invs.clear();
  
  // Do Extra Work to delete Dynamically Allocated Elements
	for(map<string, ExprNode *>::iterator it = equations.begin(); 
     	it != equations.end(); it++) {
    ExprNode *ls = (*it).second;
    delete ls;
  }
  // Do Extra Work to delete Dynamically Allocated Elements
  // Delete the predicates here since the ExprNode Destructor
  // Does not traverse predicates to make sure of no inconsistencies.
 	for(map<string, ExprNode *>::iterator it = predicates.begin(); 
     	it != predicates.end(); it++) {
    ExprNode *ls = (*it).second;
    /* While we should delete, this has problems when an equation
     * is just a predicate. (?)*/
    ls->deletePredicate();
    delete ls;
    
  }
  predicates.clear();
  equations.clear();
  
  /* Delete Transitions in transition list */
  for(vector<Transition *>::iterator it = transList->begin();
    it != transList->end(); it++ )
  {
    /* As a debug, print the transitions before deletion */
    //print_Transition(*it, cout, 0);
    delete (*it);
  }
  transList->clear();
  delete transList;

  // Clear Maps to free up dynamic memory
  atomic.clear();
  clocks.clear();
  InitSub.clear();
  
  // delete other parts
  delete sublist;
  
  // Close File for good file handling
  fclose(yyin);
  
  cout << "==--End of Program Execution-----------------------==" << endl;
  
  return 0;
}

