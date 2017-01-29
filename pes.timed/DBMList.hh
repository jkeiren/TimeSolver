/** \file DBMList.hh
 * A List of Difference Bound Matrices (DBMList); a
 * list (union) of matrices implementation for a union of clock
 * zones.
 * @author Peter Fontana, Dezhuang Zhang, and Rance Cleaveland.
 * @note Many functions are inlined for better performance.
 * @version 1.21
 * @date November 8, 2013 */

#ifndef DBMLIST_H
#define DBMLIST_H

#include <iostream>
#include <vector>
#include "DBM.hh"

/** The Difference Bound Matrix List (DBMList) class; a list
 * (union) of matrices implementation for a union of clock zones.
 * The DBMList is a vector of DBMs. The implementation is such that
 * each DBM_i in DBM_1, DBM_2, ... DBM_k is a Difference Bound Matrix (DBM),
 * and the DBMList represents the clock zone (DBM_1 || DBM_2 || ... ||| DBM_k).
 * This method provides a simple implementation of clock zone unions (not
 * necessarily the fastest) and is written so that if the DBMList has only one
 * DBM (is just a clock zone), the implementation is fast. We utilize this
 * reasoning on the (unproven) belief that clock zone unions will be rarely
 * used; the prover works to minimize the use of clock zone unions. Hence,
 * many methods either have an equivalent taking in only a DBM and/or are
 * optimized when the input DBMList or the calling DBMList is in fact
 * equivalent to a DBM (stores one DBM).
 * @author Peter Fontana, Dezhuang Zhang, and Rance Cleaveland.
 * @note Many functions are inlined for better performance.
 * @version 1.2
 * @date November 2, 2013 */
class DBMList {
private:
  /** True if the DBM is still in canonical form (cf()), false otherwise.
   * This provides a quick a 1-bit check that avoids needless
   * work to convert something already in cf() to cf(). */
  bool isCf;

  /** The list of DBMs; the set of valuations represented is
   * dbmListVec[0] || dbmListVec[1] || ... || dbmListVec[listSize-1]. */
  std::vector<DBM *> * dbmListVec;

  bidirectional_map<std::string, int>* declared_clocks;

  /** Private method that returns the complement of a DBM. This uses
   * the (simple) method of performing a DBM that is the union of all
   * the negated constraints of the DBM. This method is private
   * because it is not needed by the prover.
   * @param Y (&) The DBM to complement.
   * @return The complemented DBM, given as a DBMList. */
  DBMList * complementDBM(const DBM &Y) {
    if(Y.emptiness()) {
      DBMList * newList = new DBMList(Y.nClocks, Y.declared_clocks);
      return newList;
    }
    /* Check for infinity DBM */
    bool hasAConstraint = false;
    DBMList * myList = NULL;
    for(int i = 0; i < Y.nClocks; i++) {
      for(int j = 0; j < Y.nClocks; j++) {
        if(!(Y.isConstraintImplicit(i,j))) {
          hasAConstraint = true;
          int tempVal = Y(i,j);
          int tempCons = 0x1;
          if((tempVal&0x1) == 0x1) {
            tempCons = 0;
          }
          short int constraintVal = ((-(tempVal >> 1)) << 1) + tempCons;
          DBM *tempDBM = new DBM(nClocks,j,i, constraintVal, declared_clocks);
          if(myList == NULL) {
            myList = new DBMList(*tempDBM);
          }
          else {
            myList->addDBM(*tempDBM);
          }
          delete tempDBM;

        }
      }
    }
    if(hasAConstraint == false) {
      // Set to Empty DBM
      DBM * emptyDBM = new DBM(Y.nClocks, Y.declared_clocks);

      for (int i=1; i<Y.nClocks; i++){
        emptyDBM->addConstraint(i,0, 0);
        emptyDBM->addConstraint(0,i, 0);
        emptyDBM->addConstraint(0,0, 0);
      }
      emptyDBM->cf();
      myList = new DBMList(*emptyDBM);
      delete emptyDBM;
    }
    else {
      myList->setIsCfFalse();
    }
    return myList;
  }

public:
  /** The Number of clocks in the space for the DBMList. This
   * number includes the "zero clock." This number is also
   * the same for all DBMs in the DBMList. */
  short int nClocks;

  /** Return the number of DBMs in the DBMList. This is used to
   * determine how many zones are unioned. Knowing if the size
   * is 1 or larger than 1 is critical, since many methods are
   * optimized for a DBMList with one DBM, which is equivalent
   * to a DBM.
   * @return The number of DBMs in the DBMList. */
  int numDBMs() const {
    return dbmListVec->size();
  }

  /** Return the vector of DBMs. Utilized by other methods to access
   * the DBMs, often to iterate through each DBM.
   * @return The vector storing the DBMs in the DBMList. */
  std::vector<DBM *> * getDBMList() const {
    return dbmListVec;
  }

  /** Default Constructor for a DBMList; creates an initial DBMList
   * with one DBM,
   * representing no constraint: the diagonal and the top row are
   * (0, <=), and the rest of the entries are (infinity, <).
   * This is the loosest possible DBM.
   * @param numClocks The number of clocks, including the one "dummy" \
   * "zero clock". Hence, there are numClocks - 1 actual clocks
   * with 1 "zero" clock.
   * @return [Constructor] */
  DBMList(const short int numClocks, bidirectional_map<std::string, int>* cs)
    : declared_clocks(cs)
  {
    nClocks = numClocks;
    dbmListVec = new std::vector<DBM *>;
    dbmListVec->push_back(new DBM(numClocks, cs));
    isCf = false;
  }

  /** Copy Constructor for DBMList, making a DBMList representing the
   * DBM.
   * @param Y (&) The object to copy.
   * @return [Constructor] */
  DBMList(const DBM &Y) {
    nClocks = Y.nClocks;
    dbmListVec = new std::vector<DBM *>;
    DBM * tDBM = new DBM(Y);
    dbmListVec->push_back(tDBM);
    isCf = Y.isInCf();
    declared_clocks = Y.declared_clocks;

  }

  /** Copy Constructor for DBMLists, copying a DBMList.
   * @param Y (&) The object to copy.
   * @return [Constructor] */
  DBMList(const DBMList &Y) {
    nClocks = Y.nClocks;
    // Vector constructor makes a deep copy of the pointers (not of the objects
    // that the pointers point to). Make a deep copy of the DBM objects here
    std::vector <DBM *> * currList = Y.getDBMList();
    dbmListVec = new std::vector<DBM *>;
    for(unsigned int i = 0; i < currList->size(); i++) {
      DBM *tD =(*currList)[i];
      dbmListVec->push_back(new DBM(*tD));
    }
    isCf = Y.isCf;
    declared_clocks = Y.declared_clocks;
  }

  /** Destructor; deletes each DBM in the DBMList and then deletes the vector.
   * @return [Destructor]. */
  ~DBMList() {
    if(dbmListVec != NULL) {
      for(std::vector<DBM *>::iterator it=dbmListVec->begin(); it != dbmListVec->end(); it++)
      {
        DBM *tD = *it;
        delete tD;
      }
      dbmListVec->clear();
    }
    delete dbmListVec;

  }

  /** Tell the object that it is not in canonical form.
   * Call this method whenever changing the DBMList's value from the outside.
   * Otherwise, cf() will fail to convert the DBMList to canonical form.
   * @return None */
  void setIsCfFalse() {
    isCf = false;
    /* Do I also need to set isCf = false for internal DBMs?
     * I believe I do. */
    for(std::vector<DBM *>::iterator it=dbmListVec->begin(); it != dbmListVec->end(); it++)
    {
      DBM * tD = *it;
      tD->setIsCfFalse();
    }
  }

  /** Returns whether this DBMList is in canonical form or not.
   * @return true: the DBMList is in canonical form; false: otherwise. */
  bool isInCf() const {
    return isCf;
  }

  /** Union the calling DBMList with DBM Y; perform this by making
   * a deep copy of Y and adding to the list of DBMs.
   * The calling DBMList is changed.
   * @param Y (&) The DBM to add to the list of DBMs.
   * @return None. */
  void addDBM(const DBM &Y) {
    dbmListVec->push_back(new DBM(Y));
  }

  /** Union the calling DBMList with DBMList Y; perform this by making
   * a deep copy of each DBM in Y and adding to the list of DBMs.
   * The calling DBMList is changed.
   * @param Y (&) The DBMList to add to the list of DBMs.
   * @return None. */
  void addDBMList(const DBMList &Y) {
    for(std::vector<DBM *>::iterator it=(Y.dbmListVec)->begin(); it != (Y.dbmListVec)->end(); it++)
    {
      addDBM(*(*it));
    }
  }

  /** Performs a deep copy of the DBMList.
   * The DBMList calling this method is changed.
   * Preserves canonical form.
   * @param Y (&) The object to copy.
   * @return A reference to the copied object, which is the LHS object. */
  DBMList & operator = (const DBMList &Y){
    nClocks = Y.nClocks;
    if(dbmListVec->size() == 1 && Y.numDBMs() == 1) {
      *((*dbmListVec)[0]) = *((*(Y.getDBMList()))[0]);
    }
    else if (Y.numDBMs() == 1) {
      while(dbmListVec->size() > 1) {
        DBM * tempDBM = dbmListVec->back();
        delete tempDBM;
        dbmListVec->pop_back();
      }
      *((*dbmListVec)[0]) = *((*(Y.getDBMList()))[0]);
    }
    else {
      std::vector<DBM *> * tempList = dbmListVec;
      // Vector constructor makes a deep copy of the pointers (not of the objects
      // that the pointers point to). Make a deep copy of the DBM objects here
      std::vector <DBM *> * currList = Y.getDBMList();
      dbmListVec = new std::vector<DBM *>;
      for(unsigned int i = 0; i < currList->size(); i++) {
        dbmListVec->push_back(new DBM( *((*currList)[i])));
      }

      for(std::vector<DBM *>::iterator it=tempList->begin(); it != tempList->end(); it++)
      {
        DBM *tD = *it;
        delete tD;
      }
      tempList->clear();
      delete tempList;
    }

    isCf = Y.isInCf();
    return *this;
  }

  /** Performs a deep copy of a DBM to a DBMList object.
   * The DBMList calling this method is changed.
   * Preserves canonical form.
   * @param Y (&) The object to copy.
   * @return A reference to the copied object, which is the LHS object. */
  DBMList & operator = (const DBM &Y){
    nClocks = Y.nClocks;
    while(dbmListVec->size() > 1) {
      DBM * tempDBM = dbmListVec->back();
      delete tempDBM;
      dbmListVec->pop_back();
    }
    *((*dbmListVec)[0]) = Y;

    isCf = Y.isInCf();
    return *this;
  }

  /** Method that returns the complement of a DBMList. This uses
   * the (simple) method of performing a DBM that is the union of all
   * the negated constraints of the DBM, and complementing
   * DBM-by-DBM by converting the complement of the DBMs into
   * disjunctive normal form.
   * @return The complemented DBMList, given as a DBMList. */
  DBMList & operator!(){
    if(dbmListVec->size() == 1) {
      std::vector<DBM *> * tempList = dbmListVec;
      DBMList * myTempList = (this->complementDBM(*((*dbmListVec)[0])) );
      dbmListVec = myTempList->getDBMList();
      // Now clean up DBMs used
      for(std::vector<DBM *>::iterator it=tempList->begin(); it != tempList->end(); it++)
      {
        DBM *tD = *it;
        delete tD;
      }
      tempList->clear();
      delete tempList;
      // The vector was a shallow copy, so delete the rest of the list
      myTempList->dbmListVec = NULL;
      delete myTempList;
    }
    else {
      std::vector <DBM *> *tempList = dbmListVec;
      std::vector<DBMList *> dbmVec;
      for(unsigned int i = 0; i < dbmListVec->size(); i++) {
        DBMList * outputList = complementDBM(*((*dbmListVec)[i]));
        dbmVec.push_back(outputList);
      }
      // Vector constructor makes a deep copy of the pointers (not of the objects
      // that the pointers point to). Make a deep copy of the DBM objects here
      std::vector <DBM *> * currList = (dbmVec[0])->getDBMList();

      dbmListVec = new std::vector<DBM *>;
      for(unsigned int i = 0; i < currList->size(); i++) {
        DBM * myDBM = new DBM( *((*currList)[i]));
        dbmListVec->push_back(myDBM);
      }
      for(unsigned int j = 1; j < dbmVec.size(); j++){
        this->cf();
        *this & *(dbmVec[j]);
      }
      // Now delete tempList
      for(std::vector<DBM *>::iterator it=tempList->begin(); it != tempList->end(); it++)
      {
        DBM *tD = *it;
        delete tD;
      }
      tempList->clear();
      delete tempList;
      /* Delete dbmVec */
       for(std::vector<DBMList *>::iterator it=dbmVec.begin(); it != dbmVec.end(); it++)
      {
        DBMList *tD = *it;
        delete tD;
      }
      dbmVec.clear();
      // Now delete currList
      currList = NULL;


    }
    isCf = false;
    return *this;
  }

  /** Intersects a DBMList with a DBM converting the intersection to
   * disjunctive normal form. This involves intersecting
   * each DBM in the DBMList with the given DBM.
   * This method does not require the DBMList or the DBM to be in
   * canonical form, and does not preserve canonical form of the DBMList. The
   * calling DBMList is changed.
   * @param Y (&) The DBM to intersect
   * @return The reference to the intersected DBMList (which is the now changed
   * calling DBMList). */
  DBMList & operator & (const DBM &Y){
    if(dbmListVec->size() == 1) { // Do you really want to treat 1 as a special case?
      *((*dbmListVec)[0]) & Y;
      isCf = false;
      return *this;
    }

    /* This forms a new list by distributing the DBMs */
    for(unsigned int i = 0; i < dbmListVec->size(); i++) {
      /* Since the vector of DBMs stores the pointers
       * hopefully this updates the vector for the correct DBMs */
      DBM *tD = (*dbmListVec)[i];
      *tD & Y;
    }
    isCf = false;
    return *this;
  }

  /** Intersects two DBMLists by converting the intersection to
   * disjunctive normal form. This involves intersecting
   * DBM by DBM in the list of DBMs.
   * This method does not require the DBMLists to be in
   * canonical form, and does not preserve canonical form of the DBMList. The
   * calling DBMList is changed.
   * @param Y (&) The DBMList to intersect
   * @return The reference to the intersected DBMList (which is the now changed
   * calling DBMList). */
  DBMList & operator & (const DBMList &Y){
    if(dbmListVec->size() == 1 && Y.numDBMs() == 1) {
      *((*dbmListVec)[0]) & *((*(Y.getDBMList()))[0]);
      isCf = false;
      return *this;
    }
    if(dbmListVec->size() == 1) {
      std::vector<DBM *> * tempList = dbmListVec;
      // Vector constructor makes a deep copy of the pointers (not of the objects
      // that the pointers point to). Make a deep copy of the DBM objects here
      std::vector <DBM *> * currList = Y.getDBMList();
      dbmListVec = new std::vector<DBM *>;
      for(unsigned int i = 0; i < currList->size(); i++) {
        dbmListVec->push_back(new DBM( *((*currList)[i])));
      }
      for(unsigned int i = 0; i < Y.dbmListVec->size(); i++) {
        /* Since the std::vector of DBMs stores the pointers
        * hopefully this updates the vector for the correct DBMs */
        DBM * tD = (*dbmListVec)[i];
        *tD & *((*tempList)[0]);

      }
      // We have to delete element by element
      // Now delete tempList
      for(std::vector<DBM *>::iterator it=tempList->begin(); it != tempList->end(); it++)
      {
        DBM *tD = *it;
        delete tD;
      }
      tempList->clear();
      delete tempList;
    }
    else {
      /* Iterate through Y dbmListVec times */
      std::vector<DBM *> * tempList = dbmListVec;
      dbmListVec = new std::vector<DBM *>;
      for(unsigned int i = 0; i < tempList->size(); i++) {
        for(unsigned int j = 0; j < Y.dbmListVec->size(); j++) {
          /* Since the vector of DBMs stores the pointers
          * hopefully this updates the vector for the correct DBMs */
          DBM * copyDBM = new DBM(*((*tempList)[i]));
          *copyDBM & *((*(Y.dbmListVec))[j]);
          dbmListVec->push_back(copyDBM);
        }
      }
      // We have to delete element by element
      // Now delete tempList
      for(std::vector<DBM *>::iterator it=tempList->begin(); it != tempList->end(); it++)
      {
        DBM *tD = *it;
        delete tD;
      }
      tempList->clear();
      delete tempList;

    }
    /* This forms a new list by distributing out the intersection */
    /* Should we check for same number of clocks (?)
     * Currently, the code does not. */
    isCf = false;
    return *this;
  }

  /** Performs subset checks;
   * X <= Y if and only if each DBM in X is contained in Y.
   * (This also assumes that X and Y have the same
   * number of clocks). Because Y is a DBM,
   * we can optimize the subset computation.
   * For this method,
   * only Y is required to be in canonical form.
   * @param Y (&) The right DBM.
   * @return true: *this <= Y; false: otherwise. */
  bool operator <= (const DBM &Y) const{

    bool tempB = true;
    for(unsigned int i = 0; i < dbmListVec->size(); i++) {
      tempB = *((*dbmListVec)[i]) <= Y;
      if (tempB == false) {
        return false;
      }
    }
    return true;
  }

  /** Performs subset checks;
   * X <= Y if and only if X && !Y is empty.
   * This is a simpler (but computationally intensive)
   * implementation.
   * (This also assumes that X and Y have the same
   * number of clocks). For this method,
   * only Y is required to be in canonical form.
   * @param Y (&) The right DBMList.
   * @return true: *this <= Y; false: otherwise. */
  bool operator <= (const DBMList &Y) const {
    if(dbmListVec->size() == 1) {
      return Y >= *((*dbmListVec)[0]);
    }

    DBMList * tempDBMList = new DBMList(Y);
    !(*tempDBMList);
    tempDBMList->cf();
    if(tempDBMList->emptiness()) {
      delete tempDBMList;
      return true;
    }
    (*tempDBMList) & *this;
    tempDBMList->cf();
    bool isEmpty = tempDBMList->emptiness();
    delete tempDBMList;
    return isEmpty;
  }

  /** Performs superset checks;
   * X >= Y if and only if Y <= X, which is true if
   * and only if !X && Y is empty.
   * This is a simpler (but computationally intensive)
   * implementation.
   * (This also assumes that X and Y have the same
   * number of clocks). The simpler subset computation
   * only works when potentially greater structure is a DBM. For this method,
   * (*this), the calling DBMList, is required to be in canonical form.
   * @param Y (&) The right DBM.
   * @return true: *this >= Y; false: otherwise. */
  bool operator >= (const DBM &Y) const{
    if(dbmListVec->size() == 1) {
      return *((*dbmListVec)[0]) >= Y;
    }
    else {
      DBMList * tempDBMList = new DBMList(*this);
      !(*tempDBMList);
      tempDBMList->cf();
      if(tempDBMList->emptiness()) {
        delete tempDBMList;
        return true;
      }
      (*tempDBMList) & Y;
      tempDBMList->cf();
      bool isEmpty = tempDBMList->emptiness();
      delete tempDBMList;
      return isEmpty;
    }

  }

  /** Performs superset checks;
   * X >= Y if and only if Y <= X, which is true if
   * and only if !X && Y is empty.
   * This is a simpler (but computationally intensive)
   * implementation.
   * (This also assumes that X and Y have the same
   * number of clocks).  For this method,
   * (*this), the calling DBMList, is required to be in canonical form.
   * @param Y (&) The right DBMList.
   * @return true: *this >= Y; false: otherwise. */
  bool operator >= (const DBMList &Y) const {
    if(dbmListVec->size() == 1) {
      return Y <= *((*dbmListVec)[0]);
    }
    DBMList * tempDBMList = new DBMList(*this);
    !(*tempDBMList);
    tempDBMList->cf();
    if(tempDBMList->emptiness()) {
      delete tempDBMList;
      return true;
    }
    (*tempDBMList) & Y;
    tempDBMList->cf();
    bool isEmpty = tempDBMList->emptiness();
    delete tempDBMList;
    return isEmpty;


  }

  /** Determines equality of a DBMList and DBM;
   * X == Y if and only if X <= Y && X >= Y. Note that
   * in a DBMList, it might be possible (with our definition
   * of cf() for a DBMList) that a DBMList with more than one
   * DBM may be equal to the DBM. Equality means that the two
   * structures have the same set of clock valuations.
   * @param Y (&) The right DBM
   * @return true: the calling DBMList equals Y, false: otherwise. */
  bool operator == (const DBM &Y) const {
    if(dbmListVec->size() == 1) {
      return *((*dbmListVec)[0]) == Y;
    }
    return ((*this) <= Y) && ((*this) >= Y);
  }

  /** Determines equality of a two DBMLists;
   * X == Y if and only if X <= Y && X >= Y. Note that
   * in a DBMList, it might be possible (with our definition
   * of cf() for a DBMList) that DBMLists having a different
   * number of lists may be equal. Equality means that the two
   * structures have the same set of clock valuations.
   * @param Y (&) The right DBMList
   * @return true: the calling DBMList equals Y, false: otherwise. */
  bool operator == (const DBMList &Y) const {
    if(dbmListVec->size() == 1) {
      return Y == *((*dbmListVec)[0]);
    }
    return (*this <= Y) && (*this >= Y);
  }


  /** Checks and returns the relation comparing the calling DBMList
   * to Y.
   * @param Y (&) The right DBM.
   * @return An integer specifying the comparison between the
   * calling DBMList (X) and the input DBM (Y).  0: X incomparable to Y,
   * 1: X <= Y,  2: X >= Y,  3: X == Y.
   * @note This method assumes that the calling DBMList and Y have the same
   * number of clocks. */
  int relation(const DBM &Y) const {
    /* For now, just utilize the <= and >= comparisons. */
    bool gt = this->operator>=(Y);
    bool lt = this->operator<=(Y);

    if(gt && lt) return 3;
    if(gt) return 2;
    if(lt) return 1;
    return 0;
  }


  /** Checks and returns the relation comparing the calling DBMList
   * to Y.
   * @param Y (&) The right DBMList.
   * @return An integer specifying the comparison between the
   * calling DBMList (X) and the input DBMList (Y).  0: X incomparable to Y,
   * 1: X <= Y,  2: X >= Y,  3: X == Y.
   * @note This method assumes that the calling DBMList and Y have the same
   * number of clocks. */
  int relation(const DBMList &Y) const {
    /* For now, just utilize the <= and >= comparisons. */
    bool gt = this->operator>=(Y);
    bool lt = this->operator<=(Y);

    if(gt && lt) return 3;
    if(gt) return 2;
    if(lt) return 1;
    return 0;
  }

  /** Performs the time successor operator; this is equivalent
   * to computing the time successor of each DBM in the DBMList.
   * This method preserves canonical form.
   * @return The reference to the changed calling DBMList. */
  DBMList & suc(){

    for(unsigned int i = 0; i < dbmListVec->size(); i++) {
      DBM *tD = (*dbmListVec)[i];
      tD->suc();
    }
    isCf = false;
    return *this;
  }

  /** Performs the time predecessor operator; this is equivalent
   * to computing the time predecessor of each DBM in the DBMList.
   * This method does not preserves canonical form.
   * @return The reference to the changed calling DBMList. */
  DBMList & pre(){
    for(unsigned int i = 0; i < dbmListVec->size(); i++) {
      DBM *tD = (*dbmListVec)[i];
      tD->pre();
    }
    isCf = false;
    return *this;
  }

  /** Reset a single clock, specified by x, to 0, by resetting
   * each DBM in the DBMList.
   * The final DBMList is not in canonical form.
   * @param x The clock to reset to 0.
   * @return The reference to the changed, calling resulting DBMList. */
  DBMList & reset(const short int x){
    for(unsigned int i = 0; i < dbmListVec->size(); i++) {
      DBM *tD = (*dbmListVec)[i];
      tD->reset(x);
    }
    isCf = false;
    return *this;
  }

  /** Resets all the clocks in the given clock set to $0$ by resetting
   * each DBM in the DBMList.
   * The final DBM is not in canonical form.
   * @param rs (*) The set of clocks to reset to 0.
   * @return The reference to the changed, calling resulting DBM. */
  DBMList & reset(const ClockSet * const rs){
    for(unsigned int i = 0; i < dbmListVec->size(); i++) {
      DBM *tD = (*dbmListVec)[i];
      tD->reset(rs);
    }
    isCf = false;
    return *this;
  }

  /** Assign the current value to clock y to clock x (x := y). This
   * "resets" the clock x to the value of clock y, performing the
   * assignment in each DBM of the DBMList.
   * @param x The clock to change the value of
   * @param y The clock to reset the first clock to.
   * @return The reference to the changed, calling resulting DBMList. */
  DBMList & reset (const short int x, const short int y){
    for(unsigned int i = 0; i < dbmListVec->size(); i++) {
      DBM *tD = (*dbmListVec)[i];
      tD->reset(x,y);
    }
    isCf = false;
    return *this;
  }

  /** Compute the reset predecessor operator, which gives DBMList[x |-> 0].
   * This method computes the reset predecessor by computing the reset
   * predecessor for each DBM in the DBMList.
   * The DBMList needs to be in canonical form before
   * calling this method, and the resulting DBMList may not be in canonical form
   * after this operation.
   * @param x The clock that was just reset (after the predecessor zone).
   * @return The reference to the modified DBMList. */
  DBMList &preset(const short int x){
    for(unsigned int i = 0; i < dbmListVec->size(); i++) {
      DBM *tD = (*dbmListVec)[i];
      tD->preset(x);
    }
    isCf = false;
    return *this;
  }

  /** Compute the reset predecessor operator, which gives DBMList[PRS |-> 0].
   * This method computes the reset predecessor by computing the reset
   * predecessor for each DBM in the DBMList.
   * The DBMList needs to be in canonical form before
   * calling this method, and the resulting DBMList may not be in canonical form
   * after this operation.
   * @param prs (*) The set of clocks just reset (after the predecessor zone).
   * @return The reference to the modified DBMList. */
  DBMList &preset(const ClockSet * const prs){
    for(unsigned int i = 0; i < dbmListVec->size(); i++) {
      DBM *tD = (*dbmListVec)[i];
      tD->preset(prs);
    }
    isCf = false;
    return *this;
  }

  /** Compute the reset predecessor operator after the assignment
   * of x to y, which gives DBM[x |-> y]. Computed by computing DBM[x |-> y]
   * for each DBM in the DBMList.
   * The DBMList needs to be in canonical form before
   * calling this method, and the resulting DBMList may not be in canonical form
   * after this operation.
   * @param x The clock that was just reset (after the predecessor zone).
   * @param y The second clock; the clock whose value x was just assigned to.
   * @return The reference to the modified DBMList. */
  DBMList &preset(const short int x, const short int y){
    for(unsigned int i = 0; i < dbmListVec->size(); i++) {
      DBM *tD = (*dbmListVec)[i];
      tD->preset(x,y);
    }
    isCf = false;
    return *this;
  }


  /** Normalizes the DBMList with respect to the specified
   * constant maxc. This method normalizes by normalizing
   * each DBM in the DBMList with respect to maxc.
   * The resulting DBMList may or may not be in canonical form.
   * @param maxc The maximum constant.
   * @return none
   * @note This only works when the timed automaton is "diagonal-free,"
   * or does not have any clock difference constraints in the automaton. */
  void bound(const int maxc){
    for(unsigned int i = 0; i < dbmListVec->size(); i++) {
      DBM *tD = (*dbmListVec)[i];
      tD->bound(maxc);
    }
    isCf = false;
  }

  /** Converts the calling DBMList to its canonical form. In this
   * code, a DBMList is in canonical form if and only if all of its
   * DBMs are in canonical form (shortest path closure). We also add other
   * constraints for performance. First, we eliminate redundant empty DBMs.
   * This includes all empty DBMs when the DBMList is nonempty.
   * Even if the DBMList is empty, we
   * insist that the DBMList always has at least one DBM (even though an
   * empty list of DBMs is equivalent to an empty clock zone).
   * Second, we do not allow any redundant
   * DBMs. If DBM_i <= DBM_j, DBM_i is deleted. Among other properties,
   * this allows intersection to be an idempotent operation.
   *
   * We keep
   * the definition a bit relaxed to make its implementation easier. We
   * tightened the definition with simplifications when those will reduce
   * the number of DBMs to improve performance.
   * @return None
   * @note This implementation is the Floyd-Warshall Algorithm
   * for all pairs shortest paths on each of the DBMs in the DBMList,
   * followed by some simplifications.*/
  void cf(){
    /* Check that the DBM is in Canonical Form, and
     * do nothing if it is */
    if(isCf){
      return;
    }
    for(unsigned int i = 0; i < dbmListVec->size(); i++) {
      DBM *tD = (*dbmListVec)[i];
      tD->cf();
    }
    /* Now eliminate some redundant unions */
    /* Start with empty unions */
    /* Always keep at least one DBM in the list */
    for(unsigned int i = 0; i < dbmListVec->size(); i++) {
      /* Always keep at least one DBM in the list */
      if((*dbmListVec)[i]->emptiness() && dbmListVec->size() >= 2) {
        DBM * tempDBM = (*dbmListVec)[i];
        dbmListVec->erase(dbmListVec->begin() + i);
        delete tempDBM;
        // The decrease in i is followed by an increase,
        // which insures that no DBM is skipped
        i--;
      }
    }
    /* Now eliminate any DBM contained within another */
    for(unsigned int i = 0; i < dbmListVec->size(); i++) {
      for(unsigned int j = 0; j < dbmListVec->size(); j++) {
        if(i == j) { continue; }
        if(*((*dbmListVec)[i]) <= *((*dbmListVec)[j]) ) {
          /* Remove i: it is unnecessary */
          DBM* tempDBM = (*dbmListVec)[i];
          dbmListVec->erase(dbmListVec->begin() + i);
          delete tempDBM;
          /* Exit loop if only one element to avoid out of bounds checks */
          if(dbmListVec->size() == i) {
            break;
          }
          /* Give proper iteration by resetting j properly */
          j = -1;
        }
      }
    }
    isCf = true; // the DBM is now in Canonical Form
  }

  /** This method changes this DBMList to the empty DBMList with one
   * DBM. This is used for
   * performance enhancements to save constructors to remake a DBMList
   * when a DBMList is decided to become empty. The returned DBMList
   * is in canonical form.
   * @return [None] */
  void makeEmpty() {
    while(dbmListVec->size() > 1) {
      DBM * tempDBM = dbmListVec->back();
      dbmListVec->pop_back();
      delete tempDBM;
    }
    ((*dbmListVec)[0])->makeEmpty();
    isCf = true;
    return;
  }

  /** This checks if DBMList represents an empty region
   * or the empty clock zone. This method assumes the DBMList
   * is in canonical form.
   * @return true: this clock zone is empty, false: otherwise. */
  bool emptiness() const{
    if(dbmListVec->size() == 0) {
      /* Note: we should not get this case since
       * we always keep in one DBM. */
      return true;
    }
    bool isEmpty = true;
    for(unsigned int i = 0; i < dbmListVec->size(); i++) {
      DBM *tD = (*dbmListVec)[i];
      isEmpty = tD->emptiness();
      if(isEmpty == false) {
        return false;
      }
      else {
        /* Remove empty matrix from union since not necessary */
        if(dbmListVec->size() > 1) {
          DBM * tempDBM = (*dbmListVec)[i];
          dbmListVec->erase(dbmListVec->begin() + i);
          delete tempDBM;
          i--;
        }
      }
    }
    return isEmpty;
  }

   /** This converts all finite constraints
   * to <=, making all inequalities non strict by loosening
   * < to <=.
   * The DBMList calling this method is changed.
   * @return None*/
  void closure(){
    for(unsigned int i = 0; i < dbmListVec->size(); i++) {
      DBM *tD = (*dbmListVec)[i];
      tD->closure();
    }
    isCf = false;
  }

  /** This converts all finite constraints
   * to <, making all inequalities strict by tightening
   * <= to <.
   * The DBMList calling this method is changed.
   * @return None*/
  void closureRev(){
    for(unsigned int i = 0; i < dbmListVec->size(); i++) {
      DBM *tD = (*dbmListVec)[i];
      tD->closureRev();
    }
    isCf = false;
  }

  /** This converts all finite upper-bound constraints
   * to <, making all inequalities strict by tightening
   * <= to <, excluding single clock lower-bounds.
   * The DBMList calling this method is changed.
   * @return None*/
  void predClosureRev(){
    for(unsigned int i = 0; i < dbmListVec->size(); i++) {
      DBM *tD = (*dbmListVec)[i];
      tD->predClosureRev();
    }
    isCf = false;
  }


  /** Prints out the DBMList by printing each DBM
   * in (#, op) matrix format. This gives a list of
   * matrices.
   * The # is the integer bound for the constraint,
   * and op is based on the fourth bit. 0: <, 1: <=
   * @return None */
  void print(std::ostream& os) const{
    int dInd = 0;
        for(std::vector<DBM *>::iterator it = dbmListVec->begin();
      it != dbmListVec->end(); it++) {
          os << "DBMList DBM " << dInd << std::endl;
      DBM *tD = *it;
      tD->print(os);
      dInd++;
    }
        os << std::endl;
  }

  /** Print the DBMList, more compactly, as a list of DBMs printed
   * as a list of constraints. The constraints
   * are printed in the order they appear in each matrix, and the DBMs are
   * separated by || (without line breaks).
   * @return none */
  void print_constraint(std::ostream& os) const{
        for(std::vector<DBM *>::iterator it = dbmListVec->begin();
      it != dbmListVec->end(); it++) {
      DBM *tD = *it;
      tD->print_constraint(os);
      if( (it+1) != dbmListVec->end()) {
        os << " || ";
      }
    }
  }

  /** Prints out the constraints in the DBMList, omitting
   * implicit constraints in DBMs in the DBMList (such as x_1 >= 0). Here,
   * implicit constraints are inequalities that do not
   * constrain any values. This does not omit constraints
   * that can be derived from other constraints. The output format
   * is the same as for print_constraint().
   * @return None */
  void print_ExplicitConstraint(std::ostream& os, const std::vector<std::string>& clock_strings) const{
    for(std::vector<DBM *>::iterator it = dbmListVec->begin();
        it != dbmListVec->end(); it++) {
      DBM *tD = *it;
      tD->print_ExplicitConstraint(os, clock_strings);
      if( (it+1) != dbmListVec->end()) {
        os << " || ";
      }
    }
  }

};

/** Stream operator for DBMLists */
inline
std::ostream& operator<<(std::ostream& os, const DBMList& l)
{
    l.print(os);
    return os;
}

#endif //DBMLIST_H
