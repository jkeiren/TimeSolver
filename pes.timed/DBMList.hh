/** \file DBMList.hh
 * A List of Difference Bound Matrices (DBMList); a
 * list (union) of matrices implementation for a union of clock
 * zones.
 * @author Peter Fontana
 * @author Dezhuang Zhang
 * @author Rance Cleaveland
 * @author Jeroen Keiren
 * @copyright MIT Licence, see the accompanying LICENCE.txt
 * @note Many functions are inlined for better performance.
 */

#ifndef DBMLIST_H
#define DBMLIST_H

#include <iostream>
#include <vector>
#include "utilities.hh"
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
  std::vector<DBM *> *dbmListVec;

  const bidirectional_map<std::string, int> &declared_clocks;

  /** The Number of clocks in the space for the DBMList. This
   * number includes the "zero clock." This number is also
   * the same for all DBMs in the DBMList. */
  DBM::size_type nClocks;

  /** Private method that returns the complement of a DBM. This uses
   * the (simple) method of performing a DBM that is the union of all
   * the negated constraints of the DBM. This method is private
   * because it is not needed by the prover.
   * Does not preserve canonical form.
   * @param Y (&) The DBM to complement.
   * @return The complemented DBM, given as a DBMList. */
  DBMList *complementDBM(const DBM &Y) {
    if (Y.emptiness()) {
      return new DBMList(Y.clocks_size(), Y.declared_clocks());
    }
    /* Check for infinity DBM */
    bool hasAConstraint = false;
    DBMList *myList = nullptr;
    for (DBM::size_type i = 0; i < Y.clocks_size(); i++) {
      for (DBM::size_type j = 0; j < Y.clocks_size(); j++) {
        if (!(Y.isConstraintImplicit(i, j))) {
          hasAConstraint = true;
          int tempVal = Y(i, j);
          int tempCons = 0x1;
          if ((tempVal & 0x1) == 0x1) {
            tempCons = 0;
          }
          short int constraintVal = ((-(tempVal >> 1)) << 1) + tempCons;
          DBM tempDBM(nClocks, j, i, constraintVal, declared_clocks);
          if (myList == nullptr) {
            myList = new DBMList(tempDBM);
          } else {
            myList->addDBM(tempDBM);
          }
        }
      }
    }

    if(hasAConstraint) {
      myList->setIsCfFalse();
    } else {
      // Set to Empty DBM
      DBM emptyDBM(Y.clocks_size(), Y.declared_clocks());

      for (DBM::size_type i = 1; i < Y.clocks_size(); i++) {
        emptyDBM.addConstraint(i, 0, 0);
        emptyDBM.addConstraint(0, i, 0);
        emptyDBM.addConstraint(0, 0, 0);
      }
      emptyDBM.cf();
      myList = new DBMList(emptyDBM);
    }

    return myList;
  }

  /* Now eliminate some redundant unions */
  /* Start with empty unions */
  /* Always keep at least one DBM in the list */
  void remove_empty_dbms()
  {
    std::vector<DBM*>::iterator last = std::remove_if(dbmListVec->begin(), dbmListVec->end(), [](const DBM* dbm) { return dbm->emptiness(); });
    if(last == dbmListVec->begin()) {
      ++last;
      assert(dbmListVec->front()->emptiness());
    }
    dbmListVec->erase(last, dbmListVec->end());
    assert(!dbmListVec->empty());
    assert(!dbmListVec->front()->emptiness()||dbmListVec->size()==1);
  }

  void remove_contained_dbms()
  {
    std::vector<DBM*>::iterator first = dbmListVec->begin();
    std::vector<DBM*>::iterator last = dbmListVec->end();

    while (first != last) {
      // if first not included in any other DBM, keep it.
      if(std::any_of(dbmListVec->begin(), last, [&](const DBM* other) { return *first != other && **first <= *other; } ))
      {
        // remove first element
        --last;
        std::swap(*first, *last);
      } else {
        ++first;
      }
    }

    std::for_each(last, dbmListVec->end(), [](DBM* dbm) { delete dbm; });
    dbmListVec->erase(last, dbmListVec->end());
  }

public:
  /** Return the number of DBMs in the DBMList. This is used to
   * determine how many zones are unioned. Knowing if the size
   * is 1 or larger than 1 is critical, since many methods are
   * optimized for a DBMList with one DBM, which is equivalent
   * to a DBM.
   * @return The number of DBMs in the DBMList. */
  std::size_t numDBMs() const { return dbmListVec->size(); }

  /** Return the vector of DBMs. Utilized by other methods to access
   * the DBMs, often to iterate through each DBM.
   * @return The vector storing the DBMs in the DBMList. */
  std::vector<DBM *> *getDBMList() const { return dbmListVec; }

  /** Default Constructor for a DBMList; creates an initial DBMList
   * with one DBM,
   * representing no constraint: the diagonal and the top row are
   * (0, <=), and the rest of the entries are (infinity, <).
   * This is the loosest possible DBM.
   * @param numClocks The number of clocks, including the one "dummy" \
   * "zero clock". Hence, there are numClocks - 1 actual clocks
   * with 1 "zero" clock.
   * @return [Constructor] */
  DBMList(const DBM::size_type numClocks,
          const bidirectional_map<std::string, int> &cs)
      : isCf(false),
        dbmListVec(new std::vector<DBM*>),
        declared_clocks(cs),
        nClocks(numClocks)
  {
    dbmListVec->push_back(new DBM(numClocks, cs));
  }

  /** Copy Constructor for DBMList, making a DBMList representing the
   * DBM.
   * @param Y (&) The object to copy.
   * @return [Constructor] */
  DBMList(const DBM &Y)
      : isCf(Y.isInCf()),
        dbmListVec(new std::vector<DBM*>),
        declared_clocks(Y.declared_clocks()),
        nClocks(Y.clocks_size()) {
    dbmListVec->push_back(new DBM(Y));
  }

  /** Copy Constructor for DBMLists, copying a DBMList.
   * @param Y (&) The object to copy.
   * @return [Constructor] */
  DBMList(const DBMList &Y)
      : isCf(Y.isCf),
        dbmListVec(new std::vector<DBM*>),
        declared_clocks(Y.declared_clocks),
        nClocks(Y.nClocks) {
    // Vector constructor makes a deep copy of the pointers (not of the objects
    // that the pointers point to). Make a deep copy of the DBM objects here
    deep_copy(*dbmListVec, *(Y.getDBMList()));
  }

  DBMList(DBMList&& other) noexcept
    : isCf(std::move(other.isCf)),
      dbmListVec(std::move(other.dbmListVec)),
      declared_clocks(std::move(other.declared_clocks)),
      nClocks(std::move(other.nClocks)) {
    other.dbmListVec = nullptr;
  }

  /** Destructor; deletes each DBM in the DBMList and then deletes the vector.
   * @return [Destructor]. */
  ~DBMList() {
    if (dbmListVec != nullptr) {
      delete_vector_elements(*dbmListVec);
      dbmListVec->clear();
      delete dbmListVec;
    }
  }

  /** Tell the object that it is not in canonical form.
   * Call this method whenever changing the DBMList's value from the outside.
   * Otherwise, cf() will fail to convert the DBMList to canonical form.
   * @return None */
  void setIsCfFalse() {
    isCf = false;
    /* Do I also need to set isCf = false for internal DBMs?
     * I believe I do. */
    std::for_each(dbmListVec->begin(), dbmListVec->end(),
        [](DBM* d){ d->setIsCfFalse(); });
  }

  /** Returns whether this DBMList is in canonical form or not.
   * @return true: the DBMList is in canonical form; false: otherwise. */
  bool isInCf() const { return isCf; }

  /** Union the calling DBMList with DBM Y; perform this by making
   * a deep copy of Y and adding to the list of DBMs.
   * The calling DBMList is changed.
   * Only preserves canonical form of the individual DBMs, not of the list.
   * @param Y (&) The DBM to add to the list of DBMs.
   * @return None. */
  void addDBM(const DBM &Y) {
    dbmListVec->push_back(new DBM(Y));
    isCf = false; // only set isCf to false; individual DBMs are still in Cf.
  }

  void union_(const DBM& other) {
    if(*this <= other) {
      *this = other;
    } else if (!(*this >= other)) { // we really need a union here, since this DBM is not the result yet.
      addDBM(other);
    }
  }

  /** Union the calling DBMList with DBMList Y; perform this by making
   * a deep copy of each DBM in Y and adding to the list of DBMs.
   * The calling DBMList is changed.
   * Only preserves canonical form of the individual DBMs, not of the list.
   * @param Y (&) The DBMList to add to the list of DBMs.
   * @return None. */
  void addDBMList(const DBMList &Y) {
    std::for_each(Y.dbmListVec->begin(), Y.dbmListVec->end(),
        [&](DBM* d){ addDBM(*d); });
  }

  /** Compute the union of the other DBMList with this one, and store the result in
   * the current DBM. Note that this is an optimised version of addDBMList, which does not
   * require the union in case one of the DBMs is included in the other */
  void union_(const DBMList& other) {
    if(*this <= other) {
      *this = other;
    } else if (!(other <= *this)) { // we really need a union here, since this DBM is not the result yet.
      addDBMList(other);
    }
  }

  /** Performs a deep copy of the DBMList.
   * The DBMList calling this method is changed.
   * Preserves canonical form.
   * @param Y (&) The object to copy.
   * @return A reference to the copied object, which is the LHS object. */
  DBMList &operator=(const DBMList &Y) {
    nClocks = Y.nClocks;
    if (dbmListVec->size() == 1 && Y.numDBMs() == 1) {
      *dbmListVec->front() = *Y.getDBMList()->front();
    } else if (Y.numDBMs() == 1) {
      while (dbmListVec->size() > 1) {
        delete dbmListVec->back();
        dbmListVec->pop_back();
      }
      *dbmListVec->front() = *Y.getDBMList()->front();
    } else {
      std::vector<DBM *> *tempList = dbmListVec;
      // Vector constructor makes a deep copy of the pointers (not of the
      // objects that the pointers point to). Make a deep copy of the DBM
      // objects here
      std::vector<DBM *> *currList = Y.getDBMList();
      dbmListVec = new std::vector<DBM *>;
      deep_copy(*dbmListVec, *currList);

      delete_vector_elements(*tempList);
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
  DBMList &operator=(const DBM &Y) {
    nClocks = Y.clocks_size();
    while (dbmListVec->size() > 1) {
      DBM *tempDBM = dbmListVec->back();
      delete tempDBM;
      dbmListVec->pop_back();
    }
    *dbmListVec->front() = Y;

    isCf = Y.isInCf();
    return *this;
  }

  /** Method that returns the complement of a DBMList. This uses
   * the (simple) method of performing a DBM that is the union of all
   * the negated constraints of the DBM, and complementing
   * DBM-by-DBM by converting the complement of the DBMs into
   * disjunctive normal form.
   * Does not preserve canonical form.
   * @return The complemented DBMList, given as a DBMList. */
  DBMList &operator!() {
    std::vector<DBM *> *tempList = dbmListVec;

    if (dbmListVec->size() == 1) {
      DBMList *myTempList = complementDBM(*dbmListVec->front());
      dbmListVec = myTempList->getDBMList();
      // The vector was a shallow copy, so delete the rest of the list
      myTempList->dbmListVec = nullptr;
      delete myTempList;
    } else {
      std::vector<DBMList *> dbmVec;
      dbmVec.reserve(dbmListVec->size());
      for (const DBM* const dbm: *dbmListVec) {
        dbmVec.push_back(complementDBM(*dbm));
      }

      // Vector constructor makes a deep copy of the pointers (not of the
      // objects that the pointers point to). Make a deep copy of the DBM
      // objects here
      std::vector<DBM *> *currList = dbmVec.front()->getDBMList();

      dbmListVec = new std::vector<DBM *>;
      deep_copy(*dbmListVec, *currList);

      cf();
      for (const DBMList* const dbms: dbmVec) {
        intersect(*dbms);
      }
      cf();

      /* Delete dbmVec */
      delete_vector_elements(dbmVec);
      dbmVec.clear();
      // Now delete currList
      currList = nullptr;
    }
    // Now clean up DBMs used
    delete_vector_elements(*tempList);
    tempList->clear();
    delete tempList;

    isCf = false;
    return *this;
  }

  /** Intersects this DBMList with a DBM converting the intersection to
   * disjunctive normal form. This involves intersecting
   * each DBM in the DBMList with the given DBM.
   * This method does not require the DBMList or the DBM to be in
   * canonical form, and does not preserve canonical form of the DBMList. The
   * calling DBMList is changed.
   * @param Y (&) The DBM to intersect
   */
  DBMList& intersect(const DBM& Y) {
    /* This forms a new list by distributing the DBMs */
    std::for_each(dbmListVec->begin(), dbmListVec->end(),
        [&](DBM* d){ d->intersect(Y); });
    isCf = false;
    return *this;
  }

  /** Intersects this DBMList with another by converting the intersection to
   * disjunctive normal form. This involves intersecting
   * DBM by DBM in the list of DBMs.
   * This method does not require the DBMLists to be in
   * canonical form, and does not preserve canonical form of the DBMList. This
   * DBMList is changed.
   * @param Y (&) The DBMList to intersect */
  DBMList& intersect(const DBMList &Y) {
    if (dbmListVec->size() == 1 && Y.numDBMs() == 1) {
      dbmListVec->front()->intersect(*Y.getDBMList()->front());
    } else {
      std::vector<DBM *> *tempList = dbmListVec;
      dbmListVec = new std::vector<DBM *>;
      if (tempList->size() == 1) {
        // Deep copy of DBM to dbmListVec; since the size of the current DBMList
        // is 1, first copy, then intersect each DBM with the (single) DBM in the
        // current list.
        deep_copy(*dbmListVec, *Y.getDBMList());
        for (DBM* dbm: *dbmListVec) {
          dbm->intersect(*tempList->front());
        }
      } else {
        // Build a disjunctive normal form;
        // For example (a || b) && (c || d)
        // is transformed to a && c || a && d || b && c || b && d
        for (const DBM* const dbm1: *tempList) {
          for (const DBM* const dbm2: *Y.dbmListVec) {
            DBM* copyDBM = new DBM(*dbm1);
            copyDBM->intersect(*dbm2);
            dbmListVec->push_back(copyDBM);
          }
        }
      }

      // We have to delete element by element
      // Now delete tempList
      delete_vector_elements(*tempList);
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
  bool operator<=(const DBM &Y) const {
    if(emptiness()) {
    return true;
    } else {
      return std::all_of(dbmListVec->begin(), dbmListVec->end(), [&](const DBM* dbm) { return *dbm <= Y; });
    }
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
  bool operator<=(const DBMList &Y) const {
    if(emptiness()) {
      return true;
    } else if (dbmListVec->size() == 1) {
      return Y >= *dbmListVec->front();
    } else {
    // !Y
      DBMList complement(Y);
      !complement;
      complement.cf();

    // !Y empty, hence X && !Y empty
      if (complement.emptiness()) {
      return true;
      } else {
    // X && !Y
        complement.intersect(*this);
        complement.cf();
        return complement.emptiness();
      }
    }
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
  bool operator>=(const DBM &Y) const {
    if (Y.emptiness()) {
      return true;
    } else if (dbmListVec->size() == 1) {
      return *dbmListVec->front() >= Y;
    } else {
      DBMList complement(*this);
      !complement;
      complement.cf();
      if (complement.emptiness()) {
        return true;
      } else {
        complement.intersect(Y);
        complement.cf();
        return complement.emptiness();
      }
    }
  }

  /** Performs superset checks;
   * X >= Y if and only if Y <= X, which is true if
   * and only if !X && Y is empty.
   * For this method,
   * (*this), the calling DBMList, is required to be in canonical form.
   * @param Y (&) The right DBMList.
   * @return true: *this >= Y; false: otherwise. */
  bool operator>=(const DBMList &Y) const {
    return Y <= *this;
  }

  /** Determines equality of a DBMList and DBM;
   * X == Y if and only if X <= Y && X >= Y. Note that
   * in a DBMList, it might be possible (with our definition
   * of cf() for a DBMList) that a DBMList with more than one
   * DBM may be equal to the DBM. Equality means that the two
   * structures have the same set of clock valuations.
   * @param Y (&) The right DBM
   * @return true: the calling DBMList equals Y, false: otherwise. */
  bool operator==(const DBM &Y) const {
    if (dbmListVec->size() == 1) {
      return *dbmListVec->front() == Y;
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
  bool operator==(const DBMList &Y) const {
    if (dbmListVec->size() == 1) {
      return Y == *dbmListVec->front();
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

    if (gt && lt) return 3;
    if (gt) return 2;
    if (lt) return 1;
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

    if (gt && lt) return 3;
    if (gt) return 2;
    if (lt) return 1;
    return 0;
  }

  /** Performs the time successor operator; this is equivalent
   * to computing the time successor of each DBM in the DBMList.
   * This method preserves canonical form.
   * @return The reference to the changed calling DBMList. */
  DBMList &suc() {
    std::for_each(dbmListVec->begin(), dbmListVec->end(),
        [](DBM* d){ d->suc(); });
    isCf = false;
    return *this;
  }

  /** Performs the time predecessor operator; this is equivalent
   * to computing the time predecessor of each DBM in the DBMList.
   * This method does not preserve canonical form.
   * @return The reference to the changed calling DBMList. */
  DBMList &pre() {
    std::for_each(dbmListVec->begin(), dbmListVec->end(),
        [](DBM* d){ d->pre(); });
    isCf = false;
    return *this;
  }

  /** Reset a single clock, specified by x, to 0, by resetting
   * each DBM in the DBMList.
   * The final DBMList is not in canonical form.
   * @param x The clock to reset to 0.
   * @return The reference to the changed, calling resulting DBMList. */
  DBMList &reset(const DBM::size_type x) {
    std::for_each(dbmListVec->begin(), dbmListVec->end(),
        [&](DBM* d){ d->reset(x); });
    isCf = false;
    return *this;
  }

  /** Resets all the clocks in the given clock set to $0$ by resetting
   * each DBM in the DBMList.
   * The final DBM is not in canonical form.
   * @param rs (*) The set of clocks to reset to 0.
   * @return The reference to the changed, calling resulting DBM. */
  DBMList &reset(const ClockSet *const rs) {
    std::for_each(dbmListVec->begin(), dbmListVec->end(),
        [&](DBM* d){ d->reset(rs); });
    isCf = false;
    return *this;
  }

  /** Assign the current value to clock y to clock x (x := y). This
   * "resets" the clock x to the value of clock y, performing the
   * assignment in each DBM of the DBMList.
   * @param x The clock to change the value of
   * @param y The clock to reset the first clock to.
   * @return The reference to the changed, calling resulting DBMList. */
  DBMList &reset(const DBM::size_type x, const DBM::size_type y) {
    std::for_each(dbmListVec->begin(), dbmListVec->end(),
        [&](DBM* d){ d->reset(x, y); });
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
  DBMList &preset(const DBM::size_type x) {
    std::for_each(dbmListVec->begin(), dbmListVec->end(),
        [&](DBM* d){ d->preset(x); });
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
  DBMList &preset(const ClockSet *const prs) {
    std::for_each(dbmListVec->begin(), dbmListVec->end(),
        [&](DBM* d){ d->preset(prs); });
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
  DBMList &preset(const DBM::size_type x, const DBM::size_type y) {
    std::for_each(dbmListVec->begin(), dbmListVec->end(),
        [&](DBM* d){ d->preset(x, y); });
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
  void bound(const clock_value_t maxc) {
    std::for_each(dbmListVec->begin(), dbmListVec->end(),
        [&](DBM* d){ d->bound(maxc); });
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
  void cf() {
    /* Check that the DBM is in Canonical Form, and
     * do nothing if it is */
    if (!isCf) {
      std::for_each(dbmListVec->begin(), dbmListVec->end(),
          [](DBM* d){ d->cf(); });

      remove_empty_dbms();
      remove_contained_dbms();

      isCf = true; // the DBM is now in Canonical Form
    }
  }

  /** This method changes this DBMList to the empty DBMList with one
   * DBM. This is used for
   * performance enhancements to save constructors to remake a DBMList
   * when a DBMList is decided to become empty. The returned DBMList
   * is in canonical form.
   * @return [None] */
  void makeEmpty() {
    std::for_each(++dbmListVec->begin(), dbmListVec->end(), [](DBM* d) { delete d; });
    dbmListVec->erase(++dbmListVec->begin(), dbmListVec->end());
    dbmListVec->front()->makeEmpty();
    isCf = true;
  }

  /** This checks if DBMList represents an empty region
   * or the empty clock zone. This method assumes the DBMList
   * is in canonical form.
   * @return true: this clock zone is empty, false: otherwise. */
  bool emptiness() const {
    for (std::vector<DBM*>::iterator it = dbmListVec->begin();
         it != dbmListVec->end(); /* ++it omitted due to erase in loop */)
    {
      if (!(*it)->emptiness()) {
        return false;
      } else if(dbmListVec->size() > 1) {
        delete *it;
        it = dbmListVec->erase(it);
      } else {
        ++it;
      }
    }
    return true;
  }

  /** This converts all finite constraints
   * to <=, making all inequalities non strict by loosening
   * < to <=.
   * The DBMList calling this method is changed.
   * @return None*/
  void closure() {
    std::for_each(dbmListVec->begin(), dbmListVec->end(),
        [](DBM* d){ d->closure(); });
    isCf = false;
  }

  /** This converts all finite constraints
   * to <, making all inequalities strict by tightening
   * <= to <.
   * The DBMList calling this method is changed.
   * @return None*/
  void closureRev() {
    std::for_each(dbmListVec->begin(), dbmListVec->end(),
        [](DBM* d){ d->closureRev(); });
    isCf = false;
  }

  /** This converts all finite upper-bound constraints
   * to <, making all inequalities strict by tightening
   * <= to <, excluding single clock lower-bounds.
   * The DBMList calling this method is changed.
   * @return None*/
  void predClosureRev() {
    std::for_each(dbmListVec->begin(), dbmListVec->end(),
        [](DBM* d){ d->predClosureRev(); });
    isCf = false;
  }

  /** Prints out the DBMList by printing each DBM
   * in (#, op) matrix format. This gives a list of
   * matrices.
   * The # is the integer bound for the constraint,
   * and op is based on the fourth bit. 0: <, 1: <=
   * @return None */
  void print(std::ostream &os) const {
    int dInd = 0;
    for (const DBM* const dbm: *dbmListVec) {
      os << "DBMList DBM " << dInd << std::endl
         << *dbm;
      dInd++;
    }
    os << std::endl;
  }

  /** Print the DBMList, more compactly, as a list of DBMs printed
   * as a list of constraints. The constraints
   * are printed in the order they appear in each matrix, and the DBMs are
   * separated by || (without line breaks).
   * @return none */
  void print_constraint(std::ostream &os) const {
    for (std::vector<DBM *>::const_iterator it = dbmListVec->begin();
         it != dbmListVec->end(); it++) {
      (*it)->print_constraint(os);
      if ((it + 1) != dbmListVec->end()) {
        os << " || ";
      }
    }
  }
};

/** Stream operator for DBMLists */
inline std::ostream &operator<<(std::ostream &os, const DBMList &l) {
  l.print_constraint(os);
  return os;
}

#endif // DBMLIST_H
