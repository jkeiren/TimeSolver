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

#include <algorithm>
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
public:
  // types
  typedef DBM                                   value_type;
  typedef std::vector<DBM>::iterator            iterator;
  typedef std::vector<DBM>::const_iterator      const_iterator;
  typedef std::reverse_iterator<iterator>       reverse_iterator;
  typedef std::reverse_iterator<const_iterator> const_reverse_iterator;
  typedef DBM&                                  reference;
  typedef const DBM&                            const_reference;
  typedef std::size_t                           size_type;
  typedef std::ptrdiff_t                        difference_type;

private:
  typedef std::vector<value_type> dbm_list_t;

  /** The list of DBMs; the set of valuations represented is
   * dbms[0] || dbms[1] || ... || dbms[dbms->size()-1]. */
  dbm_list_t* m_dbms;

  const clock_name_to_index_t* m_declared_clocks;

  /** True if the DBM is still in canonical form (cf()), false otherwise.
   * This provides a quick a 1-bit check that avoids needless
   * work to convert something already in cf() to cf(). */
  bool m_is_cf;

  /** Private method that returns the complement of a DBM. This uses
   * the (simple) method of performing a DBM that is the union of all
   * the negated constraints of the DBM. This method is private
   * because it is not needed by the prover.
   * Does not preserve canonical form.
   * @param Y (&) The DBM to complement.
   * @return The complemented DBM, given as a DBMList. */
  void complementDBM(DBMList& out, const DBM& Y) {
    assert(out.emptiness());
    if(Y.emptiness())
    {
      out = DBMList(Y.declared_clocks());
    } else {
      bool first = true;
      if(!Y.emptiness()) {
        for (DBM::size_type i = 0; i < Y.clocks_size(); i++) {
          for (DBM::size_type j = 0; j < Y.clocks_size(); j++) {
            if (!(Y.isConstraintImplicit(i, j))) {
              const DBM negated_dbm(j, i, negate_constraint(Y(i,j)), m_declared_clocks);
              if(first) {
                out.front() = std::move(negated_dbm);
                first = false;
              } else {
                out.addDBM(std::move(negated_dbm));
              }
            }
          }
        }
      }
    }
  }

  /* Now eliminate some redundant unions */
  /* Start with empty unions */
  /* Always keep at least one DBM in the list */
  void remove_empty_dbms()
  {
    iterator last = std::remove_if(begin(), end(), [](const DBM& dbm) { return dbm.emptiness(); });
    if(last == begin()) {
      ++last;
      assert(front().emptiness());
    }
    erase(last, end());
    assert(!empty());
    assert(!front().emptiness()||size()==1);
  }

  void remove_contained_dbms()
  {
    iterator first = begin();
    iterator last = end();

    while (first != last) {
      // if first not included in any other DBM, keep it.
      // The pointer comparison on the address of *first and other is crucial,
      // It ensures that the object is not compared to itself.
      if(std::any_of(begin(), last, [&first](const DBM& other) { return (&(*first) != &other) && *first <= other; } ))
      {
        // remove first element
        --last;
        std::swap(*first, *last);
      } else {
        ++first;
      }
    }
    assert(last != begin());

    erase(last, end());
  }

  std::size_t clocks_size() const { return m_declared_clocks->size()+1; }

  /** Maps f to all DBMs in the list and marks the DBMList as not in cf */
  template<typename F>
  DBMList& map(F f)
  {
    std::for_each(begin(), end(), f);
    m_is_cf = false;
    return *this;
  }

public:
  /** Default Constructor for a DBMList; creates an initial DBMList
   * with one DBM,
   * representing no constraint: the diagonal and the top row are
   * (0, <=), and the rest of the entries are (infinity, <).
   * This is the loosest possible DBM.
   * @return [Constructor] */
  DBMList(const clock_name_to_index_t* cs)
      : m_dbms(new std::vector<DBM>),
        m_declared_clocks(cs),
        m_is_cf(false)
  {
    m_dbms->emplace_back(cs);
  }

  /** Copy Constructor for DBMList, making a DBMList representing the
   * DBM.
   * @param Y (&) The object to copy.
   * @return [Constructor] */
  DBMList(const DBM &Y)
      : m_dbms(new std::vector<DBM>()),
        m_declared_clocks(Y.declared_clocks()),
        m_is_cf(Y.isInCf()) {
    m_dbms->push_back(Y);
  }

  /** Placement constructor, making a DBMList representing the
   * DBM.
   * @param Y (&) The object to copy.
   * @return [Constructor] */
  DBMList(DBM &&Y)
      : m_dbms(new std::vector<DBM>),
        m_declared_clocks(Y.declared_clocks()),
        m_is_cf(Y.isInCf()) {
    m_dbms->push_back(Y);
  }

  /** Copy Constructor for DBMLists, copying a DBMList.
   * @param Y (&) The object to copy.
   * @return [Constructor] */
  DBMList(const DBMList &Y)
      : m_dbms(new std::vector<DBM>),
        m_declared_clocks(Y.m_declared_clocks),
        m_is_cf(Y.m_is_cf) {
    // Vector constructor makes a deep copy of the pointers (not of the objects
    // that the pointers point to). Make a deep copy of the DBM objects here
    *m_dbms = *Y.m_dbms;
  }

  DBMList(DBMList&& other) noexcept
    : m_dbms(std::move(other.m_dbms)),
      m_declared_clocks(std::move(other.m_declared_clocks)),
      m_is_cf(std::move(other.m_is_cf)) {
    other.m_dbms = nullptr;
  }

  /** Destructor; deletes each DBM in the DBMList and then deletes the vector.
   * @return [Destructor]. */
  ~DBMList() {
    if (m_dbms != nullptr) {
      clear();
      delete m_dbms;
      m_dbms = nullptr;
    }
  }

  // iterator support
  iterator begin() { return m_dbms->begin(); }
  iterator end() { return m_dbms->end(); }
  const_iterator begin() const { return m_dbms->begin(); }
  const_iterator end() const { return m_dbms->end(); }

  // Whether the list of DBMs is empty. Note: different from emptiness()
  bool empty() const { return m_dbms->empty(); }

private:
  // reverse iterator support
  reverse_iterator rbegin() { return m_dbms->rbegin(); }
  const_reverse_iterator rbegin() const { return m_dbms->rbegin(); }
  reverse_iterator rend() { return m_dbms->rend(); }
  const_reverse_iterator rend() const { return m_dbms->rend(); }

  // capacity
  size_type size() const { return m_dbms->size(); }

  reference back() { return m_dbms->back(); }
  const_reference back() const { return m_dbms->back(); }
  void push_back(const value_type& val) { m_dbms->push_back(val); }
  void push_back(value_type&& val) { m_dbms->push_back(val); }
  void pop_back() { m_dbms->pop_back(); }
  reference front() { return m_dbms->front(); }
  const_reference front() const { return m_dbms->front(); }

  iterator erase(const_iterator first, const_iterator last) { return m_dbms->erase(first, last); }
  iterator erase(const_iterator position) { return m_dbms->erase(position); }
  void clear() { m_dbms->clear(); }
  void reserve(const size_type n) { m_dbms->reserve(n); }

public:
  /** Tell the object that it is not in canonical form.
   * Call this method whenever changing the DBMList's value from the outside.
   * Otherwise, cf() will fail to convert the DBMList to canonical form.
   * @return None */
  void setIsCfFalse(bool recursive) {
    m_is_cf = false;
    /* Do I also need to set isCf = false for internal DBMs?
     * I believe I do. */
    if(recursive) {
      std::for_each(begin(), end(), [](DBM& d){ d.setIsCfFalse(); });
    }
  }

  /** Returns whether this DBMList is in canonical form or not.
   * @return true: the DBMList is in canonical form; false: otherwise. */
  bool isInCf() const { return m_is_cf; }

  /** Union the calling DBMList with DBM Y; perform this by making
   * a deep copy of Y and adding to the list of DBMs.
   * The calling DBMList is changed.
   * Only preserves canonical form of the individual DBMs, not of the list.
   * @param Y (&) The DBM to add to the list of DBMs.
   * @return None. */
  void addDBM(const DBM &Y) {
    m_dbms->push_back(Y);
    m_is_cf = false; // only set isCf to false; individual DBMs are still in Cf.
  }

  void addDBM(DBM &&Y) {
    m_dbms->push_back(Y);
    m_is_cf = false; // only set isCf to false; individual DBMs are still in Cf.
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
  void addDBMList(const DBMList &other) {
    m_dbms->insert(m_dbms->end(), other.begin(), other.end());
    m_is_cf = false;
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
    if (Y.size() == 1) {
      iterator dbm_it = ++begin();
      erase(dbm_it, end());
      front() = Y.front();
    } else {
      // Vector constructor makes a deep copy of the pointers (not of the
      // objects that the pointers point to). Make a deep copy of the DBM
      // objects here
      clear();
      *m_dbms = *Y.m_dbms;
    }

    m_is_cf = Y.isInCf();
    return *this;
  }

  /** Move assignment */
  DBMList& operator=(DBMList&& other) {
    m_declared_clocks = std::move(other.m_declared_clocks);
    delete m_dbms;
    m_dbms = std::move(other.m_dbms);
    m_is_cf = std::move(other.m_is_cf);
    other.m_dbms = nullptr;
    return *this;
  }

  /** Performs a deep copy of a DBM to a DBMList object.
   * The DBMList calling this method is changed.
   * Preserves canonical form.
   * @param Y (&) The object to copy.
   * @return A reference to the copied object, which is the LHS object. */
  DBMList &operator=(const DBM &Y) {
    erase(++begin(), end());
    front() = Y;
    m_is_cf = Y.isInCf();
    return *this;
  }

  DBMList &operator=(DBM &&Y) {
    erase(++begin(), end());
    front() = std::move(Y);
    m_is_cf = Y.isInCf();
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
    std::vector<DBM> *old_dbms = m_dbms;

    if (size() == 1) {
      DBMList complement_dbms((DBM(m_declared_clocks)));
      complement_dbms.makeEmpty();
      complementDBM(complement_dbms, front());
      m_dbms = std::move(complement_dbms.m_dbms);
      complement_dbms.m_dbms = nullptr;
      m_is_cf = complement_dbms.isInCf();
    } else {
      // Complement the first DBM, and intersect the complement with the complement
      // of all other DBMs.
      std::vector<DBM>::const_iterator dbm_it = old_dbms->begin();
      DBMList first_complement_dbms((DBM(m_declared_clocks)));
      first_complement_dbms.makeEmpty();
      complementDBM(first_complement_dbms, *dbm_it);
      m_dbms = std::move(first_complement_dbms.m_dbms);
      first_complement_dbms.m_dbms = nullptr;
      m_is_cf = first_complement_dbms.isInCf();

      DBMList complement_dbms((DBM(m_declared_clocks)));
      while(++dbm_it != old_dbms->end()) {
        complement_dbms.makeEmpty();
        complementDBM(complement_dbms, *dbm_it);
        intersect(complement_dbms);
      }
      cf(true);
    }
    // Now clean up DBMs used
    old_dbms->clear();
    delete old_dbms;
    old_dbms = nullptr;

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
    return map([&](DBM& d){ d.intersect(Y); });
  }

  /** Intersects this DBMList with another by converting the intersection to
   * disjunctive normal form. This involves intersecting
   * DBM by DBM in the list of DBMs.
   * This method does not require the DBMLists to be in
   * canonical form, and does not preserve canonical form of the DBMList. This
   * DBMList is changed.
   * @param Y (&) The DBMList to intersect */
  DBMList& intersect(const DBMList &Y) {
    if (size() == 1 && Y.size() == 1) {
      front().intersect(Y.front());
    } else {
      std::vector<DBM>* old_dbms = m_dbms;
      m_dbms = new std::vector<DBM>;
      if (old_dbms->size() == 1) {
        // Deep copy of DBM to dbmListVec; since the size of the current DBMList
        // is 1, first copy, then intersect each DBM with the (single) DBM in the
        // current list.
        *m_dbms = *Y.m_dbms;
        for (DBM& dbm: *m_dbms) {
          dbm.intersect(old_dbms->front());
        }
      } else {
        reserve(old_dbms->size() * Y.size());
        // Build a disjunctive normal form;
        // For example (a || b) && (c || d)
        // is transformed to a && c || a && d || b && c || b && d
        for (const DBM& dbm1: *old_dbms) {
          for (const DBM& dbm2: *Y.m_dbms) {
            DBM copyDBM(dbm1);
            copyDBM.intersect(dbm2);
            push_back(copyDBM);
          }
        }
        assert(m_dbms->size()>0);
      }

      // We have to delete element by element
      // Now delete tempList
      old_dbms->clear();
      delete old_dbms;
      old_dbms = nullptr;
    }
    /* This forms a new list by distributing out the intersection */
    /* Should we check for same number of clocks (?)
     * Currently, the code does not. */
    m_is_cf = false;
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
    } else if (Y.emptiness()) {
      assert(!emptiness());
      return false;
    } else {
      return std::all_of(begin(), end(), [&](const DBM& dbm) { return dbm <= Y; });
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
    } else if (Y.emptiness()) {
      assert(!emptiness());
      return false;
    } else if (size() == 1) {
      return Y >= front();
    } else if (Y.size() == 1) {
      return (*this) <= Y.front();
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
    } else if (emptiness()) {
      assert(!Y.emptiness());
      return false;
    } else if (size() == 1) {
      return front() >= Y;
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
    if (size() == 1) {
      return front() == Y;
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
    if (size() == 1) {
      return Y == front();
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
    return map([](DBM& d){ d.suc(); });
  }

  /** Performs the time predecessor operator; this is equivalent
   * to computing the time predecessor of each DBM in the DBMList.
   * This method does not preserve canonical form.
   * @return The reference to the changed calling DBMList. */
  DBMList &pre() {
    return map([](DBM& d){ d.pre(); });
  }

  /** Reset a single clock, specified by x, to 0, by resetting
   * each DBM in the DBMList.
   * The final DBMList is not in canonical form.
   * @param x The clock to reset to 0.
   * @return The reference to the changed, calling resulting DBMList. */
  DBMList &reset(const DBM::size_type x) {
    return map([&](DBM& d){ d.reset(x); });
  }

  /** Resets all the clocks in the given clock set to $0$ by resetting
   * each DBM in the DBMList.
   * The final DBM is not in canonical form.
   * @param rs (*) The set of clocks to reset to 0.
   * @return The reference to the changed, calling resulting DBM. */
  DBMList &reset(const clock_set& rs) {
    return map([&](DBM& d){ d.reset(rs); });
  }

  /** Assign the current value to clock y to clock x (x := y). This
   * "resets" the clock x to the value of clock y, performing the
   * assignment in each DBM of the DBMList.
   * @param x The clock to change the value of
   * @param y The clock to reset the first clock to.
   * @return The reference to the changed, calling resulting DBMList. */
  DBMList &reset(const DBM::size_type x, const DBM::size_type y) {
    return map([&](DBM& d){ d.reset(x, y); });
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
    return map([&](DBM& d){ d.preset(x); });
  }

  /** Compute the reset predecessor operator, which gives DBMList[PRS |-> 0].
   * This method computes the reset predecessor by computing the reset
   * predecessor for each DBM in the DBMList.
   * The DBMList needs to be in canonical form before
   * calling this method, and the resulting DBMList may not be in canonical form
   * after this operation.
   * @param prs (*) The set of clocks just reset (after the predecessor zone).
   * @return The reference to the modified DBMList. */
  DBMList &preset(const clock_set& prs) {
    return map([&](DBM& d){ d.preset(prs); });
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
    return map([&](DBM& d){ d.preset(x, y); });
  }

  /** Normalizes the DBMList with respect to the specified
   * constant maxc. This method normalizes by normalizing
   * each DBM in the DBMList with respect to maxc.
   * The resulting DBMList may or may not be in canonical form.
   * @param maxc The maximum constant.
   * @return none
   * @note This only works when the timed automaton is "diagonal-free,"
   * or does not have any clock difference constraints in the automaton. */
  DBMList& bound(const bound_t maxc) {
    return map([&](DBM& d){ d.bound(maxc); });
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
  void cf(bool no_remove_contained_dbms = false) {
    /* Check that the DBM is in Canonical Form, and
     * do nothing if it is */
    if (!m_is_cf) {
      std::for_each(begin(), end(), [](DBM& d){ d.cf(); });

      remove_empty_dbms();
      if(!no_remove_contained_dbms) {
        remove_contained_dbms();
      }

      m_is_cf = true; // the DBMList is now in Canonical Form
    }
  }

  /** This method changes this DBMList to the empty DBMList with one
   * DBM. This is used for
   * performance enhancements to save constructors to remake a DBMList
   * when a DBMList is decided to become empty. The returned DBMList
   * is in canonical form.
   * @return [None] */
  void makeEmpty() {
    assert(begin() != end());
    erase(++begin(), end());
    front().makeEmpty();
    m_is_cf = true;
  }

  /** This checks if DBMList represents an empty region
   * or the empty clock zone. This method assumes the DBMList
   * is in canonical form.
   * @return true: this clock zone is empty, false: otherwise. */
  bool emptiness() const {
    assert(m_is_cf);
    // since conversion to cf() removes empty DBMs,
    // the list is only empty if the first DBM is empty;
    return front().emptiness();
  }

  /** This converts all finite constraints
   * to <=, making all inequalities non strict by loosening
   * < to <=.
   * The DBMList calling this method is changed.
   * @return None*/
  DBMList& closure() {
    return map([](DBM& d){ d.closure(); });
  }

  /** This converts all finite constraints
   * to <, making all inequalities strict by tightening
   * <= to <.
   * The DBMList calling this method is changed.
   * @return None*/
  DBMList& closureRev() {
    return map([](DBM& d){ d.closureRev(); });
  }

  /** This converts all finite upper-bound constraints
   * to <, making all inequalities strict by tightening
   * <= to <, excluding single clock lower-bounds.
   * The DBMList calling this method is changed.
   * @return None*/
  DBMList& predClosureRev() {
    return map([](DBM& d){ d.predClosureRev(); });
  }

  /** Prints out the DBMList by printing each DBM
   * in (#, op) matrix format. This gives a list of
   * matrices.
   * The # is the integer bound for the constraint,
   * and op is based on the fourth bit. 0: <, 1: <=
   * @return None */
  void print(std::ostream &os) const {
    int dInd = 0;
    for (const DBM& dbm: *m_dbms) {
      os << "DBMList DBM " << dInd << std::endl
         << dbm;
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
    for (const_iterator it = begin(); it != end(); ++it) {
      (*it).print_constraint(os);
      if ((it + 1) != end()) {
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
