/** \file DBM.hh
 * The Difference Bound Matrix (DBM) class; a matrix implementation for a clock
 * zone.
 * @author Peter Fontana
 * @author Dezhuang Zhang
 * @author Rance Cleaveland
 * @author Jeroen Keiren
 * @copyright MIT Licence, see the accompanying LICENCE.txt
 * @note Many functions are inlined for better performance.
 */

#ifndef DBM_H
#define DBM_H

#include <cassert>
#include <functional>
#include <iostream>
#include <vector>
#include "OneDIntArray.hh"
#include "bidirectional_map.hh"

typedef short int clock_value_t;

inline
clock_value_t infinity(bool strict)
{
  if(strict) {
    return 0xFFF << 1;
  } else {
    return (0XFFF << 1) + 1;
  }
}

inline
clock_value_t zero(bool strict)
{
  if(strict) {
    return 0x0;
  } else {
    return 0x1;
  }
}

inline
clock_value_t clock_value(clock_value_t val, bool strict)
{
  clock_value_t result = val << 1;
  if(!strict) {
    ++result;
  }
  return result;
}

/** A bitwise vector representing clocks in the Clock Set.
 * Values are stored as bits, and Clock Sets are used in clock resets.
 * @author Peter Fontana, Dezhuang Zhang, and Rance Cleaveland.
 * @note Many functions are inlined for better performance.
 * @version 1.2
 * @date November 2, 2013 */
class ClockSet {
public:
  /** Type for the size of the clock set. */
  typedef std::size_t size_type;

protected:
  /** The number of clocks in the set. */
  size_type num_clocks_;

  /** The size of cc_ */
  size_type size_;

  /** The array of unsigned ints used to store the clock set.  Each integer
   * is treated as a bitvector. Each integer represents a different clock, and
   * different indices represent different clocks. */
  unsigned int *cc_;

  /** Return the index in the internal array corresponding to bit */
  size_type index(const size_type bit) const {
    return bit >> 5;
  }

  /** Compute amount needed to shift */
  size_type shift_amount(const size_type bit) const {
    return bit & 0x1F;
  }

public:
  /** Constructor. Initializes the set of clocks with a specified
   * number of clocks and one dummy "zero clock". The dummy "zero clock"
   * is considered to be the first index, index 0.
   * @param bit The number (index) of the clock to initialize
   * in the set.
   * @param numClocks The number of clocks in the set of clocks. This
   * number does not include the dummy "zero clock".
   * @return [Constructor]. */
  ClockSet(const size_type bit, const size_type numClocks)
    : num_clocks_(numClocks),
      size_(index(num_clocks_) + 1),
      cc_(new unsigned int[size_])
  {
    /* Correction: Initialize elements in ClockSet to 0
     * (empty Clock Set). */
    for (size_type i = 0; i < size_; i++) {
      cc_[i] = 0;
    }
    cc_[index(bit)] = (0x1 << shift_amount(bit));
  }

  /** Copy Constructor.
   * @param Y (&) The object to copy.
   * @return [Constructor]. */
  ClockSet(const ClockSet &Y)
    : num_clocks_(Y.num_clocks_),
      size_(index(num_clocks_)+1),
      cc_(new unsigned int[size_])
  {
    memcpy(cc_, Y.cc_, size_ * sizeof(unsigned int));
  }

  /** Destructor.  Does nothing.
   * @return [Destructor]. */
  ~ClockSet() { delete[] cc_; }

  /** This adds a clock to the clock set.
   * @param bit The index of the clock to add.
   * @return The changed ClockSet object. */
  ClockSet *addclock(const size_type bit) {
    size_type idx = index(bit);
    cc_[idx] = cc_[idx] | (0x1 << shift_amount(bit));
    return this;
  }

  /** Prints out the list of clocks in the set,
   * printint index _ as clock A
   * Here, it goes through the array, and
   * assumes that each clock is A _ index number,
   * printing out which clocks are in them.
   * @param os - the output stream to print to.
   * @return none */
  void print(std::ostream &os) const {
    bool end = false;
    os << "[";
    for (size_type i = 1; i <= num_clocks_; i++) {
      size_type b = shift_amount(i);
      if ((cc_[index(i)] >> b) & 0x1) {
        if (end) {
          os << ",";
        }
        /* Print clocks as x(ind): x1, x2, ...
         * x0, the dummy clock, is not printed. */
        os << "x" << (b);
        end = true;
      }
    }
    os << "]";
  }

  /** Determines if the clock index specified by bit is in
   * the ClockSet.
   * @param bit The index of the clock to see if it is in the
   * ClockSet.
   * @return 1: the clock bit is in the ClockSet; 0: otherwise. */
  unsigned int getc(const size_type bit) const {
    return ((cc_[index(bit)] >> shift_amount(bit)) & 0x1);
  }
};

/**
 * The Difference Bound Matrix (DBM) class; a matrix implementation
 * for a clock zone.
 * Here, the DBM is represented as a numClocks x numClocks matrix
 * where the matrix is represented as a folded 1-D array, with
 * entry (i,j) containing the upper bound constraint on clock constraint
 * x_i - x_j. The 0 clock (which is counted as a clock in numClocks) is
 * is the standard "zero clock" for clock zones.
 * For performance reasons, each clock is represented as a
 * clock_value_t of 13 bits, (#, op). # is the 12-bit non-negative
 * integer value and op is in {<,<=}. For the last (rightmost) bit:
 * 0: <. 1: <=. For the 12-bit integer value, Infinity is represented as 0xFFF.
 * @author Peter Fontana, Dezhuang Zhang, and Rance Cleaveland.
 * @version 1.1
 * @note Many functions are inlined for better performance.
 * @date December 3, 2012. */
class DBM : public OneDIntArray {
private:
  /** True if the DBM is still in canonical form (cf()), false otherwise.
   * This provides a quick a 1-bit check that avoids needless
   * work to convert something already in cf() to cf(). */
  bool isCf;

  /** The Number of clocks in the space for the DBM. This
   * number includes the "zero clock." */
  const size_type nClocks;

  /** Pointer to the globally declared clocks */
  const bidirectional_map<std::string, int> &declared_clocks_;

  size_type offset(const size_type row, const size_type col) const {
    assert(row < nClocks);
    assert(col < nClocks);
    const size_type index = (row * nClocks) + col;
    return index * sizeof(clock_value_t);
  }

  const clock_value_t* cell(const size_type row, const size_type col) const {
    assert(row < nClocks);
    assert(col < nClocks);
    return (clock_value_t*)&(storage[offset(row,col)]);
  }

  clock_value_t* cell(const size_type row, const size_type col) {
    assert(row < nClocks);
    assert(col < nClocks);
    return (clock_value_t *)&(storage[offset(row,col)]);
  }

  /** The private method is used to read a value of a
   * specific constraint in the DBM. This method
   * is private to provide a method without bounds checks. The class is
   * implemented to insure that row and col are not out of bounds before
   * calling these method.
   * @param row The first clock, or the row clock, with 0 being the first row.
   * @param col The second clock, or the column clock,
   * with 0 being the first column.
   * @return The value of the upper bound constraint on row - col. */
  clock_value_t operatorRead(const size_type row, const size_type col) const {
    assert(row < nClocks);
    assert(col < nClocks);
    return *cell(row,col);
  }

  /** The private method is used to write a value to a
   * specific constraint in the DBM (it can also read as well).
   * To write, use operatorWrite(row, col) = val;
   * by returning a reference, this makes writes faster. This method
   * is private to provide a method without bounds checks. The class is
   * implemented to insure that row and col are not out of bounds before
   * calling these method.
   * @param row The first clock, or the row clock, with 0 being the first row.
   * @param col The second clock, or the column clock,
   * with 0 being the first column.
   * @return A reference to the element indexed at the row "row" and column
   * "col". A reference is returned to allow the constraint to be changed. */
  clock_value_t &operatorWrite(const size_type row, const size_type col) {
    assert(row < nClocks);
    assert(col < nClocks);
    /* Indexes are zero based */
    return *cell(row, col);
  }

  /** Performs comparison checks;
   * This is done by doing an elementwise comparison.
   * Only other is required to be in canonical form.
   * @param other (&) The right DBM.
   * @param cmp The elementwise comparison. If cmp fails for some element, the
   * result is false.
   * @return true: cmp succeeds for all elements in elementwise comparison. */
  template<class BinaryPredicate>
  bool compare(const DBM& other, BinaryPredicate cmp) const
  {
    assert(nClocks == other.nClocks);
    for (size_type i = 0; i < nClocks; ++i) {
      for (size_type j = 0; j < nClocks; ++j) {
        if (cmp(this->operatorRead(i, j), other.operatorRead(i, j))) {
          return false;
        }
      }
    }

    return true;
  }

public:
  /** Default Constructor for a DBM; creates an initial DBM
   * representing no constraint: the diagonal and the left column are
   * (0, <=), and the rest of the entries are (infinity, <).
   * This is the loosest possible DBM.
   * @param numClocks The number of clocks, including the one "dummy" \
   * "zero clock". Hence, there are numClocks - 1 actual clocks
   * with 1 "zero" clock.
   * @return [Constructor] */
  DBM(const size_type numClocks, const bidirectional_map<std::string, int> &cs)
      : OneDIntArray(numClocks * numClocks),
        nClocks(numClocks),
        declared_clocks_(cs) {
    assert(nClocks >= 1);
    for (size_type i = 0; i < nClocks; i++) {
      for (size_type j = 0; j < nClocks; j++) {
        this->operatorWrite(i, j) = infinity(true);
        if (i == 0) {
          this->operatorWrite(i, j) = zero(false);
        }
        if (i == j) {
          this->operatorWrite(i, j) = zero(false);
        }
      }
    }

    // Set isCf to false to prevent breaking parser code
    isCf = false;
  }

  /** DBM constructor initializing a DBM constrained by one specified
   * inequality.
   * @param numClocks The number of clocks, including the one "dummy"
   * "zero clock". Hence, there are numClocks - 1 actual clocks
   * with 1 "zero" clock.
   * @param row The first clock in the constraint.
   * @param col The second clock in constraint.
   * @param val The value constraining the upper bound of row - col.
   * @return [Constructor] */
  DBM(const size_type numClocks, const size_type row, const size_type col,
      const clock_value_t val, const bidirectional_map<std::string, int> &cs)
      : OneDIntArray(numClocks * numClocks),
        nClocks(numClocks),
        declared_clocks_(cs) {
    assert(nClocks >= 1);
    for (size_type i = 0; i < nClocks; i++) {
      for (size_type j = 0; j < nClocks; j++) {
        if (i == 0) {
          this->operatorWrite(i, j) = zero(false);
        } else if (i == j) {
          this->operatorWrite(i, j) = zero(false);
        } else {
          this->operatorWrite(i, j) = infinity(true);
        }
      }
    }
    /* Input in the single constraint */
    this->operatorWrite(row, col) = val;

    // Set isCf to false to prevent breaking parser code
    isCf = false;
  }

  /** Copy Constructor for DBMs.
   * @param Y (&) The object to copy.
   * @return [Constructor] */
  DBM(const DBM &Y)
      : OneDIntArray(Y),
        isCf(Y.isCf),
        nClocks(Y.nClocks),
        declared_clocks_(Y.declared_clocks_) {}

  size_type clocks_size() const { return nClocks; }

  const bidirectional_map<std::string, int>& declared_clocks() const {
    return declared_clocks_;
  }

  /** Tell the object that it is not in canonical form.
   * Call this method whenever changing the DBM's value from the outside.
   * Otherwise, cf() will fail to convert the DBM to canonical form.
   * @return None */
  void setIsCfFalse() { isCf = false; }

  /** Returns whether this DBM is in canonical form or not.
   * @return true: the DBM is in canonical form; false: otherwise. */
  bool isInCf() const { return isCf; }

  /** The public method is used to read a value of a
   * specific constraint in the DBM. This method performs out of bounds checks
   * on row and col.
   * @param row The first clock, or the row clock, with 0 being the first row.
   * @param col The second clock, or the column clock,
   * with 0 being the first column.
   * @return The value of the upper bound constraint on row - col. */
  clock_value_t operator()(const size_type row, const size_type col) const {
    // Indexes are zero based
    /* Give out of bounds check for public method */
    if (row >= nClocks || col >= nClocks) {
      // I added that col < 0 to check for the third bound.
      std::cerr << "nClocks : " << nClocks << " row : " << row
                << " col : " << col << std::endl;
      std::cerr << "operator() index out of bounds" << std::endl;
      exit(-1);
    }

    return operatorRead(row,col);
  }

  /** The public method is used to write a value to a
   * specific constraint in the DBM (it can also read as well). Out of bounds
   * checks are performed.
   * @param row The first clock, or the row clock, with 0 being the first row.
   * @param col The second clock, or the column clock,
   * with 0 being the first column.
   * @param val The new 13-bit value for the upper bound of row - col.
   * @return None*/
  void addConstraint(const size_type row, const size_type col,
                     const clock_value_t val) {
    /* Give out of bounds check for public method */
    if (row >= nClocks || col >= nClocks) {
      std::cerr << "nClocks : " << nClocks << " row : " << row
                << " col : " << col << std::endl;
      std::cerr << "addConstraint index out of bounds" << std::endl;
      exit(-1);
    }

    clock_value_t *p = cell(row, col);
    // Dereference p and make assignment
    *p = val;

    isCf = false;
    return;
  }

  /* Returns if the constraint row - col is implicit.
   * Here, an "implicit constraint" means that row - col is not
   * a constraint. This does not determine if this constraint
   * is encoded by other constraints in the structure.
   * @param row The first clock, or the row clock, with 0 being the first row.
   * @param col The second clock, or the column clock,
   * with 0 being the first column.
   * @return true: the constraint is implicit (no constraint),
   * false: otherwise */
  bool isConstraintImplicit(const size_type row, const size_type col) const {
    assert(row < nClocks);
    assert(col < nClocks);
    if (row == 0 || row == col) {
      return (this->operatorRead(row, col)) == zero(false);
    } else {
      return (this->operatorRead(row, col)) == infinity(true);
    }
  }

  /** Performs a deep copy of the DBM.  The DBM calling this method is changed.
   * Preserves canonical form.
   * @param Y (&) The object to copy.
   * @return A reference to the copied object, which is the LHS object. */
  DBM& operator=(const DBM &Y) {
    assert(nClocks == Y.nClocks);
    assert(declared_clocks() == Y.declared_clocks());
    quantity = Y.quantity;
    memcpy(storage, Y.storage, quantity * sizeof(clock_value_t));

    isCf = Y.isCf;
    return *this;
  }

  /** Intersects this DBM with a second DBM by performing the constraint-by-constraint
   * intersections of the DBM. This method does not require DBMs to be in
   * canonical form, and does not preserve canonical form of the DBM. The
   * calling DBM is changed.
   * @param Y (&) The DBM to intersect */
  DBM& intersect(const DBM& Y) {
    assert(nClocks == Y.nClocks);
    /* Should we check for same number of clocks (?)
     * Currently, the code does not. */
    for (size_type i = 0; i < nClocks; i++) {
      for (size_type j = 0; j < nClocks; j++) {
        this->operatorWrite(i, j) =
            (this->operatorRead(i, j) < Y.operatorRead(i, j))
                ? this->operatorRead(i, j)
                : Y.operatorRead(i, j);
      }
    }
    isCf = false;
    return *this;
  }



  /** Performs subset checks;
   * X <= Y if and only if all the constraints of X are at least
   * as tight as Y. (This also assumes that X and Y have the same
   * number of clocks). Since each entry is only an upper bound, this
   * can be done with a <= comparison of each constraint. For this method,
   * only Y is required to be in canonical form.
   * @param Y (&) The right DBM.
   * @return true: *this <= Y; false: otherwise. */
  bool operator<=(const DBM &Y) const {
    return compare(Y, std::greater<clock_value_t>());
  }

  /** Performs superset checks; X >= Y if and only
   * Y <= X.  This method requires that (*this), the calling DBM,
   * is in canonical form.
   * @param Y (&) The right DBM.
   * @return true: the calling DBM is a superset of Y,
   * false: otherwise */
  bool operator>=(const DBM &Y) const {
    return compare(Y, std::less<clock_value_t>());
  }

  /** Performs equality checks;
   * X == Y if and only if all the constraints of X are the same as
   * the constraints as Y.
   * (This also assumes that X and Y have the same
   * number of clocks). Both (*this), the calling DBM, and Y must be
   * in canonical form.
   * @param Y (&) The right DBM
   * @return true: the calling DBM equals Y, false: otherwise. */
  bool operator==(const DBM &Y) const {
    return compare(Y, std::not_equal_to<clock_value_t>());
  }

  /** Checks and returns the relation comparing the calling DBM
   * to Y.
   * @param Y (&) The right DBM.
   * @return An integer specifying the comparison between the
   * calling DBM (X) and the input DBM (Y).  0: X incomparable to Y,
   * 1: X <= Y,  2: X >= Y,  3: X == Y.
   * @note This method assumes that the calling DBM and Y have the same
   * number of clocks. */
  int relation(const DBM &Y) {
    assert(nClocks == Y.nClocks);
    /* Should we check for same number of clocks (?)
     * Currently, the code does not. */
    bool gt = true;
    bool lt = true;
    for (size_type i = 0; i < nClocks; i++) {
      for (size_type j = 0; j < nClocks; j++) {
        gt = gt && (this->operatorRead(i, j) >= Y.operatorRead(i, j));
        lt = lt && (this->operatorRead(i, j) <= Y.operatorRead(i, j));
      }
    }
    if (gt && lt) return 3;
    if (gt) return 2;
    if (lt) return 1;
    return 0;
  }

  /** Performs the time successor operator;
   * sets the upper bound constraints on all individual clocks (except
   * the zero clock) to (infinity, <).
   * This method preserves canonical form.
   * @return The reference to the changed calling DBM. */
  DBM &suc() {
    // We start i at 1 because (0,0) isn't a clock
    for (size_type i = 1; i < nClocks; i++) {
      this->operatorWrite(i, 0) = infinity(true);
    }
    return *this;
  }

  /** The time predecessor operator; returns the clock zone where
   * consisting of all valuations that can elapse
   * (with possibly elapse 0) to the input zone.
   * This method does not preserve canonical form.
   * @return a reference to the modified DBM (which is the called DBM).*/
  DBM &pre() {
    /* i is 0 to be all lower bounds, 0 is fine since the clock (0,0) is
     * always <= 0. */
    /* This version, the version that does not preserve canonical form
     * is used due to a typo in a paper describing a version that does
     * preserve canonical form. */
    for (size_type i = 0; i < nClocks; i++) {
      this->operatorWrite(0, i) = zero(false);
    }
    isCf = false;
    return *this;
  }

  /** Reset a single clock, specified by x, to 0.
   * The final DBM is in canonical form.
   * @param x The clock to reset to 0.
   * @return The reference to the changed, calling resulting DBM. */
  DBM &reset(const size_type x) {
    /* Do out of bounds checking now instead of in methods */
    if (x >= nClocks) {
      std::cerr << "nClocks : " << nClocks << " x : " << x << std::endl;
      std::cerr << "reset(x) clock index out of bounds" << std::endl;
      exit(-1);
    }
    for (size_type i = 0; i < nClocks; i++) {
      /* Code Fix: do not change (x,x), since
       * that seemed to be a typo in the algorithm of the paper */
      if (i != x) {
        /* Since (0,0) is usually zero(false) (<= 0), this method
         * works without having to first set (x,0) and (0,x) to 0*/
        this->operatorWrite(x, i) = this->operatorRead(0, i);
        this->operatorWrite(i, x) = this->operatorRead(i, 0);
      }
    }
    return *this;
  }

  /** Resets all the clocks in the given clock set to $0$.
   * The final DBM is in canonical form.
   * @param rs (*) The set of clocks to reset to 0.
   * @return The reference to the changed, calling resulting DBM. */
  DBM &reset(const ClockSet *const rs) {
    /* This for loop takes the DBM and resets
     * all the specified clocks to reset to
     * 0. */
    for (size_type i = 1; i < nClocks; i++) {
      if (rs->getc(i)) {
        this->reset(i);
      }
    }
    return *this;
  }

  /** Assign the current value to clock y to clock x (x := y). This
   * "resets" the clock x to the value of clock y.
   * @param x The clock to change the value of
   * @param y The clock to reset the first clock to.
   * @return The reference to the changed, calling resulting DBM. */
  DBM &reset(const size_type x, const size_type y) {
    /* Do out of bounds checking now instead of in methods */
    if (x >= nClocks || y >= nClocks) {
      std::cerr << "nClocks : " << nClocks << " x : " << x << " y : " << y
                << std::endl;
      std::cerr << "reset(x,y) clock indices out of bounds" << std::endl;
      exit(-1);
    }
    for (size_type i = 0; i < nClocks; i++)
      if (i != x) {
        this->operatorWrite(x, i) = this->operatorRead(y, i);
        this->operatorWrite(i, x) = this->operatorRead(i, y);
      }
    /* The following two lines are not needed:
     * 	this->operatorWrite(x,y) = zero(false);
     * 	this->operatorWrite(y,x) = zero(false);
     * since they are performed when i = y
     * and i = x is ignored so no need to do first. */
    isCf = false;
    return *this;
  }

  /** Compute the reset predecessor operator, which gives DBM[x |-> 0].
   * This method computes
   * the clock zone z', such that z'[x := 0] = DBM (z' becomes our DBM
   * after x is reset to 0). The DBM needs to be in canonical form before
   * calling this method, and the resulting DBM may not be in canonical form
   * after this operation.
   * @param x The clock that was just reset (after the predecessor zone).
   * @return The reference to the modified DBM. */
  DBM &preset(const size_type x) {
    /* Do out of bounds checking now instead of in methods */
    if (x >= nClocks) {
      std::cerr << "nClocks : " << nClocks << " x : " << x << std::endl;
      std::cerr << "reset(x) clock index out of bounds" << std::endl;
      exit(-1);
    }

    /* Do an emptiness check. If x=0 is not a valid valuation,
     * then return the emptyset.
     * Assumption made: for single clocks, there is never a negative
     * constant used*/
    int tempIntG = this->operatorRead(0, x);
    if ((tempIntG >> 1) < 0 ||
        ((tempIntG >> 1) == 0 && (tempIntG & 0x1) == 0)) {
      // Make an empty DBM
      this->operatorWrite(x, 0) = 0;
      this->operatorWrite(0, x) = 0;
      this->operatorWrite(0, 0) = 0;
      isCf = false;
      return *this;
    }
    int tempIntL = this->operatorRead(x, 0);
    if ((tempIntL >> 1) < 0 ||
        ((tempIntL >> 1) == 0 && (tempIntL & 0x1) == 0)) {
      // Make an empty DBM
      this->operatorWrite(x, 0) = 0;
      this->operatorWrite(0, x) = 0;
      this->operatorWrite(0, 0) = 0;
      isCf = false;
      return *this;
    }

    // If here, the preset is not empty

    // Now flush out difference constraints since they
    // are reset by x
    for (size_type i = 1; i < nClocks; i++) {
      if (i == x) {
        continue;
      }
      this->operatorWrite(x, i) = infinity(true);
      this->operatorWrite(i, x) = this->operatorRead(i, 0);
    }
    this->operatorWrite(x, 0) = infinity(true);
    this->operatorWrite(0, x) = zero(false);
    isCf = false;
    return *this;
  }

  /** Compute the reset predecessor operator, which gives DBM[x |-> 0].
   * This method computes
   * the clock zone z', such that z'[PRS := 0] = DBM (z' becomes our DBM
   * after all clocks in our set PRS are reset to 0).
   * The DBM needs to be in canonical form before
   * calling this method, and the resulting DBM may not be in canonical form
   * after this operation.
   * @param prs (*) The set of clocks just reset (after the predecessor zone).
   * @return The reference to the modified DBM. */
  DBM &preset(const ClockSet *const prs) {
    /* Handle clock difference constraints first. This
     * allows us to use the single-clock constraints
     * already in the DBM */
    for (size_type i = 1; i < nClocks; i++) {
      for (size_type j = 1; j < nClocks; j++) {
        if (i == j) {
          continue;
        }
        /* In all conditions, handle constraint (i,j) here.
         * Constraint (j,i) is handled later. */
        if (prs->getc(i) && prs->getc(j)) {
          /* Note that if we are here for constraint (i,j),
           * we will get here in constraint (j,i) */

          clock_value_t tempInt = this->operatorRead(i, j);
          if ((tempInt >> 1) < 0 ||
              ((tempInt >> 1) == 0 && (tempInt & 0x1) == 0)) {
            // Make an empty DBM
            this->operatorWrite(i, 0) = 0;
            this->operatorWrite(0, i) = 0;
            this->operatorWrite(0, 0) = 0;
            isCf = false;
            return *this;
          }
          // If both clocks are reset then their difference does not matter
          this->operatorWrite(i, j) = infinity(true);
        } else if (prs->getc(i)) {
          if (this->operatorRead(0, j) > this->operatorRead(i, j)) {
            this->operatorWrite(0, j) = this->operatorRead(i, j);
          }
          this->operatorWrite(i, j) = infinity(true);
        } else if (prs->getc(j)) {
          if (this->operatorRead(i, 0) > this->operatorRead(i, j)) {
            this->operatorWrite(i, 0) = this->operatorRead(i, j);
          }
          this->operatorWrite(i, j) = infinity(true);
        }
        // Do nothing if neither clock is reset
      }
    }
    /* Handle Single clock constraints last. */
    for (size_type i = 1; i < nClocks; i++) {
      if (prs->getc(i)) {
        clock_value_t tempIntG = this->operatorRead(0, i);
        // For upper bound constraints, only invalidate if strictly
        // less than 0
        if ((tempIntG >> 1) < 0) {
          // Make an empty DBM
          this->operatorWrite(i, 0) = 0;
          this->operatorWrite(0, i) = 0;
          this->operatorWrite(0, 0) = 0;
          isCf = false;
          return *this;
        }
        clock_value_t tempIntL = this->operatorRead(i, 0);
        if ((tempIntL >> 1) < 0) {
          // Make an empty DBM
          this->operatorWrite(i, 0) = 0;
          this->operatorWrite(0, i) = 0;
          this->operatorWrite(0, 0) = 0;
          isCf = false;
          return *this;
        }

        this->operatorWrite(i, 0) = infinity(true);
        this->operatorWrite(0, i) = zero(false);
      }
    }
    isCf = false;
    return *this;
  }

  /** Compute the reset predecessor operator after the assignment
   * of x to y, which gives DBM[x |-> y].
   * This method computes
   * the clock zone z', such that z'[x := y] = DBM (z' becomes our DBM
   * after x is assigned to the current value of y).
   * The DBM needs to be in canonical form before
   * calling this method, and the resulting DBM may not be in canonical form
   * after this operation.
   * @param x The clock that was just reset (after the predecessor zone).
   * @param y The second clock; the clock whose value x was just assigned to.
   * @return The reference to the modified DBM. */
  DBM &preset(const size_type x, const size_type y) {
    /* Do out of bounds checking now instead of in methods */
    if (x >= nClocks || y >= nClocks) {
      std::cerr << "nClocks : " << nClocks << " x : " << x << " y : " << y
                << std::endl;
      std::cerr << "reset(x,y) clock indices out of bounds" << std::endl;
      exit(-1);
    }
    /* Now compute the preset by relaxing constraints on clock $x$ */
    // Now flush out difference constraints since they
    // are reset by x
    /* First check that it is a valid assignment, and make empty otherwise */
    for (size_type i = 0; i < nClocks; i++) {
      if (i == y || i == x) {
        continue;
      }
      if (this->operatorRead(i, x) < this->operatorRead(i, y)) {
        // Make an empty DBM
        this->operatorWrite(i, 0) = 0;
        this->operatorWrite(0, i) = 0;
        this->operatorWrite(0, 0) = 0;
        isCf = false;
        return *this;
      }
      if (this->operatorRead(x, i) < this->operatorRead(y, i)) {
        // Make an empty DBM
        this->operatorWrite(i, 0) = 0;
        this->operatorWrite(0, i) = 0;
        this->operatorWrite(0, 0) = 0;
        isCf = false;
        return *this;
      }
    }
    for (size_type i = 1; i < nClocks; i++) {
      if (i == x) {
        continue;
      }
      this->operatorWrite(x, i) = infinity(true);
      this->operatorWrite(i, x) = this->operatorRead(i, 0);
    }
    this->operatorWrite(x, 0) = infinity(true);
    this->operatorWrite(0, x) = zero(false);
    isCf = false;
    return *this;
  }

  /** Normalizes the DBM with respect to the specified
   * constant maxc. This method relaxes all constraints
   * outside the maximum constant max.
   * For this method to work propertly,
   * maxc must be at least as large as the maximum constant
   * in any clock constraint (invariant or guard) of the timed
   * automaton or in the formula. This method normalizes a DBM
   * and provides a finite number of coarse states, allowing
   * for termination after a finite number of states.
   * The resulting DBM may or may not be in canonical form.
   * @param maxc The maximum constant.
   * @return none
   * @note This only works when the timed automaton is "diagonal-free,"
   * or does not have any clock difference constraints in the automaton. */
  void bound(const clock_value_t maxc) {
    // Is this method correct (?) Should it also be loosening
    // clock differences based on single clock constraints?
    for (size_type i = 1; i < nClocks; i++) {
      clock_value_t iRow = (this->operatorRead(i, 0) >> 1);
      /* Sets any individual upper bound clock constraint
       * that exceeds the const maxc
       * to infinity, and sets all clock differences involving
       * that clock as the higher clock to infinity */
      if (iRow != 0xFFF && iRow > maxc) {
        this->operatorWrite(i, 0) = infinity(true);
        for (size_type j = 1; j < nClocks; j++) {
          if (i != j) {
            this->operatorWrite(i, j) = infinity(true);
          }
        }
      }
      /* Sets any clock with a lower bound constraint
       * with a lower bound value greater than maxc (that
       * has a max value less than -maxc) to maxc (if not
       * already loosened by an upper-bound constraint) and
       * loosens the relevant clock-difference constraints */
      if (-(this->operatorRead(0, i) >> 1) > maxc) {
        for (size_type j = 0; j < nClocks; j++) {
          if (j != i) {
            if (this->operatorRead(j, 0) >> 1 == 0xFFF) {
              this->operatorWrite(j, i) = infinity(true);

            } else {
              this->operatorWrite(j, i) =
                  ((this->operatorRead(j, 0) >> 1) - maxc) << 1;
            }
          }
        }
      }
    }
    /* Now loosen all the clock-difference constraints
     * that have not already been loosened by single-clock
     * constraints.  This takes all clock pairs
     * that are not infinity (not yet loosened) but
     * looser than the largest clock constant and bounds them
     * with the maximum constraint maxc in both directions,
     * relaxing the bounds. */
    for (size_type i = 1; i < nClocks; i++) {
      for (size_type j = 1; j < nClocks; j++) {
        if ((i != j) && ((this->operatorRead(i, j) >> 1) != 0xFFF)) {
          if ((this->operatorRead(i, j) >> 1) > maxc)
            this->operatorWrite(i, j) = (maxc << 1);
          if (-(this->operatorRead(i, j) >> 1) > maxc)
            /* Considered correction to
             *  this->operatorWrite(i,j) = ((-maxc) << 1);
             * but they seem to be equivalent
             * (via 2's complement implementation
             * of negative binary numbers) and due
             * to potentially losing the sign bit,
             * this remains unchanged. */
            this->operatorWrite(i, j) = -((maxc) << 1);
        }
      }
    }
    isCf = false;
  }

  /** Converts the calling DBM to its canonical form, or
   * its shortest path closure. This method is
   * equivalent to computing all-pairs shortest path on the DBM,
   * if treated as a directed graph.  Canonical form allows a universal
   * representation that makes other operators easier.
   * @return None
   * @note This implementation is the Floyd-Warshall Algorithm
   * for all pairs shortest paths.*/
  void cf() {
    if(!isCf) {
      /* Don't you need to initialize all D(i,i) to (0, \leq) (?)
       * Answer:  For this method, yes.  However, if matrices
       * are initialized properly to $(0, \leq)$, those
       * diagonal cells may never be changed and hence
       * this algorithm will still work correctly. */

      for (size_type k = 0; k < nClocks; ++k) {
        /* Deal with overflow in cf() rather than emptiness() */
        if (k == 2 && this->emptiness()) {
          isCf = true;
          // Make empty DBM
          for (size_type i = 0; i < nClocks; i++) {
            for (size_type j = 0; j < nClocks; j++) {
              this->operatorWrite(i, j) = 0;
            }
          }
          return;
        }
        for (size_type i = 0; i < nClocks; ++i) {
          for (size_type j = 0; j < nClocks; ++j) {
            const clock_value_t wholeVal_ik = operatorRead(i, k);
            const clock_value_t wholeVal_kj = operatorRead(k, j);
            const clock_value_t wholeVal_ij = operatorRead(i, j);
            /* Postive overflow potential here:
             * how to we deal with it?
             * One option: check for >= 0xFFF instead
             * of 0xFFF, but that fixes nothing. */
            clock_value_t val = 0xFFF;
            if ((wholeVal_ik >> 1) != 0xFFF && (wholeVal_kj >> 1) != 0xFFF)
              val = (wholeVal_ik >> 1) + (wholeVal_kj >> 1);

            const clock_value_t origVal = wholeVal_ij >> 1;
            /* Correction by Peter Fontana to check for negative overflow */
            if (val < origVal) {
              // Make D(i,j) = D(i, k) + D(k, j)
              // Gets the < or <= operator correct
              operatorWrite(i, j) = (val << 1) + ((wholeVal_ik & 0x1) & (wholeVal_kj & 0x1));
            } else if (val == origVal && val != 0xFFF) {
                /* Take out infinity comparison and see what happens ...  * Note:
                 * it slows performance, so keep non-overflow check in. */
              operatorWrite(i, j) = (val << 1) + ((wholeVal_ik & 0x1) & (wholeVal_kj & 0x1) &
                                                  (wholeVal_ij & 0x1));
            } // value stays d(i,j) otherwise
          }
        }
      }

      isCf = true; // the DBM is now in Canonical Form
    }
  }

  /** This method changes this DBM to the empty DBM. This is used for
   * performance enhancements to save constructors to remake a DBM
   * when a DBM is decided to become empty. The returned DBM
   * is in canonical form.
   * @return [None] */
  void makeEmpty() {
    for (size_type i = 0; i < nClocks; i++) {
      for (size_type j = 0; j < nClocks; j++) {
        operatorWrite(i, j) = 0x0;
      }
    }
    isCf = true;
    return;
  }

  /** This checks if DBM represents an empty region
   * or the empty clock zone. This method assumes the DBM
   * is in canonical form.
   * @return true: this clock zone is empty, false: otherwise. */
  bool emptiness() const {
    /* O(n) version. This assumes that the DBM is in canonical form.
     * an O(n^2) version was previously used to handle overflow possibilities
     * from a model with different semantics. */
    for (size_type i = 0; i < nClocks; i++) {
      clock_value_t rv = this->operatorRead(i, i);
      if (((rv >> 1) < 0) || (((rv >> 1) == 0) && ((rv & zero(false)) == 0))) {
        return true;
      }
    }

    return false;
  }

  /** Method that determines if the DBM has an upper bound constraint.
   * This is used to use internal methods that avoid bounds checking
   * for faster performance.
   * @return true: the DBM has a single-clock upper bound constraint, false:
   * otherwise. */
  bool hasUpperConstraint() const {
    for (size_type i = 1; i < nClocks; i++) {
      clock_value_t cons = this->operatorRead(i, 0);
      if ((cons >> 1) != 0xFFF) {
        return true;
      }
    }
    return false;
  }

  /** This converts all finite constraints
   * to <=, making all inequalities non strict by loosening
   * < to <=.
   * The DBM calling this method is changed.
   * @return None*/
  void closure() {
    for (size_type i = 0; i < nClocks; i++)
      for (size_type j = 0; j < nClocks; j++) {
        if (i == j) {
          continue;
        }
        if ((this->operatorRead(i, j) >> 1) != 0xFFF) { // if not infinity
          this->operatorWrite(i, j) =
              ((this->operatorRead(i, j) >> 1) << 1) + 1;
        }
      }
  }

  /** This converts all finite constraints
   * to <, making all inequalities strict by tightening
   * <= to <.
   * The DBM calling this method is changed.
   * @return None*/
  void closureRev() {
    for (size_type i = 0; i < nClocks; i++)
      for (size_type j = 0; j < nClocks; j++) {
        if (i == j) {
          continue;
        }
        if ((this->operatorRead(i, j) >> 1) != 0xFFF) { // if not infinity
          this->operatorWrite(i, j) =
              ((this->operatorRead(i, j) >> 1) << 1) + 0;
        }
      }
  }

  /** This converts all finite upper-bound constraints
   * to <, making all inequalities strict by tightening
   * <= to <, excluding single clock lower-bounds.
   * The DBM calling this method is changed.
   * @return None*/
  void predClosureRev() {
    for (size_type i = 1; i < nClocks; i++)
      for (size_type j = 0; j < nClocks; j++) {
        if (i == j) {
          continue;
        }
        if ((this->operatorRead(i, j) >> 1) != 0xFFF) { // if not infinity
          this->operatorWrite(i, j) =
              ((this->operatorRead(i, j) >> 1) << 1) + 0;
        }
      }
  }

  /** Print the DBM, more compactly, as a list of constraints. The constraints
   * are printed in the order they appear in the matrix.
   * @return none */
  void print_constraint(std::ostream &os) const {
    bool end = false;
    bool isAllImplicit = true;
    if (this->emptiness()) {
      os << "EMPTY";
      return;
    }
    for (size_type i = 0; i < nClocks; i++) {
      for (size_type j = 0; j < nClocks; j++) {
        if (i == j) {
          continue;
        }
        clock_value_t val = this->operatorRead(i, j) >> 1;
        if (val == 0xFFF) {
          continue;
        }
        clock_value_t type = this->operatorRead(i, j) & 0x1;
        if (i == 0 && val == 0 && type == 1) {
          continue;
        }
        isAllImplicit = false;
        if (end) {
          os << ",";
        }
        if (i != 0 && j != 0) {
          // os << "x" << (i);
          os << declared_clocks_.reverse_at(i);
          os << "-";
          // os << "x" << (j);
          os << declared_clocks_.reverse_at(j);
        } else if (i == 0) {
          os << declared_clocks_.reverse_at(j);
          if (type == 1)
            os << ">=" << -val;
          else
            os << ">" << -val;
          end = true;
          continue;
        } else if (j == 0) {
          os << declared_clocks_.reverse_at(i);
        }

        if (type == 1) {
          os << "<=" << val;
        } else {
          os << "<" << val;
        }
        end = true;
      }
    }
    if (isAllImplicit) {
      os << "INFTY";
    }
  }
};

/** Stream operator for DBMs */
inline std::ostream &operator<<(std::ostream &os, const DBM &d) {
  d.print_constraint(os);
  return os;
}

#endif // DBM_H
