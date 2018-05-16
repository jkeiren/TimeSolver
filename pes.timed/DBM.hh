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
#include "array.hh"
#include "bidirectional_map.hh"
#include "constraints.hh"

class ClockSet {
protected:
  std::vector<bool> _data;

public:
  /** Constructor. Initializes the set of clocks with a specified
   * number of clocks and one dummy "zero clock". The dummy "zero clock"
   * is considered to be the first index, index 0.
   * @param bit The number (index) of the clock to initialize
   * in the set.
   * @param num_clocks The number of clocks in the set of clocks. This
   * number does not include the dummy "zero clock".
   * @return [Constructor]. */
  ClockSet(const std::size_t bit, const std::size_t num_clocks)
    : _data(num_clocks + 1, false)
  {
    assert(bit < _data.size());
    _data[bit] = true;
  }

  /** Copy Constructor.
   * @param other (&) The object to copy.
   * @return [Constructor]. */
  ClockSet(const ClockSet &other) = default;

  /** Move Constructor. */
  ClockSet(ClockSet&& other) noexcept = default;

  /** Destructor.  Does nothing.
   * @return [Destructor]. */
  ~ClockSet() { }

  /** This adds a clock to the clock set.
   * @param bit The index of the clock to add.
   * @return The changed ClockSet object. */
  ClockSet *addclock(const std::size_t bit) {
    _data[bit] = true;
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
    for (std::size_t i = 1; i < _data.size(); ++i) {
      if (_data[i]) {
        if (end) {
          os << ",";
        }
        /* Print clocks as x(ind): x1, x2, ...
         * x0, the dummy clock, is not printed. */
        os << "x" << i;
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
  bool getc(const std::size_t bit) const {
    assert(bit < _data.size());
    return _data[bit];
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
 * 0: <. 1: <=. For the 12-bit integer value, Infinity is represented as infinity_bound.
 * @author Peter Fontana, Dezhuang Zhang, and Rance Cleaveland.
 * @version 1.1
 * @note Many functions are inlined for better performance.
 * @date December 3, 2012. */
class DBM : public Array<raw_constraint_t> {
private:
  /** True if the DBM is still in canonical form (cf()), false otherwise.
   * This provides a quick a 1-bit check that avoids needless
   * work to convert something already in cf() to cf(). */
  bool isCf;

  /** Pointer to the globally declared clocks */
  const bidirectional_map<std::string, int> &declared_clocks_;

  size_type offset(const size_type row, const size_type col) const {
    assert(row < clocks_size());
    assert(col < clocks_size());
    const size_type index = (row * clocks_size()) + col;
    return index; // * sizeof(raw_constraint_t);
  }

  const raw_constraint_t* cell(const size_type row, const size_type col) const {
    assert(row < clocks_size());
    assert(col < clocks_size());
    return &at(offset(row,col));
  }

  raw_constraint_t* cell(const size_type row, const size_type col) {
    assert(row < clocks_size());
    assert(col < clocks_size());
    return &(*this)[offset(row,col)];
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
  raw_constraint_t operatorRead(const size_type row, const size_type col) const {
    assert(row < clocks_size());
    assert(col < clocks_size());
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
  raw_constraint_t &operatorWrite(const size_type row, const size_type col) {
    assert(row < clocks_size());
    assert(col < clocks_size());
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
    assert(clocks_size() == other.clocks_size());
    for (size_type i = 0; i < clocks_size(); ++i) {
      for (size_type j = 0; j < clocks_size(); ++j) {
        if (cmp(operatorRead(i, j), other.operatorRead(i, j))) {
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
  DBM(const bidirectional_map<std::string, int> &cs)
      : Array((cs.size()+1) * (cs.size()+1)),
        declared_clocks_(cs) {
    for (size_type i = 0; i < clocks_size(); ++i) {
      for (size_type j = 0; j < clocks_size(); ++j) {
        operatorWrite(i, j) = infinity;
        if (i == 0 || i == j) {
          operatorWrite(i, j) = zero_le;
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
  DBM(const size_type row, const size_type col,
      const raw_constraint_t val, const bidirectional_map<std::string, int> &cs)
      : Array((cs.size()+1) * (cs.size()+1)),
        declared_clocks_(cs) {
    for (size_type i = 0; i < clocks_size(); ++i) {
      for (size_type j = 0; j < clocks_size(); ++j) {
        if (i == 0 || i == j) {
          operatorWrite(i, j) = zero_le;
        } else {
          operatorWrite(i, j) = infinity;
        }
      }
    }
    /* Input in the single constraint */
    operatorWrite(row, col) = val;

    // Set isCf to false to prevent breaking parser code
    isCf = false;
  }

  /** Copy Constructor for DBMs.
   * @param Y (&) The object to copy.
   * @return [Constructor] */
  DBM(const DBM &Y)
      : Array(Y),
        isCf(Y.isCf),
        declared_clocks_(Y.declared_clocks_) {
  }

  DBM(DBM&& other)
    : Array(std::move(other)),
      isCf(std::move(other.isCf)),
      declared_clocks_(std::move(other.declared_clocks_))
  {}

  size_type clocks_size() const { return declared_clocks_.size() + 1; }

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
  raw_constraint_t operator()(const size_type row, const size_type col) const {
    // Indexes are zero based
    /* Give out of bounds check for public method */
    if (row >= clocks_size() || col >= clocks_size()) {
      // I added that col < 0 to check for the third bound.
      std::cerr << "clocks_size() : " << clocks_size() << " row : " << row
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
                     const raw_constraint_t val) {
    /* Give out of bounds check for public method */
    if (row >= clocks_size() || col >= clocks_size()) {
      std::cerr << "clocks_size() : " << clocks_size() << " row : " << row
                << " col : " << col << std::endl;
      std::cerr << "addConstraint index out of bounds" << std::endl;
      exit(-1);
    }

    raw_constraint_t *p = cell(row, col);
    // Dereference p and make assignment
    *p = val;

    isCf = false;
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
    assert(row < clocks_size());
    assert(col < clocks_size());
    if (row == 0 || row == col) {
      return (operatorRead(row, col)) == zero_le;
    } else {
      return (operatorRead(row, col)) == infinity;
    }
  }

  /** Performs a deep copy of the DBM.  The DBM calling this method is changed.
   * Preserves canonical form.
   * @param Y (&) The object to copy.
   * @return A reference to the copied object, which is the LHS object. */
  DBM& operator=(const DBM &Y) {
    assert(clocks_size() == Y.clocks_size());
    assert(declared_clocks() == Y.declared_clocks());
    Array<raw_constraint_t>::operator=(Y);

    isCf = Y.isCf;
    return *this;
  }

  DBM& operator=(DBM&& other) {
    assert(declared_clocks_ == other.declared_clocks_);
    Array<raw_constraint_t>::operator=(other);
    isCf = std::move(other.isCf);
    return *this;
  }

  /** Intersects this DBM with a second DBM by performing the constraint-by-constraint
   * intersections of the DBM. This method does not require DBMs to be in
   * canonical form, and does not preserve canonical form of the DBM. The
   * calling DBM is changed.
   * @param Y (&) The DBM to intersect */
  DBM& intersect(const DBM& Y) {
    assert(clocks_size() == Y.clocks_size());
    if(isCf && emptiness()) {
      return *this;
    } else {
      /* Should we check for same number of clocks (?)
       * Currently, the code does not. */
      for (size_type i = 0; i < clocks_size(); ++i) {
        for (size_type j = 0; j < clocks_size(); ++j) {
          if(Y.operatorRead(i,j) < operatorRead(i,j)) {
            operatorWrite(i,j) = Y.operatorRead(i,j);
            isCf = false;
          }
        }
      }
      return *this;
    }
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
    return compare(Y, std::greater<raw_constraint_t>());
  }

  /** Performs superset checks; X >= Y if and only
   * Y <= X.  This method requires that (*this), the calling DBM,
   * is in canonical form.
   * @param Y (&) The right DBM.
   * @return true: the calling DBM is a superset of Y,
   * false: otherwise */
  bool operator>=(const DBM &Y) const {
    return compare(Y, std::less<raw_constraint_t>());
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
    return compare(Y, std::not_equal_to<raw_constraint_t>());
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
    assert(clocks_size() == Y.clocks_size());
    /* Should we check for same number of clocks (?)
     * Currently, the code does not. */
    bool gt = true;
    bool lt = true;
    for (size_type i = 0; i < clocks_size(); ++i) {
      for (size_type j = 0; j < clocks_size(); ++j) {
        gt = gt && (operatorRead(i, j) >= Y.operatorRead(i, j));
        lt = lt && (operatorRead(i, j) <= Y.operatorRead(i, j));
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
    for (size_type i = 1; i < clocks_size(); ++i) {
      operatorWrite(i, 0) = infinity;
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
    for (size_type i = 0; i < clocks_size(); ++i) {
      operatorWrite(0, i) = zero_le;
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
    if (x >= clocks_size()) {
      std::cerr << "clocks_size() : " << clocks_size() << " x : " << x << std::endl;
      std::cerr << "reset(x) clock index out of bounds" << std::endl;
      exit(-1);
    }
    for (size_type i = 0; i < clocks_size(); ++i) {
      /* Code Fix: do not change (x,x), since
       * that seemed to be a typo in the algorithm of the paper */
      if (i != x) {
        /* Since (0,0) is usually zero_le (<= 0), this method
         * works without having to first set (x,0) and (0,x) to 0*/
        operatorWrite(x, i) = operatorRead(0, i);
        operatorWrite(i, x) = operatorRead(i, 0);
      }
    }
    return *this;
  }

  /** Resets all the clocks in the given clock set to $0$.
   * The final DBM is in canonical form.
   * @param rs (*) The set of clocks to reset to 0.
   * @return The reference to the changed, calling resulting DBM. */
  DBM &reset(const ClockSet& rs) {
    /* This for loop takes the DBM and resets
     * all the specified clocks to reset to
     * 0. */
    for (size_type i = 1; i < clocks_size(); ++i) {
      if (rs.getc(i)) {
        reset(i);
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
    if (x >= clocks_size() || y >= clocks_size()) {
      std::cerr << "clocks_size() : " << clocks_size() << " x : " << x << " y : " << y
                << std::endl;
      std::cerr << "reset(x,y) clock indices out of bounds" << std::endl;
      exit(-1);
    }
    for (size_type i = 0; i < clocks_size(); ++i)
    {
      if (i != x) {
        operatorWrite(x, i) = operatorRead(y, i);
        operatorWrite(i, x) = operatorRead(i, y);
      }
    }
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
    if (x >= clocks_size()) {
      std::cerr << "clocks_size() : " << clocks_size() << " x : " << x << std::endl;
      std::cerr << "reset(x) clock index out of bounds" << std::endl;
      exit(-1);
    }

    /* Do an emptiness check. If x=0 is not a valid valuation,
     * then return the emptyset.
     * Assumption made: for single clocks, there is never a negative
     * constant used*/
    const raw_constraint_t raw_0_x = operatorRead(0, x);
    const bound_t bound_0_x = constraint_to_bound(raw_0_x);
    if (bound_0_x < 0 || (bound_0_x == 0 && constraint_to_strictness(raw_0_x) == strict)) {
      makeEmpty();
      return *this;
    }

    const raw_constraint_t raw_x_0 = operatorRead(x, 0);
    const bound_t bound_x_0 = constraint_to_bound(raw_x_0);
    if (bound_x_0 < 0 || (bound_x_0 == 0 && constraint_to_strictness(raw_x_0) == strict)) {
      makeEmpty();
      return *this;
    }

    // If here, the preset is not empty

    // Now flush out difference constraints since they
    // are reset by x
    for (size_type i = 1; i < clocks_size(); ++i) {
      if (i != x) {
        operatorWrite(x, i) = infinity;
        operatorWrite(i, x) = operatorRead(i, 0);
      }
    }
    operatorWrite(x, 0) = infinity;
    operatorWrite(0, x) = zero_le;
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
  DBM &preset(const ClockSet& prs) {
    /* Handle clock difference constraints first. This
     * allows us to use the single-clock constraints
     * already in the DBM */
    for (size_type i = 1; i < clocks_size(); ++i) {
      for (size_type j = 1; j < clocks_size(); ++j) {
        if (i != j) {
          /* In all conditions, handle constraint (i,j) here.
           * Constraint (j,i) is handled later. */
          if (prs.getc(i) && prs.getc(j)) {
            /* Note that if we are here for constraint (i,j),
             * we will get here in constraint (j,i) */

            const raw_constraint_t raw_i_j = operatorRead(i, j);
            if (constraint_to_bound(raw_i_j) < 0 || raw_i_j == zero_less) {
              makeEmpty();
              return *this;
            }
            // If both clocks are reset then their difference does not matter
            operatorWrite(i, j) = infinity;
          } else if (prs.getc(i)) {
            operatorWrite(0, j) = std::min(operatorRead(0, j), operatorRead(i, j));
            operatorWrite(i, j) = infinity;
          } else if (prs.getc(j)) {
            operatorWrite(i, 0) = std::min(operatorRead(i, 0), operatorRead(i, j));
            operatorWrite(i, j) = infinity;
          } // Do nothing if neither clock is reset
        }

      }
    }
    /* Handle Single clock constraints last. */
    for (size_type i = 1; i < clocks_size(); ++i) {
      if (prs.getc(i)) {
        const raw_constraint_t raw_0_i = operatorRead(0, i);
        // For upper bound constraints, only invalidate if strictly
        // less than 0
        if (constraint_to_bound(raw_0_i) < 0) {
          // Make an empty DBM
          makeEmpty();
          return *this;
        }
        const raw_constraint_t raw_i_0 = operatorRead(i, 0);
        if (constraint_to_bound(raw_i_0) < 0) {
          makeEmpty();
          return *this;
        }

        operatorWrite(i, 0) = infinity;
        operatorWrite(0, i) = zero_le;
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
    if (x >= clocks_size() || y >= clocks_size()) {
      std::cerr << "clocks_size() : " << clocks_size() << " x : " << x << " y : " << y
                << std::endl;
      std::cerr << "reset(x,y) clock indices out of bounds" << std::endl;
      exit(-1);
    }
    /* Now compute the preset by relaxing constraints on clock $x$ */
    // Now flush out difference constraints since they
    // are reset by x
    /* First check that it is a valid assignment, and make empty otherwise */
    for (size_type i = 0; i < clocks_size(); ++i) {
      if (i != y && i != x) {
        if (operatorRead(i, x) < operatorRead(i, y) ||
            operatorRead(x, i) < operatorRead(y, i)) {
          makeEmpty();
          return *this;
        }
      }
    }
    for (size_type i = 1; i < clocks_size(); ++i) {
      if (i != x) {
        operatorWrite(x, i) = infinity;
        operatorWrite(i, x) = operatorRead(i, 0);
      }
    }
    operatorWrite(x, 0) = infinity;
    operatorWrite(0, x) = zero_le;
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
  void bound(const bound_t maxc) {
    // Is this method correct (?) Should it also be loosening
    // clock differences based on single clock constraints?
    for (size_type i = 1; i < clocks_size(); ++i) {
      const bound_t bound_i_0 = constraint_to_bound(operatorRead(i, 0));
      /* Sets any individual upper bound clock constraint
       * that exceeds the const maxc
       * to infinity, and sets all clock differences involving
       * that clock as the higher clock to infinity */
      if (bound_i_0 != infinity_bound && bound_i_0 > maxc) {
        operatorWrite(i, 0) = infinity;
        for (size_type j = 1; j < clocks_size(); ++j) {
          if (i != j) {
            operatorWrite(i, j) = infinity;
          }
        }
      }
      /* Sets any clock with a lower bound constraint
       * with a lower bound value greater than maxc (that
       * has a max value less than -maxc) to maxc (if not
       * already loosened by an upper-bound constraint) and
       * loosens the relevant clock-difference constraints */
      const bound_t bound_0_i = constraint_to_bound(operatorRead(0, i));
      if (-bound_0_i > maxc) {
        for (size_type j = 0; j < clocks_size(); ++j) {
          if (j != i) {
            const raw_constraint_t raw_j_0 = operatorRead(j,0);
            operatorWrite(j, i) = (raw_j_0 == infinity)
                ? infinity
                : bound_to_constraint(constraint_to_bound(raw_j_0) - maxc, strict);
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
    for (size_type i = 1; i < clocks_size(); ++i) {
      for (size_type j = 1; j < clocks_size(); ++j) {
        const bound_t bound_i_j = constraint_to_bound(operatorRead(i, j));
        if (i != j && bound_i_j != infinity_bound) {
          if (bound_i_j > maxc) {
            operatorWrite(i, j) = bound_to_constraint(maxc, strict);
          } else if (-bound_i_j > maxc) {
            /* Considered correction to
             *  operatorWrite(i,j) = ((-maxc) << 1);
             * but they seem to be equivalent
             * (via 2's complement implementation
             * of negative binary numbers) and due
             * to potentially losing the sign bit,
             * this remains unchanged. */
            operatorWrite(i, j) = bound_to_constraint(-maxc, strict);
          }
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

      for (size_type k = 0; k < clocks_size(); ++k) {
        /* Deal with overflow in cf() rather than emptiness() */
        if (k == 2 && this->emptiness()) {
          makeEmpty();
          return;
        }
        for (size_type i = 0; i < clocks_size(); ++i) {
          for (size_type j = 0; j < clocks_size(); ++j) {
            const raw_constraint_t raw_i_k_j = add_constraints(operatorRead(i, k), operatorRead(k, j));
            if (raw_i_k_j < operatorRead(i, j)) {
              operatorWrite(i,j) = raw_i_k_j;
            }
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
    for (size_type i = 0; i < clocks_size(); ++i) {
      for (size_type j = 0; j < clocks_size(); ++j) {
        operatorWrite(i, j) = zero_less;
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
    for (size_type i = 0; i < clocks_size(); ++i) {
      const raw_constraint_t raw_i_i = operatorRead(i, i);
      if (constraint_to_bound(raw_i_i) < 0 || raw_i_i == zero_less) {
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
    for (size_type i = 1; i < clocks_size(); ++i) {
      if (operatorRead(i,0) != infinity) {
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
    for (size_type i = 0; i < clocks_size(); ++i) {
      for (size_type j = 0; j < clocks_size(); ++j) {
        const raw_constraint_t raw_i_j = operatorRead(i, j);
        if (i != j && raw_i_j != infinity) {
          operatorWrite(i, j) = make_constraint_weak(raw_i_j);
        }
      }
    }
  }

  /** This converts all finite constraints
   * to <, making all inequalities strict by tightening
   * <= to <.
   * The DBM calling this method is changed.
   * @return None*/
  void closureRev() {
    for (size_type i = 0; i < clocks_size(); ++i)
      for (size_type j = 0; j < clocks_size(); ++j) {
        const raw_constraint_t raw_i_j = operatorRead(i, j);
        if (i != j && raw_i_j != infinity) {
          operatorWrite(i, j) = make_constraint_strict(raw_i_j);
        }
      }
  }

  /** This converts all finite upper-bound constraints
   * to <, making all inequalities strict by tightening
   * <= to <, excluding single clock lower-bounds.
   * The DBM calling this method is changed.
   * @return None*/
  void predClosureRev() {
    for (size_type i = 1; i < clocks_size(); ++i) // difference with predClosure: start at 1
      for (size_type j = 0; j < clocks_size(); ++j) {
        const raw_constraint_t raw_i_j = operatorRead(i, j);
        if (i != j && raw_i_j != infinity) {
          operatorWrite(i, j) = make_constraint_strict(raw_i_j);
        }
      }
  }

  /** Print the DBM, more compactly, as a list of constraints. The constraints
   * are printed in the order they appear in the matrix.
   * @return none */
  void print_constraint(std::ostream &os) const {
    bool end = false;
    bool isAllImplicit = true;
    if (emptiness()) {
      os << "EMPTY";
      return;
    }
    for (size_type i = 0; i < clocks_size(); ++i) {
      for (size_type j = 0; j < clocks_size(); ++j) {
        if (i == j) {
          continue;
        }
        bound_t val = constraint_to_bound(operatorRead(i, j));
        if (val == infinity_bound) {
          continue;
        }
        strictness_t type = constraint_to_strictness(operatorRead(i, j));
        if (i == 0 && val == 0 && type == weak) {
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
