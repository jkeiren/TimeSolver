/** \file DBM.hh
 * The Difference Bound Matrix (DBM) class; a matrix implementation for a clock
 * zone.
 * @author Peter Fontana, Dezhuang Zhang, and Rance Cleaveland. 
 * @note Many functions are inlined for better performance.
 * @version 1.21
 * @date November 8, 2013 */

#ifndef DBM_H
#define DBM_H

#include <iostream>
#include <vector>
#include "OneDIntArray.hh"
#include "bidirectional_map.hh"

/** A bitwise vector representing clocks in the Clock Set.
 * Values are stored as bits, and Clock Sets are used in clock resets.
 * @author Peter Fontana, Dezhuang Zhang, and Rance Cleaveland. 
 * @note Many functions are inlined for better performance.
 * @version 1.2
 * @date November 2, 2013 */
class ClockSet{
public:
  /** Constructor. Initializes the set of clocks with a specified
   * number of clocks and one dummy "zero clock". The dummy "zero clock"
   * is considered to be the first index, index 0.
   * @param bit The number (index) of the clock to initialize 
   * in the set.
   * @param numClocks The number of clocks in the set of clocks. This
   * number does not include the dummy "zero clock".  
   * @return [Constructor]. */
  ClockSet(const int bit, const int numClocks) : num(numClocks){
    int b = bit & 0x1F;
    int idx = bit >> 5;
    cc = new unsigned int [(numClocks >> 5) + 1];
    /* Correction: Initialize elements in ClockSet to 0
     * (empty Clock Set). */
    for(int i = 0; i < (numClocks >> 5) + 1; i++) {
      cc[i] = 0;
    }
    cc[idx] = (0x1 << b);
  };
  
   /** Copy Constructor. 
   * @param Y (&) The object to copy. 
   * @return [Constructor]. */
  ClockSet(const ClockSet &Y) {
    num = Y.num;
    cc = new unsigned int [(num >> 5) + 1];
     for(int i = 0; i < (num >> 5) + 1; i++) {
      cc[i] = (Y.cc)[i];
    }
  
  }
  
  /** Destructor.  Does nothing.
   * @return [Destructor]. */
  ~ClockSet(){
  	delete []cc;
  };
  
  
  /** This adds a clock to the clock set.
   * @param bit The index of the clock to add.
   * @return The changed ClockSet object. */
  ClockSet * addclock(const int bit){
    int b = bit & 0x1F;
    int idx = bit >> 5;
    cc[idx] = cc[idx] | (0x1 << b);
    return this;
  };
  
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
    for(int i = 1; i <= num; i++){
      int b = i & 0x1F;
      int idx = i >> 5;
      if((cc[idx] >> b)&0x1) {
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
  unsigned int getc(const int bit) const {
    int b = bit & 0x1F;
    int idx = bit >> 5;
    return ((cc[idx] >> b) & 0x1);
  };
protected:
  
  /** The array of unsigned ints used to store the clock set.  Each integer 
   * is treated as a bitvector. Each integerrepresents a different clock, and 
   * different indices represent different clocks. */
  unsigned int *cc;
  /** The number of clocks in the set. */
  int num;
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
 * short int of 13 bits, (#, op). # is the 12-bit non-negative
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

  /** The private method is used to read a value of a
   * specific constraint in the DBM. This method
   * is private to provide a method without bounds checks. The class is 
   * implemented to insure that row and col are not out of bounds before
   * calling these method.
   * @param row The first clock, or the row clock, with 0 being the first row.
   * @param col The second clock, or the column clock, 
   * with 0 being the first column.
   * @return The value of the upper bound constraint on row - col. */
  short int operatorRead(const short int row, const short int col) const {
    /* Indexes are zero based */
    
    // Offsets to one dimentional array
    short int index = (row * nClocks) + col;         
    short int offset = index * sizeof(short int);
    short int *p = (short int*) &(storage[offset]);
    // Dereference p
    return (*p);                           
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
  short int& operatorWrite(const short int row, const short int col) {
    /* Indexes are zero based */
    
    // Offsets to one dimentional array
    short int index = (row * nClocks) + col;         
    short int offset = index * sizeof(short int);
    short int *p = (short int*) &(storage[offset]);
    // Dereference p
    return (*p);                                       
  }
  
protected:

public:
  /** The Number of clocks in the space for the DBM. This
   * number includes the "zero clock." */
  short int nClocks;

  /** Pointer to the globally declared clocks */
  const bidirectional_map<std::string, int>& declared_clocks;
  
  /** Default Constructor for a DBM; creates an initial DBM
   * representing no constraint: the diagonal and the left column are 
   * (0, <=), and the rest of the entries are (infinity, <). 
   * This is the loosest possible DBM.
   * @param numClocks The number of clocks, including the one "dummy" \
   * "zero clock". Hence, there are numClocks - 1 actual clocks 
   * with 1 "zero" clock.
   * @return [Constructor] */
  DBM(const short int numClocks, const bidirectional_map<std::string, int>& cs)
  : OneDIntArray(numClocks * numClocks), nClocks(numClocks), declared_clocks(cs)
  {
    for(short int i = 0; i < nClocks; i++){
      for(short int j = 0; j < nClocks; j++){
        /* Here 0xFFF << 1 = 0xFFF0 is the  
         bit-representation
         Used for (infinity, <). */
        this->operatorWrite(i,j) =  (0xFFF<<1);
        /* 0x1 means (0, <=) , since the left 3-bits
         * represent the integer bound */
        if (i == 0) {
          this->operatorWrite(i,j) =  0x1;
        }
        if (i == j) { 
          this->operatorWrite(i,j) =  0x1;
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
  DBM(const int numClocks, const short int row, const short int col, const short int val,
      const bidirectional_map<std::string, int>& cs)
      : OneDIntArray(numClocks * numClocks), nClocks(numClocks), declared_clocks(cs)
  {
    for(short int i = 0; i < nClocks; i++){
      for(short int j = 0; j < nClocks; j++){
      /* 0x1 means (0, <=) , since the left 3-bits
         * represent the integer bound */
        if (i == 0) {
          this->operatorWrite(i,j) =  0x1;
        }
        else if (i == j) { 
          this->operatorWrite(i,j) =  0x1;
        }
        else {
          /* Here 0xFFF << 1 = 0xFFF0 is the  
          bit-representation
          Used for (infinity, <). */
          this->operatorWrite(i,j) =  (0xFFF<<1);
        }
        
      }
    }
    /* Input in the single constraint */
    this->operatorWrite(row,col) = val;

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
      declared_clocks(Y.declared_clocks)
  {}

  /** Tell the object that it is not in canonical form.
   * Call this method whenever changing the DBM's value from the outside.
   * Otherwise, cf() will fail to convert the DBM to canonical form.
   * @return None */
  void setIsCfFalse() {
    isCf = false;
  }

  /** Returns whether this DBM is in canonical form or not.
   * @return true: the DBM is in canonical form; false: otherwise. */
  bool isInCf() const {
    return isCf;
  }

  /** The public method is used to read a value of a
   * specific constraint in the DBM. This method performs out of bounds checks
   * on row and col.
   * @param row The first clock, or the row clock, with 0 being the first row.
   * @param col The second clock, or the column clock,
   * with 0 being the first column.
   * @return The value of the upper bound constraint on row - col. */
  short int operator() (const short int row, const short int col) const {
    //Indexes are zero based
    /* Give out of bounds check for public method */
    if (row < 0 || row >= nClocks || col >= nClocks || col < 0){
      // I added that col < 0 to check for the third bound.
      std::cerr << "nClocks : " << nClocks << " row : "<<row << " col : "
      << col <<std::endl;
      std::cerr <<  "operator() index out of bounds" <<std::endl; exit(-1);
    }

    // Offsets to one dimentional array
    short int index = (row * nClocks) + col;
    short int offset = index * sizeof(short int);
    short int *p = (short int*) &(storage[offset]);
    // Dereference p
    return (*p);
  }

  /** The public method is used to write a value to a
   * specific constraint in the DBM (it can also read as well). Out of bounds
   * checks are performed.
   * @param row The first clock, or the row clock, with 0 being the first row.
   * @param col The second clock, or the column clock,
   * with 0 being the first column.
   * @param val The new 13-bit value for the upper bound of row - col.
   * @return None*/
  void addConstraint(const short int row, const short int col, const short int val) {
    // Use Version of operator() that allows for a reference
    // But avoid additional method invocation.
    /* Give out of bounds check for public method */
    if (row < 0 || row >= nClocks || col >= nClocks || col < 0){
      // I added that col < 0 to check for the third bound.
      std::cerr << "nClocks : " << nClocks << " row : "<<row << " col : "
      << col <<std::endl;
      std::cerr <<  "operator() index out of bounds" <<std::endl; exit(-1);
    }

    // Offsets to one dimentional array
    short int index = (row * nClocks) + col;
    short int offset = index * sizeof(short int);
    short int *p = (short int*) &(storage[offset]);
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
  bool isConstraintImplicit(const short int row, const short int col) const {
    if(row == 0 || row == col) {
      return (this->operatorRead(row,col)) == 0x1;
    }
    else {
      return (this->operatorRead(row,col)) == (0xFFF << 1);
    }

  }

  /** Performs a deep copy of the DBM.  The DBM calling this method is changed.
   * Preserves canonical form.
   * @param Y (&) The object to copy.
   * @return A reference to the copied object, which is the LHS object. */
  DBM & operator = (const DBM &Y){
    quantity = Y.quantity;
    nClocks = Y.nClocks;
    memcpy(storage, Y.storage, quantity * sizeof(short int));

    isCf = Y.isCf;
    return *this;
  }

  /** Intersects two DBMs by performing the constraint-by-constraint
   * intersections of the DBM. This method does not require DBMs to be in
   * canonical form, and does not preserve canonical form of the DBM. The
   * calling DBM is changed.
   * @param Y (&) The DBM to intersect
   * @return The reference to the intersected DBM (which is the now changed
   * calling DBM). */
  DBM & operator & (const DBM &Y){
    /* Should we check for same number of clocks (?)
     * Currently, the code does not. */
    for(short int i = 0; i < nClocks; i++) {
      for(short int j = 0; j < nClocks; j++) {
        this->operatorWrite(i,j) = (this->operatorRead(i,j) < Y.operatorRead(i,j)) ?
        this->operatorRead(i,j) : Y.operatorRead(i,j) ;
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
  bool operator <= (const DBM &Y){
    /* Change constraint comparison order:
     * 1. First, check all single-clock lower bound constraints.
     * 2. Second, check all single-clock upper bound constraints.
     * 3. Then, check all the clock-difference constraints.
     * In this process, we include checking the diagonals
     * but exclude the cell (0,0). Also note that this
     * code assumes that both DBMs have the same
     * number of clocks. */
    for(short int j = 1; j < nClocks; j++) {
      if (this->operatorRead(0,j) > Y.operatorRead(0,j)) {
        return false;
      }
    }
    for(short int i = 1; i < nClocks; i++) {
      if (this->operatorRead(i,0) > Y.operatorRead(i,0)) {
        return false;
      }
    }
    for(short int i = 1; i < nClocks; i++) {
      for(short int j = 1; j < nClocks; j++) {
        if (this->operatorRead(i,j) > Y.operatorRead(i,j)) {
           return false;
         }
      }
    }

    return true;
  }

  /** Performs superset checks; X >= Y if and only
   * Y <= X.  This method requires that (*this), the calling DBM,
   * is in canonical form.
   * @param Y (&) The right DBM.
   * @return true: the calling DBM is a superset of Y,
   * false: otherwise */
  bool operator >= (const DBM &Y){
    /* Change constraint comparison order:
     * 1. First, check all single-clock lower bound constraints.
     * 2. Second, check all single-clock upper bound constraints.
     * 3. Then, check all the clock-difference constraints.
     * In this process, we include checking the diagonals
     * but exclude the cell (0,0). Also note that this
     * code assumes that both DBMs have the same
     * number of clocks. */
    for(short int j = 1; j < nClocks; j++) {
      if (this->operatorRead(0,j) < Y.operatorRead(0,j)) {
        return false;
      }
    }
    for(short int i = 1; i < nClocks; i++) {
      if (this->operatorRead(i,0) < Y.operatorRead(i,0)) {
        return false;
      }
    }
    for(short int i = 1; i < nClocks; i++) {
      for(short int j = 1; j < nClocks; j++) {
        if (this->operatorRead(i,j) < Y.operatorRead(i,j)) {
           return false;
         }
      }
    }

    return true;
  }

  /** Performs equality checks;
   * X == Y if and only if all the constraints of X are the same as
   * the constraints as Y.
   * (This also assumes that X and Y have the same
   * number of clocks). Both (*this), the calling DBM, and Y must be
   * in canonical form.
   * @param Y (&) The right DBM
   * @return true: the calling DBM equals Y, false: otherwise. */
  bool operator == (const DBM &Y) const {
     /* Change constraint comparison order:
     * 1. First, check all single-clock lower bound constraints.
     * 2. Second, check all single-clock upper bound constraints.
     * 3. Then, check all the clock-difference constraints.
     * In this process, we include checking the diagonals
     * but exclude the cell (0,0). Also note that this
     * code assumes that both DBMs have the same
     * number of clocks. */
    for(short int j = 1; j < nClocks; j++) {
      if (this->operatorRead(0,j) != Y.operatorRead(0,j)) {
        return false;
      }
    }
    for(short int i = 1; i < nClocks; i++) {
      if (this->operatorRead(i,0) != Y.operatorRead(i,0)) {
        return false;
      }
    }
    for(short int i = 1; i < nClocks; i++) {
      for(short int j = 1; j < nClocks; j++) {
        if (this->operatorRead(i,j) != Y.operatorRead(i,j)) {
           return false;
         }
      }
    }

    return true;
  }

  /** Checks and returns the relation comparing the calling DBM
   * to Y.
   * @param Y (&) The right DBM.
   * @return An integer specifying the comparison between the
   * calling DBM (X) and the input DBM (Y).  0: X incomparable to Y,
   * 1: X <= Y,  2: X >= Y,  3: X == Y.
   * @note This method assumes that the calling DBM and Y have the same
   * number of clocks. */
  int relation(const DBM &Y){
    /* Should we check for same number of clocks (?)
     * Currently, the code does not. */
    bool gt = true;
    bool lt = true;
    for(short int i = 0; i < nClocks; i++){
      for(short int j = 0; j < nClocks; j++){
        gt = gt && (this->operatorRead(i,j) >= Y.operatorRead(i,j));
        lt = lt && (this->operatorRead(i,j) <= Y.operatorRead(i,j));
      }
    }
    if(gt && lt) return 3;
    if(gt) return 2;
    if(lt) return 1;
    return 0;
  }



  /** Performs the time successor operator;
   * sets the upper bound constraints on all individual clocks (except
   * the zero clock) to (infinity, <).
   * This method preserves canonical form.
   * @return The reference to the changed calling DBM. */
  DBM & suc(){
    // We start i at 1 because (0,0) isn't a clock
    for(short int i = 1; i < nClocks; i++) {
      this->operatorWrite(i,0) = (0xFFF << 1);
    }
    return *this;
  }

  /** The time predecessor operator; returns the clock zone where
   * consisting of all valuations that can elapse
   * (with possibly elapse 0) to the input zone.
   * This method does not preserve canonical form.
   * @return a reference to the modified DBM (which is the called DBM).*/
  DBM & pre(){
    /* i is 0 to be all lower bounds, 0 is fine since the clock (0,0) is
     * always <= 0. */
    /* This version, the version that does not preserve canonical form
     * is used due to a typo in a paper describing a version that does
     * preserve canonical form. */
    for(short int i = 0; i < nClocks; i++){
      this->operatorWrite(0,i) = 0x1;
    }
    isCf = false;
    return *this;
  }

  /** Reset a single clock, specified by x, to 0.
   * The final DBM is in canonical form.
   * @param x The clock to reset to 0.
   * @return The reference to the changed, calling resulting DBM. */
  DBM & reset(const short int x){
    /* Do out of bounds checking now instead of in methods */
    if (x < 0 || x >= nClocks){
      std::cerr << "nClocks : " << nClocks << " x : "<< x <<std::endl;
      std::cerr <<  "reset(x) clock index out of bounds" <<std::endl; exit(-1);
    }
    for(short int i = 0; i < nClocks; i++){
      /* Code Fix: do not change (x,x), since
       * that seemed to be a typo in the algorithm of the paper */
      if(i != x) {
        /* Since (0,0) is usually 0x1 (<= 0), this method
         * works without having to first set (x,0) and (0,x) to 0*/
        this->operatorWrite(x,i) = this->operatorRead(0,i);
        this->operatorWrite(i,x) = this->operatorRead(i,0);
      }
    }
    return *this;
  }

  /** Resets all the clocks in the given clock set to $0$.
   * The final DBM is in canonical form.
   * @param rs (*) The set of clocks to reset to 0.
   * @return The reference to the changed, calling resulting DBM. */
  DBM &reset(const ClockSet * const rs) {
    /* This for loop takes the DBM and resets
     * all the specified clocks to reset to
     * 0. */
    for(int i = 1; i < nClocks; i++) {
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
  DBM &reset(const short int x, const short int y){
    /* Do out of bounds checking now instead of in methods */
    if (x < 0 || x >= nClocks || y >= nClocks || y < 0){
      std::cerr << "nClocks : " << nClocks << " x : "<< x << " y : "
      << y <<std::endl;
      std::cerr <<  "reset(x,y) clock indices out of bounds" <<std::endl; exit(-1);
    }
    for(short int i = 0; i < nClocks; i++)
      if (i != x) {
        this->operatorWrite(x,i) = this->operatorRead(y,i);
        this->operatorWrite(i,x) = this->operatorRead(i,y);
      }
    /* The following two lines are not needed:
     * 	this->operatorWrite(x,y) = 0x1;
     * 	this->operatorWrite(y,x) = 0x1;
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
  DBM &preset(const short int x){
    /* Do out of bounds checking now instead of in methods */
    if (x < 0 || x >= nClocks){
      std::cerr << "nClocks : " << nClocks << " x : "<< x <<std::endl;
      std::cerr <<  "reset(x) clock index out of bounds" <<std::endl; exit(-1);
    }

    /* Do an emptiness check. If x=0 is not a valid valuation,
     * then return the emptyset.
     * Assumption made: for single clocks, there is never a negative
     * constant used*/
    int tempIntG = this->operatorRead(0,x);
    if((tempIntG >> 1) < 0 || ((tempIntG >> 1) == 0 && (tempIntG & 0x1) == 0)) {
      // Make an empty DBM
      this->operatorWrite(x,0) = 0;
      this->operatorWrite(0,x) = 0;
      this->operatorWrite(0,0) = 0;
      isCf = false;
      return *this;
    }
    int tempIntL = this->operatorRead(x,0);
    if((tempIntL >> 1) < 0 || ((tempIntL >> 1) == 0 && (tempIntL & 0x1) == 0)) {
      // Make an empty DBM
      this->operatorWrite(x,0) = 0;
      this->operatorWrite(0,x) = 0;
      this->operatorWrite(0,0) = 0;
      isCf = false;
      return *this;
    }

    // If here, the preset is not empty

    // Now flush out difference constraints since they
    // are reset by x
    for(short int i=1; i<nClocks; i++){
      if(i == x) {
        continue;
      }
      this->operatorWrite(x,i) = 0xFFF << 1;
      this->operatorWrite(i,x) = this->operatorRead(i,0);
    }
    this->operatorWrite(x,0) = 0xFFF << 1;
    this->operatorWrite(0,x) = 0x1;
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
  DBM &preset(const ClockSet * const prs){

    /* Handle clock difference constraints first. This
     * allows us to use the single-clock constraints
     * already in the DBM */
    for(int i = 1; i < nClocks; i++) {
      for(int j = 1; j < nClocks; j++) {
        if(i == j) { continue; }
        /* In all conditions, handle constraint (i,j) here.
         * Constraint (j,i) is handled later. */
        if (prs->getc(i) && prs->getc(j)) {
          /* Note that if we are here for constraint (i,j),
           * we will get here in constraint (j,i) */

          int tempInt = this->operatorRead(i,j);
          if((tempInt >> 1) < 0 || ((tempInt >> 1) == 0 && (tempInt & 0x1) == 0)) {
            // Make an empty DBM
            this->operatorWrite(i,0) = 0;
            this->operatorWrite(0,i) = 0;
            this->operatorWrite(0,0) = 0;
            isCf = false;
            return *this;
          }
          // If both clocks are reset then their difference does not matter
          this->operatorWrite(i,j) = 0xFFF << 1;
        }
        else if(prs->getc(i)) {
          if(this->operatorRead(0,j) > this->operatorRead(i,j)) {
            this->operatorWrite(0,j) = this->operatorRead(i,j);
          }
          this->operatorWrite(i,j) = 0xFFF << 1;
        }
        else if(prs->getc(j)) {
          if(this->operatorRead(i,0) > this->operatorRead(i,j)) {
            this->operatorWrite(i,0) = this->operatorRead(i,j);
          }
          this->operatorWrite(i,j) = 0xFFF << 1;
        }
        // Do nothing if neither clock is reset
      }
    }
    /* Handle Single clock constraints last. */
    for(int i = 1; i < nClocks; i++) {
      if(prs->getc(i)) {
        int tempIntG = this->operatorRead(0,i);
        // For upper bound constraints, only invalidate if strictly
        // less than 0
        if((tempIntG >> 1) < 0) {
          // Make an empty DBM
          this->operatorWrite(i,0) = 0;
          this->operatorWrite(0,i) = 0;
          this->operatorWrite(0,0) = 0;
          isCf = false;
          return *this;
        }
        int tempIntL = this->operatorRead(i,0);
        if((tempIntL >> 1) < 0) {
          // Make an empty DBM
          this->operatorWrite(i,0) = 0;
          this->operatorWrite(0,i) = 0;
          this->operatorWrite(0,0) = 0;
          isCf = false;
          return *this;
        }

        this->operatorWrite(i,0) = 0xFFF << 1;
        this->operatorWrite(0,i) = 0x1;

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
  DBM &preset(const short int x, const short int y){
    /* Do out of bounds checking now instead of in methods */
    if (x < 0 || x >= nClocks || y >= nClocks || y < 0){
      std::cerr << "nClocks : " << nClocks << " x : "<< x << " y : "
      << y <<std::endl;
      std::cerr <<  "reset(x,y) clock indices out of bounds" <<std::endl;
      exit(-1);
    }
    /* Now compute the preset by relaxing constraints on clock $x$ */
      // Now flush out difference constraints since they
    // are reset by x
    /* First check that it is a valid assignment, and make empty otherwise */
    for(short int i = 0; i < nClocks; i++) {
      if(i==y || i == x) { continue; }
      if(this->operatorRead(i,x) < this->operatorRead(i,y)) {
        // Make an empty DBM
        this->operatorWrite(i,0) = 0;
        this->operatorWrite(0,i) = 0;
        this->operatorWrite(0,0) = 0;
        isCf = false;
        return *this;
      }
      if(this->operatorRead(x,i) < this->operatorRead(y,i)) {
        // Make an empty DBM
        this->operatorWrite(i,0) = 0;
        this->operatorWrite(0,i) = 0;
        this->operatorWrite(0,0) = 0;
        isCf = false;
        return *this;
      }
    }
    for(short int i=1; i<nClocks; i++){
      if(i == x) { continue; }
      this->operatorWrite(x,i) = 0xFFF << 1;
      this->operatorWrite(i,x) = this->operatorRead(i,0);
    }
    this->operatorWrite(x,0) = 0xFFF << 1;
    this->operatorWrite(0,x) = 0x1;
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
  void bound(const int maxc){
    // Is this method correct (?) Should it also be loosening
    // clock differences based on single clock constraints?
    for (short int i = 1; i < nClocks; i++){
      short int iRow = (this->operatorRead(i,0) >> 1);
      /* Sets any individual upper bound clock constraint
       * that exceeds the const maxc
       * to infinity, and sets all clock differences involving
       * that clock as the higher clock to infinity */
      if (iRow != 0xFFF && iRow > maxc){
        this->operatorWrite(i,0) = (0xFFF << 1);
        for(short int j = 1; j < nClocks; j++){
          if(i != j) {
            this->operatorWrite(i,j) = (0xFFF << 1);
          }
        }
      }
      /* Sets any clock with a lower bound constraint
       * with a lower bound value greater than maxc (that
       * has a max value less than -maxc) to maxc (if not
       * already loosened by an upper-bound constraint) and
       * loosens the relevant clock-difference constraints */
      if (-(this->operatorRead(0,i) >> 1) > maxc){
        for(short int j = 0; j < nClocks; j++){
          if (j != i) {
            if (this->operatorRead(j,0) >> 1 == 0xFFF) {
              this->operatorWrite(j,i) = (0xFFF << 1);

            }
            else {
              this->operatorWrite(j,i) = ((this->operatorRead(j,0) >> 1) - maxc) << 1;
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
    for (short int i = 1; i < nClocks; i++){
      for (short int j = 1; j < nClocks; j++){
        if((i != j) && ((this->operatorRead(i,j) >> 1) != 0xFFF) ){
          if ((this->operatorRead(i,j) >> 1) > maxc)
            this->operatorWrite(i,j) = (maxc << 1);
          if (-(this->operatorRead(i,j) >> 1) > maxc)
          /* Considered correction to
           *  this->operatorWrite(i,j) = ((-maxc) << 1);
           * but they seem to be equivalent
           * (via 2's complement implementation
           * of negative binary numbers) and due
           * to potentially losing the sign bit,
           * this remains unchanged. */
            this->operatorWrite(i,j) = -((maxc) << 1);
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
  void cf(){

    /* Check that the DBM is in Canonical Form, and
     * do nothing if it is */
    if(isCf){
      return;
    }

    /* Don't you need to initialize all D(i,i) to (0, \leq) (?)
     * Answer:  For this method, yes.  However, if matrices
     * are initialized properly to $(0, \leq)$, those
     * diagonal cells may never be changed and hence
     * this algorithm will still work correctly. */

    int val;
    short int origVal;
    short int wholeVal_ik;
    short int wholeVal_kj;
    short int wholeVal_ij;
    for(short int k = 0; k < nClocks; k++){
      /* Deal with overflow in cf() rather than emptiness() */
      if(k==2 && this->emptiness()) {
        isCf=true;
        // Make empty DBM
        for(short int i = 0; i < nClocks; i++) {
          for(short int j = 0; j < nClocks; j++) {
            this->operatorWrite(i,j) = 0;
          }
        }
        return;
      }
      for(short int i = 0; i < nClocks; i++){
        for(short int j = 0; j < nClocks; j++){
          wholeVal_ik = this->operatorRead(i,k);
          wholeVal_kj = this->operatorRead(k,j);
          wholeVal_ij = this->operatorRead(i,j);
          /* Postive overflow potential here:
           * how to we deal with it?
           * One option: check for >= 0xFFF instead
           * of 0xFFF, but that fixes nothing. */
          if((wholeVal_ik >> 1) == 0xFFF ||
             (wholeVal_kj >> 1) == 0xFFF)
            val = 0xFFF;
          else
            val = (wholeVal_ik >> 1)
            + (wholeVal_kj >> 1);
          // Changed code to fix operator when value == added
          // with a possible change in constraint
          origVal = wholeVal_ij >> 1;
          if(val <= origVal ){
            /* Correction by Peter Fontana to check for negative overflow */
            if(val < origVal) { // val < so take only those operators
              // Make D(i,j) = D(i, k) + D(k, j)
              this->operatorWrite(i,j) = (val << 1)
              // Gets the < or <= operator correct
              + ((wholeVal_ik & 0x1) & (wholeVal_kj & 0x1)) ;
            }
            /* Correction by Peter Fontana to improve
             * performance */
            else if (val != 0xFFF){
              /* Take out infinity comparison and see what happens ...  * Note: it slows performance, so keep non-overflow
               * check in. */
              this->operatorWrite(i,j) = (val << 1)
              + ((wholeVal_ik & 0x1) & (wholeVal_kj & 0x1) &
                 (wholeVal_ij & 0x1)) ;
            }      // value stays d(i,j) otherwise

          }      // value stays d(i,j) otherwise
        }
      }
    }


    isCf = true; // the DBM is now in Canonical Form

  }

  /** This method changes this DBM to the empty DBM. This is used for
   * performance enhancements to save constructors to remake a DBM
   * when a DBM is decided to become empty. The returned DBM
   * is in canonical form.
   * @return [None] */
  void makeEmpty() {
    for(short int i = 0; i < nClocks; i++){
      for(short int j = 0; j < nClocks; j++){
        this->operatorWrite(i,j) = 0x0;
      }
    }
    isCf = true;
    return;
  }

  /** This checks if DBM represents an empty region
   * or the empty clock zone. This method assumes the DBM
   * is in canonical form.
   * @return true: this clock zone is empty, false: otherwise. */
  bool emptiness() const{
    /* O(n) version. This assumes that the DBM is in canonical form.
     * an O(n^2) version was previously used to handle overflow possibilities
     * from a model with different semantics. */
    for(int i = 0; i < nClocks; i++) {
      short int rv = this->operatorRead(i,i);
      if( ((rv >> 1) < 0) ||
      (((rv >> 1) == 0) && ((rv&0x1) == 0)) ) {
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
    for(int i = 1; i < nClocks; i++) {
      int cons = this->operatorRead(i,0);
      if((cons >> 1) != 0xFFF) {
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
  void closure(){
    for(short int i = 0; i < nClocks; i++)
      for(short int j = 0; j < nClocks; j++){
        if (i==j) {
          continue;
        }
        if((this->operatorRead(i,j) >> 1) != 0xFFF) { // if not infinity
          this->operatorWrite(i,j) = ((this->operatorRead(i,j)>>1) << 1) + 1;
        }
      }
  }

  /** This converts all finite constraints
   * to <, making all inequalities strict by tightening
   * <= to <.
   * The DBM calling this method is changed.
   * @return None*/
  void closureRev(){
    for(short int i = 0; i < nClocks; i++)
      for(short int j = 0; j < nClocks; j++){
        if (i==j) {
          continue;
        }
        if((this->operatorRead(i,j) >> 1) != 0xFFF) { // if not infinity
          this->operatorWrite(i,j) = ((this->operatorRead(i,j)>>1) << 1) + 0;
        }
      }
  }

  /** This converts all finite upper-bound constraints
   * to <, making all inequalities strict by tightening
   * <= to <, excluding single clock lower-bounds.
   * The DBM calling this method is changed.
   * @return None*/
  void predClosureRev(){
    for(short int i = 1; i < nClocks; i++)
      for(short int j = 0; j < nClocks; j++){
        if (i==j) {
          continue;
        }
        if((this->operatorRead(i,j) >> 1) != 0xFFF) { // if not infinity
          this->operatorWrite(i,j) = ((this->operatorRead(i,j)>>1) << 1) + 0;
        }
      }
  }

  /** Prints out the DBM in (#, op) matrix format.
   * The # is the integer bound for the constraint,
   * and op is based on the fourth bit. 0: <, 1: <=
   * @return None */
  void print(std::ostream& os) const{
    for(short int i = 0; i < nClocks; i++){
      for(short int j = 0; j < nClocks; j++){
        short int val = this->operatorRead(i,j) >> 1;
        short int type = this->operatorRead(i,j) & 0x1;
        if (type == 1){
          if (val == 0xFFF)
            os << "(" << "+inf" << "," << "<=)\t";
          else
            os << "( " << val << "," << "<= )\t";
        }else{
          if (val == 0xFFF)
            os << "(" << "+inf" << "," << "<)\t";
          else
            os << "( " << val << "," << "<  )\t";
        }
      }
            os << std::endl;
    }
  }

  /** Print the DBM, more compactly, as a list of constraints. The constraints
   * are printed in the order they appear in the matrix.
   * @return none */
  void print_constraint(std::ostream& os) const{
    bool end = false;
    bool isAllImplicit=true;
    if(this->emptiness()) {
      os << "EMPTY";
      return;
    }
    for(short int i = 0; i < nClocks; i++){
      for(short int j = 0; j < nClocks; j++){
        if(i==j) {
          continue;
        }
        short int val = this->operatorRead(i,j) >> 1;
        if (val == 0xFFF) {
          continue;
        }
        short int type = this->operatorRead(i,j) & 0x1;
        if(i==0 && val == 0 && type == 1) {
            continue;
        }
        isAllImplicit=false;
        if(end) {
          os <<",";
        }
        if(i != 0 && j!=0){
          //os << "x" << (i);
          os << declared_clocks.reverse_at(i);
          os << "-";
          //os << "x" << (j);
          os << declared_clocks.reverse_at(j);
        }else if (i == 0){
          os << declared_clocks.reverse_at(j);
          if (type == 1) os << ">=" << -val ;
          else os << ">" << -val ;
          end = true;
          continue;
        }else if (j == 0){
          os << declared_clocks.reverse_at(i);
        }

        if (type == 1) {
          os << "<=" << val ;
        }
        else {
          os << "<" << val ;
        }
        end = true;
      }
    }
    if(isAllImplicit) {
      os << "INFTY";
    }
  }

};

/** Stream operator for DBMs */
inline
std::ostream& operator<<(std::ostream& os, const DBM& d)
{
    d.print_constraint(os);
    return os;
}

#endif //DBM_H
