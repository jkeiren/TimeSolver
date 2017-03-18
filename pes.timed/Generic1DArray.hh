/** \file Generic1DArray.hh
 * An array structure used to store a one-dimensional array of
 * various data primitives.
 * Project: Proof Based Real-time Model Checker
 * Purpose: Header for Generic One Dimentional Array Class
 * @author Dezhuang Zhang and Peter Fontana.
 * @version 1.21
 * @date November 8, 2013 */

#ifndef GENERIC1DARRAY_H
#define GENERIC1DARRAY_H

#include <iostream>
#include <string.h>
#include <stdio.h>
#include <stdlib.h>

/** An array structure used to store a one-dimensional array of
 * various data primitives.
 * @author Dezhuang Zhang and Peter Fontana.
 * @note Many functions are inlined for better performance.
 * @version 1.2
 * @date November 2, 2013 */
class Generic1DArray {
  
protected:
  /** The internal representation of the array as a sequence of bytes. */
  unsigned char* storage;
  /** Number of storage spaces. */
  short int quantity;
  /** The size of each element. This is usually sizeof(short int). */
  short int eltSize;
  
public:
  /** Default Constructor.
   * @param nEls The number of elements to allocate in the array
   * @param sz The size of each element.
   * @return [Constructor]. */
  Generic1DArray(const short int nEls, const short int sz) {
    quantity = nEls;
    eltSize = sz;
	  /* Edit: Changed from sizeof(short int) to have the specified size.
	   * This fixes the problem of parameter sz not being used. */
    storage = new unsigned char [quantity * sz];
  }

  /** Copy Constructor for constant objects.
   * @param Y (&) The reference to the object to copy.
   * @return [Constructor]. */
  Generic1DArray(const Generic1DArray &Y){
    quantity = Y.quantity;
    eltSize = Y.eltSize;
    storage = new unsigned char [quantity * Y.eltSize];
    memcpy(storage, Y.storage, quantity * Y.eltSize);
  }
  
  /** Destructor of Generic1DArray.
   * @return [Destructor]. */
  ~Generic1DArray() {
    if(storage != 0) delete []storage;
  }
  
  /** Performs a deep copy (not aliased) of the array, making the
   * produced array the same size as |Y|.
   * makes a deep copy (Not aliased).
   * @param Y (&) The reference to the second Generic1D Array
   * @return A reference to the copied object (the LHS).  When completed,
   * the LHS Generic1DArray object will be changed. */
  Generic1DArray & operator = (const Generic1DArray &Y){
    quantity = Y.quantity;
    eltSize = Y.eltSize;
    memcpy(storage, Y.storage, quantity * Y.eltSize);
    return *this;
  }
  
  /** Adds a new element to the 1D Array at the specified index.
   * @param element (*) The element to add to the array
   * @param inx The index in the array to add;  0 is
   * the first index.
   * @return None. When completed, the array will be changed.*/
  void add(const void* element, const short int inx) {
    if (inx < 0 || inx >= quantity) {
      std::cerr << "Generic1DArray add - index out of bounds " << std::endl;
      exit(-1);
    }
    memcpy(&(storage[inx * eltSize]), element, eltSize);
    if(!storage) {
      std::cerr << "memcpy error - add Generic1DArray" << std::endl;
      exit(-1);
    }
  }

  /** Returns a reference of the element at the specified index.
   * This function returns a reference to the original copy,
   * not a deep copy.
   * @param index The index of the element in the array; 0 is
   * the first index.
   * @return A pointer to the specified element in the array. */
  void* fetch(const short int index) const {
    if(index >= quantity || index < 0) {
      return 0;
    }
    // Return address of desired element:
    return &(storage[index * eltSize]);
  }

  /** Performs a bitwise comparison of the storage of
   * both arrays.
   * @param Y (&) The second Generic1DArray to compare to.
   * @return true: the two arrays are equal; false: otherwise. */
  bool operator == (const Generic1DArray & Y){
    for (int i = 0; i < (quantity >>1); i++) {
      if ((int *)&(storage[i << 2]) != (int *)&(Y.storage[i << 2])) {
        return false;
      }
    }
    // Check the last bit
    if ((quantity & 0x1) == 1) {
      return ((short int *)&(storage[(quantity>>1)<<2])==(short int *)&(Y.storage[(quantity>>1)<<2]));
    }
    return true;
  }
};
#endif // GENERIC1DARRAY_H
