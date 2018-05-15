/** \file Generic1DArray.hh
 * An array structure used to store a one-dimensional array of
 * various data primitives.
 * Project: Proof Based Real-time Model Checker
 * Purpose: Header for Generic One Dimentional Array Class
 * @author Peter Fontana
 * @author Dezhuang Zhang
 * @author Jeroen Keiren
 * @copyright MIT Licence, see the accompanying LICENCE.txt
  */

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
public:
  /** Type for the size of the array */
  typedef std::size_t size_type;

protected:
  /** The internal representation of the array as a sequence of bytes. */
  unsigned char *storage;

  /** Number of storage spaces. */
  size_type quantity;
  /** The size of each element. This is usually sizeof(short int). */
  std::size_t eltSize;

public:
  /** Default Constructor.
   * @param nEls The number of elements to allocate in the array
   * @param sz The size of each element.
   * @return [Constructor]. */
  Generic1DArray(const size_type nEls, const std::size_t sz) {
    quantity = nEls;
    eltSize = sz;
    /* Edit: Changed from sizeof(short int) to have the specified size.
     * This fixes the problem of parameter sz not being used. */
    storage = new unsigned char[quantity * sz];
  }

  /** Copy Constructor for constant objects.
   * @param Y (&) The reference to the object to copy.
   * @return [Constructor]. */
  Generic1DArray(const Generic1DArray &Y) {
    quantity = Y.quantity;
    eltSize = Y.eltSize;
    storage = new unsigned char[quantity * Y.eltSize];
    memcpy(storage, Y.storage, quantity * Y.eltSize);
  }

  /** Move constructor */
  Generic1DArray(Generic1DArray &&other) noexcept :
    storage(std::move(other.storage)),
    quantity(std::move(other.quantity)),
    eltSize(std::move(other.eltSize))
  {
    other.storage = nullptr;
  }

  /** Destructor of Generic1DArray.
   * @return [Destructor]. */
  ~Generic1DArray() {
    delete[] storage;
  }

  /** Performs a deep copy (not aliased) of the array, making the
   * produced array the same size as |Y|.
   * makes a deep copy (Not aliased).
   * @param Y (&) The reference to the second Generic1D Array
   * @return A reference to the copied object (the LHS).  When completed,
   * the LHS Generic1DArray object will be changed. */
  Generic1DArray &operator=(const Generic1DArray &Y) {
    quantity = Y.quantity;
    eltSize = Y.eltSize;
    memcpy(storage, Y.storage, quantity * Y.eltSize);
    return *this;
  }


  /** Performs a bitwise comparison of the storage of
   * both arrays.
   * @param Y (&) The second Generic1DArray to compare to.
   * @return true: the two arrays are equal; false: otherwise. */
  bool operator==(const Generic1DArray &Y) {
    for (size_type i = 0; i < (quantity >> 1); i++) {
      if ((int *)&(storage[i << 2]) != (int *)&(Y.storage[i << 2])) {
        return false;
      }
    }
    // Check the last bit
    if ((quantity & 0x1) == 1) {
      return ((short int *)&(storage[(quantity >> 1) << 2]) ==
              (short int *)&(Y.storage[(quantity >> 1) << 2]));
    }
    return true;
  }
};
#endif // GENERIC1DARRAY_H
