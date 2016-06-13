/** \file OneDIntArray.hh
 * An implementation of an array of short integers.
 * @author Dezhuang Zhang and Peter Fontana
 * @note Many functions are inlined for better performance.
 * @version 1.21
 * @date November 8, 2013 */

#ifndef ONEDINTARRAY_H
#define ONEDINTARRAY_H

#include "Generic1DArray.hh"

/** An implementation of an array of short integers.
 * @author Dezhuang Zhang and Pater Fontana
 * @note Many functions are inlined for better performance.
 * @version 1.2
 * @date November 2, 2013 */
class OneDIntArray : public Generic1DArray {
  
public:
  /** Default Contructor.  
   * @param numElements The number of elements to allocate
   * for the array.
   * @return [Constructor]. */
  OneDIntArray(short int numElements) : Generic1DArray(numElements, sizeof(short int)) {}
  
  /** Copy Constructor.
   * @param Y (&) The reference to the object to copy.
   * @return [Constructor]. */
  OneDIntArray(OneDIntArray &Y) : Generic1DArray(Y){};
  
  /** Copy Constructor for constant objects.
   * @param Y (&) The reference to the object to copy.
   * @return [Constructor]. */
  OneDIntArray(const OneDIntArray &Y) : Generic1DArray(Y){};
  
  /** Retrieves a reference for the element specified at the given index.
   * The reference returned is a reference to the actual copy, not a deep copy. 
   * Consequently, this reference can be used to change the 
   * referred object's value.
   * @param index The index of the element to acces; 0 is
   * the first index.
   * @return A reference to the element in the array. */
  short int& operator[](short int index) {
    // Indexes are zero based
    /* We might want a private method that does not use bounds checks
     * In order to improve performance. */
    if (index < 0 || index >= quantity) {   
      cerr << "OneDIntArray operator[] - out of bounds." <<endl;
      exit(-1);
    }
    short int offset = index * sizeof(short int);
    short int *p = (short int*) &(storage[offset]);
    // Dereference p
    return (*p);                                       
  }

protected:

  /** Retrieves a reference for the element specified at the given index.
   * This is a protected method because it eliminates bounds checking to improve
   * performance.
   * The reference returned is a reference to the actual copy, not a deep copy. 
   * Consequently, this reference can be used to change the 
   * referred object's value.
   * @param index The index of the element to acces; 0 is
   * the first index.
   * @return A reference to the element in the array. */
  short int& operatorAccess(short int index) {
    // Indexes are zero based
    short int offset = index * sizeof(short int);
    short int *p = (short int*) &(storage[offset]);
    // Dereference p
    return (*p);                                       
  }
  
};

#endif  //ONEDINTARRAY_H
