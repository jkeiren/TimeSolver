/** \file OneDIntArray.hh
 * An implementation of an array of short integers.
 * @author Peter Fontana
 * @author Dezhuang Zhang
 * @author Jeroen Keiren
 * @copyright MIT Licence, see the accompanying LICENCE.txt
 * @note Many functions are inlined for better performance.
 */

#ifndef ONEDINTARRAY_H
#define ONEDINTARRAY_H

#include "Generic1DArray.hh"

/** An implementation of an array of short integers.
 * @author Dezhuang Zhang and Peter Fontana
 * @note Many functions are inlined for better performance.
 * @version 1.2
 * @date November 2, 2013 */
class OneDIntArray : public Generic1DArray {
public:
  /** OneDIntArray stores elements of type short it */
  typedef short int element_type;

  /** Default Contructor.
   * @param numElements The number of elements to allocate
   * for the array.
   * @return [Constructor]. */
  OneDIntArray(const size_type numElements)
      : Generic1DArray(numElements, sizeof(element_type)) {}

  /** Copy Constructor for constant objects.
   * @param Y (&) The reference to the object to copy.
   * @return [Constructor]. */
  OneDIntArray(const OneDIntArray& Y) : Generic1DArray(Y){}

  /** Move constructor */
  OneDIntArray(OneDIntArray&&) noexcept = default;

public:
  /** Retrieves a reference for the element specified at the given index.
   * The reference returned is a reference to the actual copy, not a deep copy.
   * Consequently, this reference can be used to change the
   * referred object's value.
   * @param index The index of the element to acces; 0 is
   * the first index.
   * @return A reference to the element in the array. */
  element_type& operator[](const size_type index) {
    // re-use the const version of this function.
    return const_cast<element_type&>(at(index));
  }

  /** Retrieves a const reference for the element specified at the given index.
   * The reference returned is a reference to the actual copy, not a deep copy.
   * Consequently, since this is a constant reference it cannot be used to
   * change the referred object's value.
   * @param index The index of the element to acces; 0 is
   * the first index.
   * @return A const reference to the element in the array. */
  const element_type& at(const size_type index) const {
    // Indexes are zero based
    /* We might want a private method that does not use bounds checks
     * In order to improve performance. */
    if (index >= quantity) {
      std::cerr << "OneDIntArray operator[] - out of bounds." << std::endl;
      exit(-1);
    }
    return operatorAccess(index);
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
  element_type& operatorAccess(const size_type index) {
    return const_cast<element_type&>(operatorAccess_impl(index));
  }

  /** Retrieves a reference for the element specified at the given index.
   * This is a protected method because it eliminates bounds checking to improve
   * performance.
   * The reference returned is a reference to the actual copy, not a deep copy.
   * Consequently, this reference can be used to change the
   * referred object's value.
   * @param index The index of the element to acces; 0 is
   * the first index.
   * @return A reference to the element in the array. */
  const element_type& operatorAccess(const size_type index) const {
    return operatorAccess_impl(index);
  }

  /** Retrieves a reference for the element specified at the given index.
   * This is a protected method because it eliminates bounds checking to improve
   * performance.
   * The reference returned is a reference to the actual copy, not a deep copy.
   * Consequently, this reference can be used to change the
   * referred object's value.
   * @param index The index of the element to acces; 0 is
   * the first index.
   * @return A reference to the element in the array. */
  const element_type& operatorAccess_impl(const size_type index) const {
    // Indexes are zero based
    size_type offset = index * sizeof(element_type);
    element_type* p = (element_type*)&(storage[offset]);
    // Dereference p
    return (*p);
  }
};

#endif // ONEDINTARRAY_H
