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

#include <iterator>
#include <stdexcept>
#include "Generic1DArray.hh"

/** Array datatype that simply wraps a POD-array with elements of type T.
 *
 * Storage of the array is heap allocated.
 */
template<typename T>
class Array {
public:
  typedef T element_type; //! Type of elements of the array
  typedef std::size_t size_type; //! Size type

private:
  std::size_t m_size; //! Size of the array
  element_type* storage; //! Heap allocated array (new[]'d)

public:
  /** Constructor
   *
   * @note Storage is uninitialised
   */
  Array(const std::size_t size) :
    m_size(size),
    storage(new element_type[size])
  {}

  /** Constructor
   *
   * @note All elements of the array get value @v
   */
  Array(const std::size_t size, const element_type& v) :
    m_size(size),
    storage(new element_type[size])
  {
    std::fill(storage, storage + m_size, v);
  }

  /** Copy constructor */
  Array(const Array<T>& other) :
    m_size(other.m_size),
    storage(new element_type[other.m_size])
  {
    std::memcpy(storage, other.storage, m_size * sizeof(element_type));
  }

  /** Move constructor
   *
   * This invalidates other
   */
  Array(Array<T>&& other) :
    m_size(std::move(other.m_size)),
    storage(std::move(other.storage))
  {
    other.storage = nullptr;
  }

  /** Destructor
   */
  ~Array()
  {
    delete[] storage;
  }

  /** Copy assign
   */
  Array& operator=(const Array<T>& other)
  {
    m_size = other.m_size;
    storage = new element_type[other.m_size];
    std::memcpy(storage, other.storage, m_size * sizeof(element_type));
    return *this;
  }

  /** Move assign
   *
   * This leaves other invalid.
   */
  Array& operator=(Array<T>&& other)
  {
    m_size = std::move(other.m_size);
    storage = std::move(other.storage);
    other.storage = nullptr;
    return *this;
  }

  /** Comparison with another array
   */
  bool operator==(const Array<T>& other) const
  {
    return *storage == *other.storage;
  }

  /** Get size of array
   */
  size_type size() const
  {
    return m_size;
  }

  /** Access element @i of the array
   *
   * Returns a reference to the object at position @i.
   */
  element_type& operator[](const std::size_t i)
  {
    assert(i < m_size);
    return storage[i];
  }

  /** Access element @i of the array
   *
   * Returns a const reference to the object at position @i.
   */
  const element_type& at(const std::size_t i) const
  {
    if(!(i < m_size)) {
      throw std::runtime_error("index out of bounds");
    }
    return storage[i];
  }

};

/** An implementation of an array of short integers.
 * @author Dezhuang Zhang and Peter Fontana
 * @note Many functions are inlined for better performance.
 * @version 1.2
 * @date November 2, 2013 */
class OneDIntArray : public Generic1DArray {
public:
  /** OneDIntArray stores elements of type short int */
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
    return operatorAccess(index);
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
      throw std::runtime_error("OneDIntArray at - index out of bounds.");
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
