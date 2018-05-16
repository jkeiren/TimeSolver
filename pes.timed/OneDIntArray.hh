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

#endif // ONEDINTARRAY_H
