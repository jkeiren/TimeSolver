/** \file OneDIntArray.hh
 * An implementation of an array of short integers.
 * @author Peter Fontana
 * @author Dezhuang Zhang
 * @author Jeroen Keiren
 * @copyright MIT Licence, see the accompanying LICENCE.txt
 * @note Many functions are inlined for better performance.
 */

#ifndef ARRAY_H
#define ARRAY_H

#include <algorithm>
#include <iterator>
#include <stdexcept>

/** Array datatype that simply wraps a POD-array with elements of type T.
 *
 * Storage of the array is heap allocated.
 */
template<typename T>
class Array {
public:
  // types
  typedef T                                     value_type;
  typedef T*                                    iterator;
  typedef const T*                              const_iterator;
  typedef std::reverse_iterator<iterator>       reverse_iterator;
  typedef std::reverse_iterator<const_iterator> const_reverse_iterator;
  typedef T&                                    reference;
  typedef const T&                              const_reference;
  typedef std::size_t                           size_type;
  typedef std::ptrdiff_t                        difference_type;

private:
  size_type   m_size; //! Size of the array
  value_type* m_data; //! Heap allocated array (new[]'d)

public:
  /** Constructor
   *
   * @note Storage is uninitialised
   */
  Array(const std::size_t size) :
    m_size(size),
    m_data(new value_type[size])
  {}

  /** Constructor
   *
   * @note All elements of the array get value v
   */
  Array(const std::size_t size, const value_type& v) :
    m_size(size),
    m_data(new value_type[size])
  {
    std::fill(m_data, m_data + m_size, v);
  }

  /** Copy constructor */
  Array(const Array<T>& other) :
    m_size(other.m_size),
    m_data(new value_type[other.m_size])
  {
    std::memcpy(m_data, other.m_data, m_size * sizeof(value_type));
  }

  /** Move constructor
   *
   * This invalidates other
   */
  Array(Array<T>&& other) :
    m_size(std::move(other.m_size)),
    m_data(std::move(other.m_data))
  {
    other.m_data = nullptr;
  }

  /** Destructor
   */
  ~Array()
  {
    delete[] m_data;
  }

  /** Copy assign
   */
  Array& operator=(const Array<T>& other)
  {
    m_size = other.m_size;
    m_data = new value_type[other.m_size];
    std::memcpy(m_data, other.m_data, m_size * sizeof(value_type));
    return *this;
  }

  /** Move assign
   *
   * This leaves other invalid.
   */
  Array& operator=(Array<T>&& other)
  {
    m_size = std::move(other.m_size);
    m_data = std::move(other.m_data);
    other.m_data = nullptr;
    return *this;
  }

  // iterator support
  iterator begin() { return m_data; }
  const_iterator begin() const { return m_data; }
  iterator end() { return m_data + m_size; }
  const_iterator end() const { return m_data + m_size; }

  // reverse iterator support
  reverse_iterator rbegin() { return m_data + m_size - 1; }
  const_reverse_iterator rbegin() const { return m_data + m_size - 1; }
  reverse_iterator rend() { return m_data - 1; }
  const_reverse_iterator rend() const { return m_data - 1; }

  // capacity
  size_type size() const { return m_size; }
  bool empty() const { return m_size == 0; }

  // element access
  /** Access element i of the array
   *
   * Returns a reference to the object at position i.
   */
  reference operator[](const size_type i)
  {
    assert(i < m_size);
    return m_data[i];
  }

  const_reference operator[](const size_type i) const
  {
    assert(i < m_size);
    return m_data[i];
  }

  /** Access element @i of the array
   *
   * Returns a const reference to the object at position @i.
   */
  reference at(const std::size_t i)
  {
    if(!(i < m_size)) {
      throw std::runtime_error("index out of bounds");
    }
    return m_data[i];
  }

  reference front() { return m_data[0]; }
  const_reference front() const { return m_data[0]; }
  reference back() { return m_data[m_size-1]; }
  const_reference back() const { return m_data[m_size-1]; }

  /** Access element @i of the array
   *
   * Returns a const reference to the object at position @i.
   */
  const_reference at(const std::size_t i) const
  {
    if(!(i < m_size)) {
      throw std::runtime_error("index out of bounds");
    }
    return m_data[i];
  }


  /** Comparison with another array
   */
  bool operator==(const Array<T>& other) const
  {
    return std::equal(begin(), end(), other.begin());
  }
};

#endif // ARRAY_H
