/**
  * Utility functions.
  *
  * @author Jeroen Keiren
  * @copyright MIT Licence, see the accompanying LICENCE.txt.
  */

#ifndef UTILITIES_HH
#define UTILITIES_HH

#include <algorithm>
#include <vector>

/** \brief Determines whether n is exactly a power of two */
inline bool is_power_of_two(const std::size_t n)
{
  if (n == 0) {
    return false;
  } else {
    return (n & (n - 1)) == 0;
  }
}

/** \brief calls delete on all element af a vector */
template<typename T>
void delete_vector_elements(std::vector<T*>& vec)
{
  std::for_each(vec.begin(), vec.end(), [](T* t) { delete t; });
}

#endif // UTILITIES_HH
