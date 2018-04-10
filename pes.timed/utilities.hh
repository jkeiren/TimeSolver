/**
  * Utility functions.
  *
  * @author Jeroen Keiren
  * @copyright MIT Licence, see the accompanying LICENCE.txt.
  */

#ifndef UTILITIES_HH
#define UTILITIES_HH

#include <vector>

template<typename T>
void delete_vector_elements(std::vector<T*>& vec)
{
  std::for_each(vec.begin(), vec.end(), [](T* t) { delete t; });
}

template<typename T>
void deep_copy(std::vector<T*>& out, const std::vector<T*>& in)
{
  out.reserve(out.size()+in.size());
  std::for_each(in.begin(), in.end(), [&](T* t) { out.push_back(new T(*t)); });
}

#endif // UTILITIES_HH
