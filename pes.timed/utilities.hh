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
  for (typename std::vector<T*>::iterator it = vec.begin(); it != vec.end();
       ++it){
    delete *it;
  }
}

template<typename T>
void deep_copy(std::vector<T*>& out, const std::vector<T*>& in)
{
  for(typename std::vector<T*>::const_iterator it = in.begin(); it != in.end(); ++it)
  {
    out.push_back(new T(**it));
  }
}

#endif // UTILITIES_HH
