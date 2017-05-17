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

#endif // UTILITIES_HH
