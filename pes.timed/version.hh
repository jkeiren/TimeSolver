/** \file version.hh
 * Version information for timesolver
 * @author Jeroen Keiren
 * @copyright MIT Licence, see the accompanying LICENCE.txt
 */

#include "version_string.hh"
#include <string>

inline
std::string version() {
  return VERSION_STRING;
}
