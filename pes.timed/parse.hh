/** \file parse.hh
 * High-level interface for parsing a PES
 * @author Jeroen Keiren
 * @copyright MIT Licence, see the accompanying LICENCE.txt
 */

#ifndef PARSE_HH
#define PARSE_HH

#include "pes.hh"

void parse_pes(const std::string& input_filename, bool debug, pes& result);

void parse_pes_from_string(const std::string& input_string, bool debug, pes& result);

#endif // PARSE_HH
