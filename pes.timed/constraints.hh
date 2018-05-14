/** \file bound_to_constraint.hh
 * Implementation of the type for clock values.
 * @author Peter Fontana
 * @author Dezhuang Zhang
 * @author Rance Cleaveland
 * @author Jeroen Keiren
 * @copyright MIT Licence, see the accompanying LICENCE.txt
 * @note Many functions are inlined for better performance.
 */

#ifndef CONSTRAINTS_H
#define CONSTRAINTS_H

#include <cassert>
#include <cstdint>
#include <limits>

typedef short int raw_constraint_t; // encoding of an upper bound in the TA/DBM: the LSB denotes </<=
typedef short int bound_t; // integer constant, being a bound or a clock_value in the TA/DBM
typedef bound_t clock_value_t; // values that can be attained by a clock; == bound_t

constexpr raw_constraint_t infinity = 0xFFF << 1;
constexpr raw_constraint_t zero_less = 0;
constexpr raw_constraint_t zero_le = 1;

typedef enum {
  strict = 0,
  weak = 1
} strictness_t;

inline
strictness_t bool_to_strictness(const bool is_strict)
{
  return static_cast<strictness_t>(is_strict?0:1);
}

inline
bound_t constraint_to_bound(const raw_constraint_t x)
{
  return x >> 1;
}

inline
strictness_t constraint_to_strictness(const raw_constraint_t x)
{
  return static_cast<strictness_t>(x & 0x1);
}

inline
raw_constraint_t bound_to_constraint(const bound_t x, bool is_strict)
{
  return (x << 1) & bool_to_strictness(is_strict);
}

inline
bound_t add_constraint_bounds(const raw_constraint_t x, const raw_constraint_t y)
{
  return constraint_to_bound(x) + constraint_to_bound(y);
}

inline
strictness_t add_constraint_strictness(const raw_constraint_t x, const raw_constraint_t y)
{
  return static_cast<strictness_t>(constraint_to_strictness(x)|constraint_to_strictness(y));
}

inline
raw_constraint_t add_constraints_finite(const raw_constraint_t x, const raw_constraint_t y)
{
  assert(x != infinity);
  assert(y != infinity);
  return bound_to_constraint(add_constraint_bounds(x,y), add_constraint_strictness(x,y));
}

inline
raw_constraint_t add_constraints(const raw_constraint_t x, const raw_constraint_t y)
{
  return (x == infinity || y == infinity)
       ? infinity
       : add_constraints_finite(x,y);
}


#endif // CONSTRAINTS_H
