/** \file bound_to_constraint.h
 * Implementation of the type for clock values and bounds used in DBMs.
 * @author Peter Fontana
 * @author Dezhuang Zhang
 * @author Rance Cleaveland
 * @author Jeroen Keiren
 * @copyright MIT Licence, see the accompanying LICENCE.txt
 */

#ifndef CONSTRAINTS_H
#define CONSTRAINTS_H

#include <cstdint>
#include <limits>

/// values that can be attained by a clock;
/// use fastest int of at least 16 bits for this.
typedef int_fast16_t clock_value_t;

/** Bounds used in difference bound matrices.
 *
 * Represents a pair (x, R) where x is a clock value and R in { <, <= }.
 * This representation is coded as an integer value where the lsb denotes R,
 * such that, if lsb = 0, the ordering is strict (R = <), and when lsb = 1, the
 * ordering is weak (R = <=).
 */
class bound_t
{
public:
  /// Public type to denote the raw value. This is exposed for testing purposes.
  typedef clock_value_t raw_value_type; // raw value

private:
  /// Field that records the actual value.
  raw_value_type m_value;

  /// The largest clock value that can possibly be represented.
  static constexpr clock_value_t infinity_clock_value =
      std::numeric_limits<clock_value_t>::max() >> 1;

  /// The representation used internally for infinity.
  static constexpr raw_value_type infinity_raw_value = infinity_clock_value
                                                       << 1;
  /// Convert a raw value to a clock value.
  constexpr clock_value_t clock_value(const raw_value_type x) const
  {
    return x >> 1;
  }

public:
  /// Default constructor, produced representation of infinity.
  constexpr bound_t() : m_value(infinity_raw_value) {}

  /// Constructor
  constexpr bound_t(clock_value_t value, bool strict)
      : m_value(static_cast<raw_value_type>(value << 1) |
                (strict ? static_cast<raw_value_type>(0)
                        : static_cast<raw_value_type>(1)))
  {
  }

  /// Explicit constructor. Assumes \a raw_value is already in the internal
  /// representation. Use for testing purposes only.
  explicit constexpr bound_t(const raw_value_type raw_value)
      : m_value(raw_value)
  {
  }

  /// Extract the clock value x from a bound (x, R)
  constexpr clock_value_t value() const { return clock_value(m_value); }

  /// Determine whether the bound is strict.
  /// For bound (x, R) this is true iff R = <.
  constexpr bool is_strict() const { return (m_value & 0x1) == 0; }

  /// Add two bounds.
  constexpr bound_t operator+(const bound_t& other) const
  {
    return (m_value == infinity_raw_value ||
            other.m_value == infinity_raw_value)
               ? bound_t()
               : bound_t(value() + other.value(),
                         is_strict() || other.is_strict());
  }

  /// Negate bound
  /// \pre (*this) == (x,R)
  /// \ret (-x,R') where R' == < iff R == <=
  constexpr bound_t operator-() const
  {
    return bound_t(-value(), !is_strict());
  }

  /// Get strict version of this bound.
  /// \pre (*this) == (x,R)
  /// \return (x,<)
  constexpr bound_t get_strict() const { return bound_t(m_value & ~0x1); }

  /// Get weak version of this bound.
  /// \pre (*this) == (x,R)
  /// \return (x,<=)
  constexpr bound_t get_weak() const { return bound_t(m_value | 0x1); }

  /// \overload
  constexpr bool operator==(const bound_t& other) const
  {
    return m_value == other.m_value;
  }

  /// \overload
  constexpr bool operator!=(const bound_t& other) const
  {
    return m_value != other.m_value;
  }

  /// \overload
  constexpr bool operator<(const bound_t& other) const
  {
    return m_value < other.m_value;
  }

  /// \overload
  constexpr bool operator<=(const bound_t& other) const
  {
    return m_value <= other.m_value;
  }

  /// \overload
  constexpr bool operator>(const bound_t& other) const
  {
    return m_value > other.m_value;
  }

  /// \overload
  constexpr bool operator>=(const bound_t& other) const
  {
    return m_value >= other.m_value;
  }
};

/// Convenience constant for bound (infinity, <).
/// Used in many comparisons in the algorithms.
constexpr bound_t infinity = bound_t();

/// Convenience constant for bound (0,<=).
/// Used in many comparisons in the algorithms.
constexpr bound_t zero_le = bound_t(0, false);

/// Convenience constant for bound (0,<).
/// Used in many comparisons in the algorithms.
constexpr bound_t zero_less = bound_t(0, true);

#endif // CONSTRAINTS_H
