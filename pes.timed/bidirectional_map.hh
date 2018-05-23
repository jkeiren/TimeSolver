/** \file bidirectional_map.hh
 * Simple bidirectional map implementation that keeps track of key <-> value
 * mappings in both directions.
 * @author Jeroen Keiren
 * @copyright MIT Licence, see the accompanying LICENCE.txt
 */

#ifndef BIDIRECTIONAL_MAP_HH
#define BIDIRECTIONAL_MAP_HH

#include <map>
#include <initializer_list>

/** Bidirectional map. Assume the value type is size_t, and that the values are
 *  dense. */
template <typename KeyType, typename ValueType>
class bidirectional_map {
protected:
  std::map<KeyType, ValueType> _left;  // left view
  std::map<ValueType, KeyType> _right; // right view

public:
  bidirectional_map() {}

  bidirectional_map(std::initializer_list< std::pair<KeyType, ValueType> > il)
  {
    for (std::pair<KeyType, ValueType> kv: il) {
      if (_left.find(kv.first) != _left.end()) {
        throw std::runtime_error(
            "Inserting duplicate key into bidirectional map.");
      }
      if (_right.find(kv.second) != _right.end()) {
        throw std::runtime_error(
            "Inserting duplicate value into bidirectional map.");
      }
      _left[kv.first] = kv.second;
      _right[kv.second] = kv.first;
    }
  }

  bool operator==(const bidirectional_map<KeyType, ValueType>& other) const {
    return _left == other._left && _right == other._right;
  }

  void insert(const KeyType& k, const ValueType& v) {
    if (_left.find(k) != _left.end()) {
      throw std::runtime_error(
          "Inserting duplicate key into bidirectional map.");
    }
    if (_right.find(v) != _right.end()) {
      throw std::runtime_error(
          "Inserting duplicate value into bidirectional map.");
    }
    _left[k] = v;
    _right[v] = k;
  }

  bool empty() const { return _left.empty(); }

  std::size_t size() const { return _left.size(); }

  const std::map<KeyType, ValueType>& left() const { return _left; }

  const std::map<ValueType, KeyType>& right() const { return _right; }

  const ValueType& at(const KeyType& k) const { return _left.at(k); }

  const KeyType& reverse_at(const ValueType& v) const { return _right.at(v); }

  void clear() {
    _left.clear();
    _right.clear();
  }
};

typedef bidirectional_map<std::string, std::size_t> clock_name_to_index_t;
typedef bidirectional_map<std::string, std::size_t> atomic_name_to_index_t;

#endif // BIDIRECTIONAL_MAP_HH
