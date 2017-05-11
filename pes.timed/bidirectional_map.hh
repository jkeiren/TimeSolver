#ifndef BIDIRECTIONAL_MAP_HH
#define BIDIRECTIONAL_MAP_HH

#include <map>

/** Bidirectional map. Assume the value type is size_t, and that the values are
 *  dense. */
template <typename KeyType, typename ValueType>
class bidirectional_map {
protected:
  std::map<KeyType, ValueType> _left;  // left view
  std::map<ValueType, KeyType> _right; // right view

public:
  bidirectional_map() {}

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

#endif // BIDIRECTIONAL_MAP_HH
