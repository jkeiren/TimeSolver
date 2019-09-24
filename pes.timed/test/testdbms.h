/**
  * Some DBMs that are used in both DBM and DBMList tests.  *
  *
  * @author Peter Fontana
  * @author Jeroen Keiren
  * @copyright MIT Licence, see the accompanying LICENCE.txt.
  */

#ifndef TESTDBMS_HH
#define TESTDBMS_HH

#include "DBM.h"

inline
const clock_name_to_index_t* make_c2()
{
  static const clock_name_to_index_t c2 = { {"x1",1}, {"x2",2} };
  return &c2;
}

inline
const clock_name_to_index_t* make_c3()
{
  static const clock_name_to_index_t c3 = { {"x1",1}, {"x2",2}, {"x3",3} };
  return &c3;
}

inline
const clock_name_to_index_t* make_c4()
{
  static const clock_name_to_index_t c4 = { {"x1",1}, {"x2",2}, {"x3",3}, {"x4",4} };
  return &c4;
}

inline
const clock_name_to_index_t* make_c5()
{
  static const clock_name_to_index_t c5 = { {"x1",1}, {"x2",2}, {"x3",3}, {"x4",4}, {"x5",5} };
  return &c5;
}

inline
DBM emptyDBM3()
{
    DBM empty(make_c2());
    empty.makeEmpty();
    return empty;
}

inline
DBM testDBM1()
{
    DBM testDBM1(make_c2());
    testDBM1.addConstraint(0, 0, zero_le);
    testDBM1.addConstraint(0, 1, bound_t(-1, false));
    testDBM1.addConstraint(0, 2, bound_t(-5, false));
    testDBM1.addConstraint(1, 0, bound_t(3, false));
    testDBM1.addConstraint(1, 1, zero_le);
    testDBM1.addConstraint(1, 2, infinity);
    testDBM1.addConstraint(2, 0, bound_t(7, false));
    testDBM1.addConstraint(2, 1, infinity);
    testDBM1.addConstraint(2, 2, zero_le);
    return testDBM1;
}

inline
DBM testDBM1cf()
{
    // DBM in canonical form (expected result)
    DBM expected(make_c2());
    expected.addConstraint(0, 0, zero_le);
    expected.addConstraint(0, 1, bound_t(-1, false));
    expected.addConstraint(0, 2, bound_t(-5, false));
    expected.addConstraint(1, 0, bound_t(3, false));
    expected.addConstraint(1, 1, zero_le);
    expected.addConstraint(1, 2, bound_t(-2, false));
    expected.addConstraint(2, 0, bound_t(7, false));
    expected.addConstraint(2, 1, bound_t(6, false));
    expected.addConstraint(2, 2, zero_le);
    return expected;
}

inline
DBM testDBM1pre()
{
    DBM expected(make_c2());
    expected.addConstraint(0,0, zero_le);
    expected.addConstraint(0,1, zero_le);
    expected.addConstraint(0,2, zero_le);
    expected.addConstraint(1, 0, bound_t(3, false));
    expected.addConstraint(1,1, zero_le);
    expected.addConstraint(1,2, infinity);
    expected.addConstraint(2, 0, bound_t(7, false));
    expected.addConstraint(2,1, infinity);
    expected.addConstraint(2,2, zero_le);
    return expected;
}

inline
DBM testDBM1precf()
{
    DBM expected(make_c2());
    expected.addConstraint(0,0, zero_le);
    expected.addConstraint(0,1, zero_le);
    expected.addConstraint(0,2, zero_le);
    expected.addConstraint(1, 0, bound_t(3, false));
    expected.addConstraint(1,1, zero_le);
    expected.addConstraint(1, 2, bound_t(3, false));
    expected.addConstraint(2, 0, bound_t(7, false));
    expected.addConstraint(2, 1, bound_t(7, false));
    expected.addConstraint(2,2, zero_le);
    return expected;
}

#endif // TESTDBMS_HH
