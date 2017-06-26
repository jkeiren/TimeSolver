/**
  * Some DBMs that are used in both DBM and DBMList tests.  *
  *
  * @author Peter Fontana
  * @author Jeroen Keiren
  * @copyright MIT Licence, see the accompanying LICENCE.txt.
  */

#ifndef TESTDBMS_HH
#define TESTDBMS_HH

#include "DBM.hh"

inline
bidirectional_map<std::string, int> make_c3()
{
  static bidirectional_map<std::string, int> c3 = { {"x1",1}, {"x2",2}, {"x3",3} };
  return c3;
}

inline
bidirectional_map<std::string, int> make_c4()
{
  static bidirectional_map<std::string, int> c4 = { {"x1",1}, {"x2",2}, {"x3",3}, {"x4",4} };
  return c4;
}

inline
bidirectional_map<std::string, int> make_c5()
{
  bidirectional_map<std::string, int> c5 = { {"x1",1}, {"x2",2}, {"x3",3}, {"x4",4}, {"x5",5} };
  return c5;
}

inline
DBM emptyDBM3()
{
    DBM empty(3, make_c3());
    empty.makeEmpty();
    return empty;
}

inline
DBM testDBM1()
{
    DBM testDBM1(3, make_c3());
    testDBM1.addConstraint(0,0, zero(false));
    testDBM1.addConstraint(0,1, clock_value(-1, false));
    testDBM1.addConstraint(0,2, clock_value(-5, false));
    testDBM1.addConstraint(1,0, clock_value(3, false));
    testDBM1.addConstraint(1,1, zero(false));
    testDBM1.addConstraint(1,2, infinity(true));
    testDBM1.addConstraint(2,0, clock_value(7, false));
    testDBM1.addConstraint(2,1, infinity(true));
    testDBM1.addConstraint(2,2, zero(false));
    return testDBM1;
}

inline
DBM testDBM1cf()
{
    // DBM in canonical form (expected result)
    DBM expected(3, make_c3());
    expected.addConstraint(0,0, zero(false));
    expected.addConstraint(0,1, clock_value(-1, false));
    expected.addConstraint(0,2, clock_value(-5, false));
    expected.addConstraint(1,0, clock_value(3, false));
    expected.addConstraint(1,1, zero(false));
    expected.addConstraint(1,2, clock_value(-2, false));
    expected.addConstraint(2,0, clock_value(7, false));
    expected.addConstraint(2,1, clock_value(6, false));
    expected.addConstraint(2,2, zero(false));
    return expected;
}

inline
DBM testDBM1pre()
{
    DBM expected(3, make_c3());
    expected.addConstraint(0,0, zero(false));
    expected.addConstraint(0,1, zero(false));
    expected.addConstraint(0,2, zero(false));
    expected.addConstraint(1,0, clock_value(3, false));
    expected.addConstraint(1,1, zero(false));
    expected.addConstraint(1,2, infinity(true));
    expected.addConstraint(2,0, clock_value(7, false));
    expected.addConstraint(2,1, infinity(true));
    expected.addConstraint(2,2, zero(false));
    return expected;
}

inline
DBM testDBM1precf()
{
    DBM expected(3, make_c3());
    expected.addConstraint(0,0, zero(false));
    expected.addConstraint(0,1, zero(false));
    expected.addConstraint(0,2, zero(false));
    expected.addConstraint(1,0, clock_value(3, false));
    expected.addConstraint(1,1, zero(false));
    expected.addConstraint(1,2, clock_value(3, false));
    expected.addConstraint(2,0, clock_value(7, false));
    expected.addConstraint(2,1, clock_value(7, false));
    expected.addConstraint(2,2, zero(false));
    return expected;
}

#endif // TESTDBMS_HH
