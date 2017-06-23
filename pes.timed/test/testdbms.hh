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
    testDBM1.addConstraint(0,0, (0x1));
    testDBM1.addConstraint(0,1, (-1 << 1) + 1);
    testDBM1.addConstraint(0,2,  (-5 << 1) + 1);
    testDBM1.addConstraint(1,0,  (3 << 1) + 1);
    testDBM1.addConstraint(1,1, (0x1));
    testDBM1.addConstraint(1,2, (0xFFF<<1));
    testDBM1.addConstraint(2,0, (7 << 1) + 1);
    testDBM1.addConstraint(2,1,  (0xFFF<<1));
    testDBM1.addConstraint(2,2, (0x1));
    return testDBM1;
}

inline
DBM testDBM1cf()
{
    // DBM in canonical form (expected result)
    DBM expected(3, make_c3());
    expected.addConstraint(0,0, (0x1));
    expected.addConstraint(0,1, (-1 << 1) + 1);
    expected.addConstraint(0,2,  (-5 << 1) + 1);
    expected.addConstraint(1,0,  (3 << 1) + 1);
    expected.addConstraint(1,1, (0x1));
    expected.addConstraint(1,2, (-2 << 1) + 1);
    expected.addConstraint(2,0, (7 << 1) + 1);
    expected.addConstraint(2,1,  (6 << 1) + 1);
    expected.addConstraint(2,2, (0x1));
    return expected;
}

inline
DBM testDBM1pre()
{
    DBM expected(3, make_c3());
    expected.addConstraint(0,0, (0x1));
    expected.addConstraint(0,1, (0x1));
    expected.addConstraint(0,2,  (0x1));
    expected.addConstraint(1,0,  (3 << 1) + 1);
    expected.addConstraint(1,1, (0x1));
    expected.addConstraint(1,2, (0xFFF<<1));
    expected.addConstraint(2,0, (7 << 1) + 1);
    expected.addConstraint(2,1,  (0xFFF<<1));
    expected.addConstraint(2,2, (0x1));
    return expected;
}

inline
DBM testDBM1precf()
{
    DBM expected(3, make_c3());
    expected.addConstraint(0,0, (0x1));
    expected.addConstraint(0,1, (0x1));
    expected.addConstraint(0,2, (0x1));
    expected.addConstraint(1,0, (3 << 1) + 1);
    expected.addConstraint(1,1, (0x1));
    expected.addConstraint(1,2, (3 << 1) + 1);
    expected.addConstraint(2,0, (7 << 1) + 1);
    expected.addConstraint(2,1, (7 << 1) + 1);
    expected.addConstraint(2,2, (0x1));
    return expected;
}

#endif // TESTDBMS_HH
