#ifndef TESTDBMS_HH
#define TESTDBMS_HH

#include "DBM.hh"

bidirectional_map<std::string, int> make_c3()
{
  bidirectional_map<std::string, int> c3;
  c3.insert("x1",1);
  c3.insert("x2",2);
  c3.insert("x3",3);
  return c3;
}

bidirectional_map<std::string, int> make_c4()
{
  bidirectional_map<std::string, int> c4;
  c4 = make_c3();
  c4.insert("x4",4);
  return c4;
}

bidirectional_map<std::string, int> make_c5()
{
  bidirectional_map<std::string, int> c5;
  c5 = make_c4();
  c5.insert("x5",5);
  return c5;
}

DBM emptyDBM3()
{
    DBM empty(3, make_c3());
    empty.makeEmpty();
    return empty;
}

DBM inftyDBM()
{
  DBM INFTYDBM(3, make_c3());
  for(int i = 0; i < 3;i++) {
    for(int j = 0; j < 3; j++){
      if(i == j || i == 0){
        INFTYDBM.addConstraint(i,j, 0x1);
      }
      else {
        INFTYDBM.addConstraint(i,j, (0xFFF << 1));
      }
    }
  }
  return INFTYDBM;
}

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
