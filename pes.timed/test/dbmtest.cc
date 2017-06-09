/**
  * Unit tests for DBM.
  *
  *
  * @author Peter Fontana
  * @author Jeroen Keiren
  * @copyright MIT Licence, see the accompanying LICENCE.txt.
  */

#include <limits.h>
#include "DBM.hh"
#include "testdbms.hh"
#include "gtest/gtest.h"

DBM testDBM2()
{
    DBM testDBM2(testDBM1());
    testDBM2.addConstraint(2,1, (1 << 1) + 1);
    return testDBM2;
}

DBM testDBM3()
{
    // Make a third test DBM
    DBM testDBM3(3, make_c3());
    testDBM3.addConstraint(0,0, (0x1));
    testDBM3.addConstraint(0,1, (-3 << 1) + 1);
    testDBM3.addConstraint(0,2, (0xFFF<<1));
    testDBM3.addConstraint(1,0, (0xFFF<<1));
    testDBM3.addConstraint(1,1, (0x1));
    testDBM3.addConstraint(1,2,  (-5 << 1) + 1);
    testDBM3.addConstraint(2,0, (0xFFF<<1));
    testDBM3.addConstraint(2,1, (7 << 1) + 1);
    testDBM3.addConstraint(2,2,  (0x1));
    return testDBM3;
}

DBM testDBM4()
{
    // Make a fourth test DBM - empty
    // This is only empty because the (0, <=) becomes (0,<)
    // and illustrates a bug in cf()
    DBM testDBM4(3, make_c3());
    testDBM4.addConstraint(0,0, 0x1);
    testDBM4.addConstraint(0,1, (-3 << 1) + 1);
    testDBM4.addConstraint(0,2, (0xFFF<<1));
    testDBM4.addConstraint(1,0, (3 << 1));
    testDBM4.addConstraint(1,1, (0x1));
    testDBM4.addConstraint(1,2, (0xFFF<<1));
    testDBM4.addConstraint(2,0, (0xFFF<<1));
    testDBM4.addConstraint(2,1, (0xFFF<<1));
    testDBM4.addConstraint(2,2, (0x1));
    return testDBM4;
}

DBM testDBM5()
{
    // Make a fifth test DBM - empty
    DBM testDBM5(3, make_c3());
    testDBM5.addConstraint(0,0, (0x1));
    testDBM5.addConstraint(0,1, (-4 << 1) + 1);
    testDBM5.addConstraint(0,2, (0xFFF<<1));
    testDBM5.addConstraint(1,0, (2 << 1));
    testDBM5.addConstraint(1,1, (0x1));
    testDBM5.addConstraint(1,2, (0xFFF<<1));
    testDBM5.addConstraint(2,0, (0xFFF<<1));
    testDBM5.addConstraint(2,1, (0xFFF<<1));
    testDBM5.addConstraint(2,2, (0x1));
    return testDBM5;
}

DBM testDBM6()
{
    // Make a sixth test DBM - empty
    DBM testDBM6(3, make_c3());
    testDBM6.addConstraint(0,0, (0x1));
    testDBM6.addConstraint(0,1, (-1 << 1) + 1);
    testDBM6.addConstraint(0,2, (-1 << 1) + 1);
    testDBM6.addConstraint(1,0, (1 << 1) + 1);
    testDBM6.addConstraint(1,1, (0x1));
    testDBM6.addConstraint(1,2, (0 << 1) + 1);
    testDBM6.addConstraint(2,0, (2 << 1));
    testDBM6.addConstraint(2,1, (1 << 1) + 1);
    testDBM6.addConstraint(2,2, (0x1));
    return testDBM6;
}

DBM testDBM7()
{
    // Make a seventh test DBM - empty
    DBM testDBM7(3, make_c3());
    testDBM7.addConstraint(0,0, (0x1));
    testDBM7.addConstraint(0,1, (-3 << 1) + 1);
    testDBM7.addConstraint(0,2, (-1 << 1) + 1);
    testDBM7.addConstraint(1,0, (3 << 1) + 1);
    testDBM7.addConstraint(1,1, (0x1));
    testDBM7.addConstraint(1,2, (3 << 1) + 1);
    testDBM7.addConstraint(2,0, (6 << 1));
    testDBM7.addConstraint(2,1, (3 << 1) + 1);
    testDBM7.addConstraint(2,2, (0x1));
    return testDBM7;
}

DBM testDBM8()
{
    DBM testDBM8(4, make_c4());
    testDBM8.addConstraint(0,1, (-1 << 1) + 1);
    testDBM8.addConstraint(3,1, (6 << 1) + 1);
    testDBM8.addConstraint(3,2, (4 << 1) + 1);
    return testDBM8;
}

DBM testDBM9()
{
    DBM testDBM9(4, make_c4());
    testDBM9.addConstraint(0,1, (-1 << 1) + 1);
    testDBM9.addConstraint(3,2, (4 << 1) + 1);
    return testDBM9;
}

DBM testDBM10()
{
    DBM testDBM10(4, make_c4());
    testDBM10.addConstraint(3,1, (6 << 1) + 1);
    testDBM10.addConstraint(3,2, (4 << 1) + 1);
    return testDBM10;
}

DBM testDBM11()
{
    DBM testDBM11(4, make_c4());
    testDBM11.addConstraint(2,0,(3 << 1) + 1);
    return testDBM11;
}

TEST(DBMTest, DefaultIsInfty)
{
  DBM INFTYDBM(3, make_c3());
  for(size_t i = 0; i < make_c3().size();i++) {
    for(size_t j = 0; j < make_c3().size(); j++){
      if(i == j || i == 0){
        INFTYDBM.addConstraint(i,j, 0x1);
      }
      else {
        INFTYDBM.addConstraint(i,j, (0xFFF << 1));
      }
    }
  }
  DBM defaultDBM(3, make_c3());
  EXPECT_EQ(INFTYDBM, defaultDBM);
}

TEST(DBMTest, Copy)
{
    DBM copy = testDBM1();
    EXPECT_EQ(testDBM1(), copy);
}

TEST(DBMTest, Emptiness)
{
    EXPECT_TRUE(emptyDBM3().emptiness());
    EXPECT_FALSE(testDBM1().emptiness());
    EXPECT_FALSE(testDBM2().emptiness());
    EXPECT_FALSE(testDBM3().emptiness());
    EXPECT_FALSE(testDBM4().emptiness());
    EXPECT_FALSE(testDBM5().emptiness());
    EXPECT_FALSE(testDBM6().emptiness());
    EXPECT_FALSE(testDBM7().emptiness());
    EXPECT_FALSE(DBM(3, make_c3()).emptiness());
}

TEST(DBMTest, PreEmptyIsEmpty)
{
  DBM preEmpty(emptyDBM3());
  preEmpty.pre();
  preEmpty.cf();
  EXPECT_TRUE(preEmpty.emptiness());
}

TEST(DBMTest, CanonicalEmpty)
{
    DBM canonical(emptyDBM3());
    canonical.cf();
    EXPECT_TRUE(canonical.emptiness());
    EXPECT_EQ(emptyDBM3(), canonical);
}

TEST(DBMTest, CanonicalDBM1)
{
    DBM canonical(testDBM1());
    canonical.cf();
    EXPECT_FALSE(canonical.emptiness());
    EXPECT_EQ(testDBM1cf(), canonical);
}

TEST(DBMTest, CanonicalDBM2)
{
    DBM canonical(testDBM2());
    canonical.cf();
    EXPECT_TRUE(canonical.emptiness());
    EXPECT_EQ(emptyDBM3(), canonical);
}

TEST(DBMTest, CanonicalDBM3)
{
    DBM canonical(testDBM3());
    canonical.cf();
    EXPECT_FALSE(canonical.emptiness());

    // DBM in canonical form (expected result)
    DBM expected(3, make_c3());
    expected.addConstraint(0,0, (0x1));
    expected.addConstraint(0,1, (-3 << 1) + 1);
    expected.addConstraint(0,2, (-8 << 1) + 1);
    expected.addConstraint(1,0, (0xFFF<<1));
    expected.addConstraint(1,1, (0x1));
    expected.addConstraint(1,2,  (-5 << 1) + 1);
    expected.addConstraint(2,0, (0xFFF<<1));
    expected.addConstraint(2,1, (7 << 1) + 1);
    expected.addConstraint(2,2,  (0x1));

    EXPECT_EQ(expected, canonical);
}

TEST(DBMTest, CanonicalDBM4)
{
    DBM canonical(testDBM4());
    canonical.cf();
    EXPECT_TRUE(canonical.emptiness());
    EXPECT_EQ(emptyDBM3(), canonical);
}

TEST(DBMTest, CanonicalDBM5)
{
    DBM canonical(testDBM5());
    canonical.cf();
    EXPECT_TRUE(canonical.emptiness());
    EXPECT_EQ(emptyDBM3(), canonical);
}

TEST(DBMTest, CanonicalDBM6)
{
    DBM canonical(testDBM6());
    canonical.cf();
    EXPECT_FALSE(canonical.emptiness());

    // DBM in canonical form (expected result)
    DBM expected(3, make_c3());
    expected.addConstraint(0,0, (0x1));
    expected.addConstraint(0,1, (-1 << 1) + 1);
    expected.addConstraint(0,2, (-1 << 1) + 1);
    expected.addConstraint(1,0, (1 << 1) + 1);
    expected.addConstraint(1,1, (0x1));
    expected.addConstraint(1,2, (0x1));
    expected.addConstraint(2,0, (2 << 1));
    expected.addConstraint(2,1, (1 << 1));
    expected.addConstraint(2,2, (0x1));

    EXPECT_EQ(expected, canonical);
}

TEST(DBMTest, CanonicalDBM7)
{
    DBM canonical(testDBM7());
    canonical.cf();
    EXPECT_FALSE(canonical.emptiness());

    // DBM in canonical form (expected result)
    DBM expected(3, make_c3());
    expected.addConstraint(0,0, (0x1));
    expected.addConstraint(0,1, (-3 << 1) + 1);
    expected.addConstraint(0,2, (-1 << 1) + 1);
    expected.addConstraint(1,0, (3 << 1) + 1);
    expected.addConstraint(1,1, (0x1));
    expected.addConstraint(1,2, (2 << 1) + 1);
    expected.addConstraint(2,0, (6 << 1));
    expected.addConstraint(2,1, (3 << 1));
    expected.addConstraint(2,2, (0x1));

    EXPECT_EQ(expected, canonical);
}

TEST(DBMTest, PreDBM1)
{
    DBM pre(testDBM1());
    pre.pre();

    EXPECT_EQ(testDBM1pre(), pre);
}

TEST(DBMTest, PreCanonicalDBM1)
{
    DBM pre_cf(testDBM1());
    pre_cf.pre();
    pre_cf.cf();

    EXPECT_EQ(testDBM1precf(), pre_cf);
}

TEST(DBMTest, PreCanonicalStrictDBM1)
{
  DBM strict_pred(testDBM1precf());
  strict_pred.predClosureRev();

  // DBM in canonical form (expected result)
  DBM expected(3, make_c3());
  expected.addConstraint(0,0, (0x1));
  expected.addConstraint(0,1, (0x1));
  expected.addConstraint(0,2, (0x1));
  expected.addConstraint(1,0, (3 << 1));
  expected.addConstraint(1,1, (0x1));
  expected.addConstraint(1,2, (3 << 1));
  expected.addConstraint(2,0, (7 << 1));
  expected.addConstraint(2,1, (7 << 1));
  expected.addConstraint(2,2, (0x1));

  EXPECT_EQ(expected, strict_pred);
}

TEST(DBMTest, AddDBM1)
{
    DBM add(testDBM1());
    add.addConstraint(0,1, (-2 << 1) + 1);

    DBM expected(3, make_c3());
    expected.addConstraint(0,0, (0x1));
    expected.addConstraint(0,1, (-2 << 1) + 1);
    expected.addConstraint(0,2,  (-5 << 1) + 1);
    expected.addConstraint(1,0,  (3 << 1) + 1);
    expected.addConstraint(1,1, (0x1));
    expected.addConstraint(1,2, (0xFFF<<1));
    expected.addConstraint(2,0, (7 << 1) + 1);
    expected.addConstraint(2,1,  (0xFFF<<1));
    expected.addConstraint(2,2, (0x1));

    EXPECT_EQ(expected, add);
}

TEST(DBMTest, AddCanonicalDBM1)
{
    DBM add_canonical(testDBM1());
    add_canonical.addConstraint(0,1, (-2 << 1) + 1);
    add_canonical.cf();

    DBM expected(3, make_c3());
    expected.addConstraint(0,0, (0x1));
    expected.addConstraint(0,1, (-2 << 1) + 1);
    expected.addConstraint(0,2,  (-5 << 1) + 1);
    expected.addConstraint(1,0,  (3 << 1) + 1);
    expected.addConstraint(1,1, (0x1));
    expected.addConstraint(1,2, (-2 << 1) + 1);
    expected.addConstraint(2,0, (7 << 1) + 1);
    expected.addConstraint(2,1, (5<<1) + 1);
    expected.addConstraint(2,2, (0x1));

    EXPECT_EQ(expected, add_canonical);
}

// TODO: The following test is copied from the original, but it should be
// performed on the DBM that has not been changed to canonical form, I think.
TEST(DBMTest, CanonicalBound3DBM2)
{
    DBM bound3(testDBM2());
    bound3.cf();
    bound3.bound(3);

    EXPECT_TRUE(bound3.emptiness());
    EXPECT_EQ(emptyDBM3(), bound3);
}

TEST(DBMTest, IntersectDBM7DBM6)
{
    DBM left(testDBM7());
    left.cf();
    DBM right(testDBM6());
    right.cf();

    left.intersect(right);
    EXPECT_FALSE(left.emptiness());

    DBM expected(3, make_c3());
    expected.addConstraint(0,0, (0x1));
    expected.addConstraint(0,1, (-3 << 1) + 1);
    expected.addConstraint(0,2, (-1 << 1) + 1);
    expected.addConstraint(1,0, (1 << 1) + 1);
    expected.addConstraint(1,1, (0x1));
    expected.addConstraint(1,2, (0x1));
    expected.addConstraint(2,0, (2 << 1));
    expected.addConstraint(2,1, (1 << 1));
    expected.addConstraint(2,2, (0x1));

    EXPECT_EQ(expected, left);

}

TEST(DBMTest, IntersectDBM8DBM6)
{
    DBM left(testDBM7());
    left.cf();
    DBM right(testDBM6());
    right.cf();

    left.intersect(right);
    EXPECT_FALSE(left.emptiness());

    DBM expected(3, make_c3());
    expected.addConstraint(0,0, (0x1));
    expected.addConstraint(0,1, (-3 << 1) + 1);
    expected.addConstraint(0,2, (-1 << 1) + 1);
    expected.addConstraint(1,0, (1 << 1) + 1);
    expected.addConstraint(1,1, (0x1));
    expected.addConstraint(1,2, (0x1));
    expected.addConstraint(2,0, (2 << 1));
    expected.addConstraint(2,1, (1 << 1));
    expected.addConstraint(2,2, (0x1));

    EXPECT_EQ(expected, left);
    left.cf();
    EXPECT_TRUE(left.emptiness());
    EXPECT_EQ(emptyDBM3(), left);
}

TEST(DBMTest, IntersectDBM8DBM6heap)
{
    DBM* left = new DBM(testDBM7());
    left->cf();
    DBM right(testDBM6());
    right.cf();

    left->intersect(right);
    EXPECT_FALSE(left->emptiness());

    DBM expected(3, make_c3());
    expected.addConstraint(0,0, (0x1));
    expected.addConstraint(0,1, (-3 << 1) + 1);
    expected.addConstraint(0,2, (-1 << 1) + 1);
    expected.addConstraint(1,0, (1 << 1) + 1);
    expected.addConstraint(1,1, (0x1));
    expected.addConstraint(1,2, (0x1));
    expected.addConstraint(2,0, (2 << 1));
    expected.addConstraint(2,1, (1 << 1));
    expected.addConstraint(2,2, (0x1));

    EXPECT_EQ(expected, *left);
    left->cf();
    EXPECT_TRUE(left->emptiness());
    EXPECT_EQ(emptyDBM3(), *left);
}

TEST(DBMTest, IntersectDBM8DBM6reference)
{
    DBM temp(testDBM7());
    DBM* left = &temp;

    left->cf();
    DBM right(testDBM6());
    right.cf();

    left->intersect(right);
    EXPECT_FALSE(left->emptiness());

    DBM expected(3, make_c3());
    expected.addConstraint(0,0, (0x1));
    expected.addConstraint(0,1, (-3 << 1) + 1);
    expected.addConstraint(0,2, (-1 << 1) + 1);
    expected.addConstraint(1,0, (1 << 1) + 1);
    expected.addConstraint(1,1, (0x1));
    expected.addConstraint(1,2, (0x1));
    expected.addConstraint(2,0, (2 << 1));
    expected.addConstraint(2,1, (1 << 1));
    expected.addConstraint(2,2, (0x1));

    EXPECT_EQ(expected, *left);
    left->cf();
    EXPECT_TRUE(left->emptiness());
    EXPECT_EQ(emptyDBM3(), *left);
}

TEST(DBMTest, ccrepA)
{
  DBM ccrepA(5, make_c5());
  for (int i=0; i<5; i++) {
    ccrepA.addConstraint(i,0, 0x1);
  }

  EXPECT_FALSE(ccrepA.emptiness());
  ccrepA.cf();
  EXPECT_FALSE(ccrepA.emptiness());

  DBM expected(5, make_c5());
  for (int i=0; i < 5; i++) {
      for (int j=0; j < 5; j++) {
          expected.addConstraint(i,j, (0x1));
      }
  }
  EXPECT_EQ(expected, ccrepA);

}

TEST(DBMTest, empty)
{
    DBM expected(3, make_c3());
    for (int i=0; i < 3; i++) {
        for (int j=0; j < 3; j++) {
            expected.addConstraint(i,j, (0x0));
        }
    }
    EXPECT_EQ(expected, emptyDBM3());
}

// Extra tests
TEST(DBMTest, tDBM5)
{
    DBM test(3, make_c3());
    test.addConstraint(0,2, (-3 << 1) + 1);
    test.addConstraint(1,0, (2 << 1) + 1);
    test.addConstraint(2,0, (2 << 1) + 1);
    EXPECT_FALSE(test.emptiness());

    test.cf();
    EXPECT_TRUE(test.emptiness());
    EXPECT_EQ(emptyDBM3(), test);
}

TEST(DBMTest, Bound1)
{
    /* Make DBM to try to test the correctnes of bound(maxc) */
    DBM test(3, make_c3());
    test.addConstraint(0,0, 0x1);
    test.addConstraint(0,1, (-3 << 1) + 1);
    test.addConstraint(0,2, (0xFFF<<1));
    test.addConstraint(1,0, (0xFFF<<1));
    test.addConstraint(1,1, (0x1));
    test.addConstraint(1,2, (0xFFF<<1));
    test.addConstraint(2,0, (0xFFF<<1));
    test.addConstraint(2,1, (0xFFF<<1));
    test.addConstraint(2,2, (0x1));

    EXPECT_FALSE(test.emptiness());
    DBM canonical(test);
    canonical.cf();
    EXPECT_EQ(test, canonical);
    EXPECT_FALSE(canonical.emptiness());

    test.bound(2);
    EXPECT_FALSE(test.emptiness());

    DBM expected(3, make_c3());
    expected.addConstraint(0,0, 0x1);
    expected.addConstraint(0,1, (-2 << 1));
    expected.addConstraint(0,2, (0xFFF<<1));
    expected.addConstraint(1,0, (0xFFF<<1));
    expected.addConstraint(1,1, (0x1));
    expected.addConstraint(1,2, (0xFFF<<1));
    expected.addConstraint(2,0, (0xFFF<<1));
    expected.addConstraint(2,1, (0xFFF<<1));
    expected.addConstraint(2,2, (0x1));

    EXPECT_EQ(expected, test);
}

TEST(DBMTest, Bound2)
{
    /* Make DBM to try to test the correctnes of bound(maxc) */
    DBM test(3, make_c3());
    test.addConstraint(0,0, 0x1);
    test.addConstraint(0,1, (-5 << 1) + 1);
    test.addConstraint(0,2, (0xFFF<<1));
    test.addConstraint(1,0, (0xFFF<<1));
    test.addConstraint(1,1, (0x1));
    test.addConstraint(1,2, (0xFFF<<1));
    test.addConstraint(2,0, (0xFFF<<1));
    test.addConstraint(2,1, (2<<1) + 1);
    test.addConstraint(2,2, (0x1));

    EXPECT_FALSE(test.emptiness());
    DBM canonical(test);
    canonical.cf();
    EXPECT_EQ(test, canonical);
    EXPECT_FALSE(canonical.emptiness());

    test.bound(4);
    EXPECT_FALSE(test.emptiness());

    DBM expected(3, make_c3());
    expected.addConstraint(0,0, 0x1);
    expected.addConstraint(0,1, (-4 << 1));
    expected.addConstraint(0,2, (0xFFF<<1));
    expected.addConstraint(1,0, (0xFFF<<1));
    expected.addConstraint(1,1, (0x1));
    expected.addConstraint(1,2, (0xFFF<<1));
    expected.addConstraint(2,0, (0xFFF<<1));
    expected.addConstraint(2,1, (0xFFF<<1));
    expected.addConstraint(2,2, (0x1));

    EXPECT_EQ(expected, test);
}

TEST(DBMTest, Bound3)
{
    /* Make DBM to try to test the correctnes of bound(maxc) */
    DBM test(3, make_c3());
    test.addConstraint(0,0, 0x1);
    test.addConstraint(0,1, (-5 << 1) + 1);
    test.addConstraint(0,2, (0xFFF<<1));
    test.addConstraint(1,0, (0xFFF<<1));
    test.addConstraint(1,1, (0x1));
    test.addConstraint(1,2, (0xFFF<<1));
    test.addConstraint(2,0, (1<<1)+1);
    test.addConstraint(2,1, (2 <<1)+1);
    test.addConstraint(2,2, (0x1));

    EXPECT_FALSE(test.emptiness());

    // DBM in canonical form, test canonisation works for this instance.
    DBM canonical(3, make_c3());
    canonical.addConstraint(0,0, 0x1);
    canonical.addConstraint(0,1, (-5 << 1) + 1);
    canonical.addConstraint(0,2, (0xFFF<<1));
    canonical.addConstraint(1,0, (0xFFF<<1));
    canonical.addConstraint(1,1, (0x1));
    canonical.addConstraint(1,2, (0xFFF<<1));
    canonical.addConstraint(2,0, (1<<1)+1);
    canonical.addConstraint(2,1, (-4 <<1)+1);
    canonical.addConstraint(2,2, (0x1));

    test.cf();
    EXPECT_EQ(canonical, test);
    EXPECT_FALSE(canonical.emptiness());

    // Finally test bounding.
    DBM expected(3, make_c3());
    expected.addConstraint(0,0, 0x1);
    expected.addConstraint(0,1, (-4 << 1));
    expected.addConstraint(0,2, (0xFFF<<1));
    expected.addConstraint(1,0, (0xFFF<<1));
    expected.addConstraint(1,1, (0x1));
    expected.addConstraint(1,2, (0xFFF<<1));
    expected.addConstraint(2,0, (1<<1)+1);
    expected.addConstraint(2,1, (-3 <<1));
    expected.addConstraint(2,2, (0x1));

    test.bound(4);
    EXPECT_FALSE(test.emptiness());
    EXPECT_EQ(expected, test);
}

TEST(DBMTest, Bound4)
{
    /* Make DBM to try to test the correctnes of bound(maxc) */
    DBM test(3, make_c3());
    test.addConstraint(0,0, 0x1);
    test.addConstraint(0,1, (-5 << 1) + 1);
    test.addConstraint(0,2, (0xFFF<<1));
    test.addConstraint(1,0, (0xFFF<<1));
    test.addConstraint(1,1, (0x1));
    test.addConstraint(1,2, (0xFFF<<1));
    test.addConstraint(2,0, (0<<1)+1);
    test.addConstraint(2,1, (2<<1)+1);
    test.addConstraint(2,2, (0x1));

    EXPECT_FALSE(test.emptiness());

    // DBM in canonical form, test canonisation works for this instance.
    DBM canonical(3, make_c3());
    canonical.addConstraint(0,0, 0x1);
    canonical.addConstraint(0,1, (-5 << 1) + 1);
    canonical.addConstraint(0,2, (0xFFF<<1));
    canonical.addConstraint(1,0, (0xFFF<<1));
    canonical.addConstraint(1,1, (0x1));
    canonical.addConstraint(1,2, (0xFFF<<1));
    canonical.addConstraint(2,0, (0<<1)+1);
    canonical.addConstraint(2,1, (-5<<1)+1);
    canonical.addConstraint(2,2, (0x1));

    test.cf();
    EXPECT_EQ(canonical, test);
    EXPECT_FALSE(canonical.emptiness());

    // Finally test bounding.
    DBM expected(3, make_c3());
    expected.addConstraint(0,0, 0x1);
    expected.addConstraint(0,1, (-4 << 1));
    expected.addConstraint(0,2, (0xFFF<<1));
    expected.addConstraint(1,0, (0xFFF<<1));
    expected.addConstraint(1,1, (0x1));
    expected.addConstraint(1,2, (0xFFF<<1));
    expected.addConstraint(2,0, (0<<1)+1);
    expected.addConstraint(2,1, (-4<<1));
    expected.addConstraint(2,2, (0x1));

    test.bound(4);
    EXPECT_FALSE(test.emptiness());
    EXPECT_EQ(expected, test);
}

TEST(DBMTest, Bound5)
{
    /* Make DBM to try to test the correctnes of bound(maxc) */
    DBM test(3, make_c3());
    test.addConstraint(0,0, 0x1);
    test.addConstraint(0,1, (-5 << 1) + 1);
    test.addConstraint(0,2, (0xFFF<<1));
    test.addConstraint(1,0, (0xFFF<<1));
    test.addConstraint(1,1, (0x1));
    test.addConstraint(1,2, (0xFFF<<1));
    test.addConstraint(2,0, (-1 <<1)+1);
    test.addConstraint(2,1, (2<<1)+1);
    test.addConstraint(2,2, (0x1));

    EXPECT_FALSE(test.emptiness());

    // DBM in canonical form, test canonisation works for this instance.
    DBM canonical(3, make_c3());
    canonical.addConstraint(0,0, 0x1);
    canonical.addConstraint(0,1, (-5 << 1) + 1);
    canonical.addConstraint(0,2, (0xFFF<<1));
    canonical.addConstraint(1,0, (0xFFF<<1));
    canonical.addConstraint(1,1, (0x1));
    canonical.addConstraint(1,2, (0xFFF<<1));
    canonical.addConstraint(2,0, (-1 <<1)+1);
    canonical.addConstraint(2,1, (-6<<1)+1);
    canonical.addConstraint(2,2, (0x1));

    test.cf();
    EXPECT_EQ(canonical, test);
    EXPECT_FALSE(canonical.emptiness());

    // Finally test bounding.
    DBM expected(3, make_c3());
    expected.addConstraint(0,0, 0x1);
    expected.addConstraint(0,1, (-4 << 1));
    expected.addConstraint(0,2, (0xFFF<<1));
    expected.addConstraint(1,0, (0xFFF<<1));
    expected.addConstraint(1,1, (0x1));
    expected.addConstraint(1,2, (0xFFF<<1));
    expected.addConstraint(2,0, (-1 <<1)+1);
    expected.addConstraint(2,1, (-4<<1));
    expected.addConstraint(2,2, (0x1));

    test.bound(4);
    EXPECT_FALSE(test.emptiness());
    EXPECT_EQ(expected, test);
}

TEST(DBMTest, Bound6)
{
    /* Make DBM to try to test the correctnes of bound(maxc) */
    DBM test(3, make_c3());
    test.addConstraint(0,0, 0x1);
    test.addConstraint(0,1, (-2 << 1) + 1);
    test.addConstraint(0,2, (0xFFF<<1));
    test.addConstraint(1,0, (0xFFF<<1));
    test.addConstraint(1,1, (0x1));
    test.addConstraint(1,2, (1<<1));
    test.addConstraint(2,0, (0xFFF<<1));
    test.addConstraint(2,1, (0xFFF<<1));
    test.addConstraint(2,2, (0x1));

    EXPECT_FALSE(test.emptiness());

    // DBM in canonical form, test canonisation works for this instance.
    DBM canonical(3, make_c3());
    canonical.addConstraint(0,0, 0x1);
    canonical.addConstraint(0,1, (-2 << 1) + 1);
    canonical.addConstraint(0,2, (-1 << 1));
    canonical.addConstraint(1,0, (0xFFF<<1));
    canonical.addConstraint(1,1, (0x1));
    canonical.addConstraint(1,2, (1<<1));
    canonical.addConstraint(2,0, (0xFFF<<1));
    canonical.addConstraint(2,1, (0xFFF<<1));
    canonical.addConstraint(2,2, (0x1));

    test.cf();
    EXPECT_EQ(canonical, test);
    EXPECT_FALSE(canonical.emptiness());

    // Finally test bounding.
    DBM expected(3, make_c3());
    expected.addConstraint(0,0, 0x1);
    expected.addConstraint(0,1, (-1 << 1));
    expected.addConstraint(0,2, (-1<<1));
    expected.addConstraint(1,0, (0xFFF<<1));
    expected.addConstraint(1,1, (0x1));
    expected.addConstraint(1,2, (1<<1));
    expected.addConstraint(2,0, (0xFFF<<1));
    expected.addConstraint(2,1, (0xFFF<<1));
    expected.addConstraint(2,2, (0x1));

    test.bound(1);
    EXPECT_FALSE(test.emptiness());
    EXPECT_EQ(expected, test);

    test.cf();
    EXPECT_EQ(expected, test);
}

TEST(DBMTest, Empty1)
{
    DBM test(3, make_c3());
    test.addConstraint(0,0, 0x1);
    test.addConstraint(0,1, (-5 << 1) + 1);
    test.addConstraint(0,2, (0xFFF<<1));
    test.addConstraint(1,0, (0xFFF<<1));
    test.addConstraint(1,1, (0x1));
    test.addConstraint(1,2, (0xFFF<<1));
    test.addConstraint(2,0, (0xFFF<<1));
    test.addConstraint(2,1, (2 << 1) + 1);
    test.addConstraint(2,2, (0x1));

    EXPECT_FALSE(test.emptiness());

    // DBM is already in cf
    DBM canonical(test);
    canonical.cf();
    EXPECT_EQ(test, canonical);

    // Normalize
    DBM expected(3, make_c3());
    expected.addConstraint(0,0, 0x1);
    expected.addConstraint(0,1, (-4 << 1));
    expected.addConstraint(0,2, (0xFFF<<1));
    expected.addConstraint(1,0, (0xFFF<<1));
    expected.addConstraint(1,1, (0x1));
    expected.addConstraint(1,2, (0xFFF<<1));
    expected.addConstraint(2,0, (0xFFF<<1));
    expected.addConstraint(2,1, (0xFFF<<1));
    expected.addConstraint(2,2, (0x1));

    test.bound(4);
    EXPECT_EQ(expected, test);
    EXPECT_FALSE(test.emptiness());

    DBM canonical_bound(test);
    canonical_bound.cf();
    EXPECT_EQ(test, canonical_bound);
}

TEST(DBMTest, Empty2)
{
    DBM test(testDBM8());
    EXPECT_FALSE(test.emptiness());

    // DBM is already in cf
    DBM canonical(test);
    canonical.cf();
    EXPECT_EQ(test, canonical);
    EXPECT_FALSE(test.emptiness());
}

TEST(DBMTest, Empty3)
{
    DBM test(testDBM9());
    EXPECT_FALSE(test.emptiness());

    // DBM is already in cf
    DBM canonical(test);
    canonical.cf();
    EXPECT_EQ(test, canonical);
    EXPECT_FALSE(test.emptiness());
}

TEST(DBMTest, Empty4)
{
    DBM test(testDBM10());
    EXPECT_FALSE(test.emptiness());

    // DBM is already in cf
    DBM canonical(test);
    canonical.cf();
    EXPECT_EQ(test, canonical);
    EXPECT_FALSE(test.emptiness());
}

TEST(DBMTest, Empty5)
{
    DBM test(testDBM11());
    EXPECT_FALSE(test.emptiness());

    DBM canonical(4, make_c4());
    canonical.addConstraint(0,0, 0x1);
    canonical.addConstraint(0,1, 0x1);
    canonical.addConstraint(0,2, 0x1);
    canonical.addConstraint(0,3, (0x1));
    canonical.addConstraint(1,0, (0xFFF<<1));
    canonical.addConstraint(1,1, (0x1));
    canonical.addConstraint(1,2, (0xFFF<<1));
    canonical.addConstraint(1,3, (0xFFF<<1));
    canonical.addConstraint(2,0, (3<<1)+1);
    canonical.addConstraint(2,1, (3<<1)+1);
    canonical.addConstraint(2,2, (0x1));
    canonical.addConstraint(2,3, (3<<1)+1);
    canonical.addConstraint(3,0, (0xFFF<<1));
    canonical.addConstraint(3,1, (0xFFF<<1));
    canonical.addConstraint(3,2, (0xFFF<<1));
    canonical.addConstraint(3,3, (0x1));

    test.cf();
    EXPECT_EQ(canonical, test);
    EXPECT_FALSE(test.emptiness());
}

TEST(DBMTest, IntersectDBM11DBM8)
{
  DBM left(testDBM11());
  left.cf();
  DBM right(testDBM8());
  left.intersect(right);

  DBM expected(4, make_c4());
  expected.addConstraint(0,0, 0x1);
  expected.addConstraint(0,1, (-1 << 1) + 1);
  expected.addConstraint(0,2, 0x1);
  expected.addConstraint(0,3, (0x1));
  expected.addConstraint(1,0, (0xFFF<<1));
  expected.addConstraint(1,1, (0x1));
  expected.addConstraint(1,2, (0xFFF<<1));
  expected.addConstraint(1,3, (0xFFF<<1));
  expected.addConstraint(2,0, (3<<1)+1);
  expected.addConstraint(2,1, (3<<1)+1);
  expected.addConstraint(2,2, (0x1));
  expected.addConstraint(2,3, (3<<1)+1);
  expected.addConstraint(3,0, (0xFFF<<1));
  expected.addConstraint(3,1, (6 << 1) + 1);
  expected.addConstraint(3,2, (4 << 1) + 1);
  expected.addConstraint(3,3, (0x1));

  EXPECT_EQ(expected, left);

  DBM canonical(4, make_c4());
  canonical.addConstraint(0,0, 0x1);
  canonical.addConstraint(0,1, (-1 << 1) + 1);
  canonical.addConstraint(0,2, 0x1);
  canonical.addConstraint(0,3, (0x1));
  canonical.addConstraint(1,0, (0xFFF<<1));
  canonical.addConstraint(1,1, (0x1));
  canonical.addConstraint(1,2, (0xFFF<<1));
  canonical.addConstraint(1,3, (0xFFF<<1));
  canonical.addConstraint(2,0, (3<<1)+1);
  canonical.addConstraint(2,1, (2<<1)+1);
  canonical.addConstraint(2,2, (0x1));
  canonical.addConstraint(2,3, (3<<1)+1);
  canonical.addConstraint(3,0, (7 << 1) + 1);
  canonical.addConstraint(3,1, (6 << 1) + 1);
  canonical.addConstraint(3,2, (4 << 1) + 1);
  canonical.addConstraint(3,3, (0x1));

  left.cf();
  EXPECT_EQ(canonical, left);
}

TEST(DBMTest, IntersectDBM11DBM9)
{
  DBM left(testDBM11());
  DBM right(testDBM9());
  left.intersect(right);

  DBM expected(4, make_c4());
  expected.addConstraint(0,0, 0x1);
  expected.addConstraint(0,1, (-1 << 1) + 1);
  expected.addConstraint(0,2, 0x1);
  expected.addConstraint(0,3, (0x1));
  expected.addConstraint(1,0, (0xFFF<<1));
  expected.addConstraint(1,1, (0x1));
  expected.addConstraint(1,2, (0xFFF<<1));
  expected.addConstraint(1,3, (0xFFF<<1));
  expected.addConstraint(2,0, (3<<1)+1);
  expected.addConstraint(2,1, (0xFFF<<1));
  expected.addConstraint(2,2, (0x1));
  expected.addConstraint(2,3, (0xFFF<<1));
  expected.addConstraint(3,0, (0xFFF<<1));
  expected.addConstraint(3,1, (0xFFF<<1));
  expected.addConstraint(3,2, (4 << 1) + 1);
  expected.addConstraint(3,3, (0x1));
  EXPECT_EQ(expected, left);

  DBM canonical(4, make_c4());
  canonical.addConstraint(0,0, 0x1);
  canonical.addConstraint(0,1, (-1 << 1) + 1);
  canonical.addConstraint(0,2, 0x1);
  canonical.addConstraint(0,3, (0x1));
  canonical.addConstraint(1,0, (0xFFF<<1));
  canonical.addConstraint(1,1, (0x1));
  canonical.addConstraint(1,2, (0xFFF<<1));
  canonical.addConstraint(1,3, (0xFFF<<1));
  canonical.addConstraint(2,0, (3<<1)+1);
  canonical.addConstraint(2,1, (2<<1)+1);
  canonical.addConstraint(2,2, (0x1));
  canonical.addConstraint(2,3, (3<<1)+1);
  canonical.addConstraint(3,0, (7 << 1) + 1);
  canonical.addConstraint(3,1, (6 << 1) + 1);
  canonical.addConstraint(3,2, (4 << 1) + 1);
  canonical.addConstraint(3,3, (0x1));

  left.cf();
  EXPECT_EQ(canonical, left);
}

TEST(DBMTest, IntersectDBM11DBM10)
{
  DBM left(testDBM11());
  DBM right(testDBM10());
  left.intersect(right);

  DBM expected(4, make_c4());
  expected.addConstraint(0,0, 0x1);
  expected.addConstraint(0,1, 0x1);
  expected.addConstraint(0,2, 0x1);
  expected.addConstraint(0,3, 0x1);
  expected.addConstraint(1,0, (0xFFF<<1));
  expected.addConstraint(1,1, (0x1));
  expected.addConstraint(1,2, (0xFFF<<1));
  expected.addConstraint(1,3, (0xFFF<<1));
  expected.addConstraint(2,0, (3<<1)+1);
  expected.addConstraint(2,1, (0xFFF<<1));
  expected.addConstraint(2,2, (0x1));
  expected.addConstraint(2,3, (0xFFF<<1));
  expected.addConstraint(3,0, (0xFFF<<1));
  expected.addConstraint(3,1, (6 << 1) + 1);
  expected.addConstraint(3,2, (4 << 1) + 1);
  expected.addConstraint(3,3, (0x1));
  EXPECT_EQ(expected, left);

  DBM canonical(4, make_c4());
  canonical.addConstraint(0,0, 0x1);
  canonical.addConstraint(0,1, 0x1);
  canonical.addConstraint(0,2, 0x1);
  canonical.addConstraint(0,3, 0x1);
  canonical.addConstraint(1,0, (0xFFF<<1));
  canonical.addConstraint(1,1, (0x1));
  canonical.addConstraint(1,2, (0xFFF<<1));
  canonical.addConstraint(1,3, (0xFFF<<1));
  canonical.addConstraint(2,0, (3<<1)+1);
  canonical.addConstraint(2,1, (3<<1)+1);
  canonical.addConstraint(2,2, (0x1));
  canonical.addConstraint(2,3, (3<<1)+1);
  canonical.addConstraint(3,0, (7 << 1) + 1);
  canonical.addConstraint(3,1, (6 << 1) + 1);
  canonical.addConstraint(3,2, (4 << 1) + 1);
  canonical.addConstraint(3,3, (0x1));

  left.cf();
  EXPECT_EQ(canonical, left);
}

// Call RUN_ALL_TESTS() in main().
//
// We do this by linking in src/gtest_main.cc file, which consists of
// a main() function which calls RUN_ALL_TESTS() for us.
//
// This runs all the tests we've defined, prints the result, and
// returns 0 if successful, or 1 otherwise.
