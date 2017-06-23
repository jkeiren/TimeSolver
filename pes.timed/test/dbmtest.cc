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

TEST(DBMTest, ClockZero)
{
  clock_value_t zero_strict = zero(true);
  EXPECT_EQ(0x0000, zero_strict);
  clock_value_t zero_nonstrict = zero(false);
  EXPECT_EQ(0x0001, zero_nonstrict);
  EXPECT_EQ(zero_strict, clock_value(0, true));
  EXPECT_EQ(zero_nonstrict, clock_value(0, false));
}

TEST(DBMTest, ClockInfty)
{
  clock_value_t infty_strict = infinity(true);
  EXPECT_EQ(0x1FFE, infty_strict);
  clock_value_t infty_nonstrict = infinity(false);
  EXPECT_EQ(0x1FFF, infty_nonstrict);
  EXPECT_EQ(infty_strict, clock_value(4095, true));
  EXPECT_EQ(infty_nonstrict, clock_value(4095, false));
}

TEST(DBMTest, ClockPositive)
{
  clock_value_t one_strict = clock_value(1, true);
  EXPECT_EQ(0x0002, one_strict);
  clock_value_t one_nonstrict = clock_value(1, false);
  EXPECT_EQ(0x0003, one_nonstrict);

  clock_value_t three_strict = clock_value(3, true);
  EXPECT_EQ(0x0006, three_strict);
  clock_value_t three_nonstrict = clock_value(3, false);
  EXPECT_EQ(0x0007, three_nonstrict);
}

TEST(DBMTest, ClockNegative)
{
  clock_value_t neg_one_strict = clock_value(-1, true);
  EXPECT_EQ(static_cast<clock_value_t>(0xFFFE), neg_one_strict); // 2's complement repr. of -2
  clock_value_t neg_one_nonstrict = clock_value(-1, false);
  EXPECT_EQ(static_cast<clock_value_t>(0xFFFF), neg_one_nonstrict); // 2's complement repr. of -1

  clock_value_t neg_three_strict = clock_value(-3, true);
  EXPECT_EQ(static_cast<clock_value_t>(0xFFFA), neg_three_strict); // 2's complement repr. of -6
  clock_value_t neg_three_nonstrict = clock_value(-3, false);
  EXPECT_EQ(static_cast<clock_value_t>(0xFFFB), neg_three_nonstrict); // 2's complement repr. of -5
}

DBM testDBM2()
{
    DBM testDBM2(testDBM1());
    testDBM2.addConstraint(2,1, clock_value(1, false));
    return testDBM2;
}

DBM testDBM3()
{
    // Make a third test DBM
    DBM testDBM3(3, make_c3());
    testDBM3.addConstraint(0,0, clock_value(0, false));
    testDBM3.addConstraint(0,1, clock_value(-3, false));
    testDBM3.addConstraint(0,2, infinity(true));
    testDBM3.addConstraint(1,0, infinity(true));
    testDBM3.addConstraint(1,1, zero(false));
    testDBM3.addConstraint(1,2, clock_value(-5, false));
    testDBM3.addConstraint(2,0, infinity(true));
    testDBM3.addConstraint(2,1, clock_value(7, false));
    testDBM3.addConstraint(2,2,  zero(false));
    return testDBM3;
}

DBM testDBM4()
{
    // Make a fourth test DBM - empty
    // This is only empty because the (0, <=) becomes (0,<)
    // and illustrates a bug in cf()
    DBM testDBM4(3, make_c3());
    testDBM4.addConstraint(0,0, zero(false));
    testDBM4.addConstraint(0,1, clock_value(-3, false));
    testDBM4.addConstraint(0,2, infinity(true));
    testDBM4.addConstraint(1,0, clock_value(3, true));
    testDBM4.addConstraint(1,1, zero(false));
    testDBM4.addConstraint(1,2, infinity(true));
    testDBM4.addConstraint(2,0, infinity(true));
    testDBM4.addConstraint(2,1, infinity(true));
    testDBM4.addConstraint(2,2, zero(false));
    return testDBM4;
}

DBM testDBM5()
{
    // Make a fifth test DBM - empty
    DBM testDBM5(3, make_c3());
    testDBM5.addConstraint(0,0, zero(false));
    testDBM5.addConstraint(0,1, clock_value(-4, false));
    testDBM5.addConstraint(0,2, infinity(true));
    testDBM5.addConstraint(1,0, clock_value(2, true));
    testDBM5.addConstraint(1,1, zero(false));
    testDBM5.addConstraint(1,2, infinity(true));
    testDBM5.addConstraint(2,0, infinity(true));
    testDBM5.addConstraint(2,1, infinity(true));
    testDBM5.addConstraint(2,2, zero(false));
    return testDBM5;
}

DBM testDBM6()
{
    // Make a sixth test DBM - empty
    DBM testDBM6(3, make_c3());
    testDBM6.addConstraint(0,0, zero(false));
    testDBM6.addConstraint(0,1, clock_value(-1, false));
    testDBM6.addConstraint(0,2, clock_value(-1, false));
    testDBM6.addConstraint(1,0, clock_value(1, false));
    testDBM6.addConstraint(1,1, zero(false));
    testDBM6.addConstraint(1,2, zero(false));
    testDBM6.addConstraint(2,0, clock_value(2, true));
    testDBM6.addConstraint(2,1, clock_value(1, false));
    testDBM6.addConstraint(2,2, zero(false));
    return testDBM6;
}

DBM testDBM7()
{
    // Make a seventh test DBM - empty
    DBM testDBM7(3, make_c3());
    testDBM7.addConstraint(0,0, zero(false));
    testDBM7.addConstraint(0,1, clock_value(-3, false));
    testDBM7.addConstraint(0,2, clock_value(-1, false));
    testDBM7.addConstraint(1,0, clock_value(3, false));
    testDBM7.addConstraint(1,1, zero(false));
    testDBM7.addConstraint(1,2, clock_value(3, false));
    testDBM7.addConstraint(2,0, clock_value(6, true));
    testDBM7.addConstraint(2,1, clock_value(3, false));
    testDBM7.addConstraint(2,2, zero(false));
    return testDBM7;
}

DBM testDBM8()
{
    DBM testDBM8(4, make_c4());
    testDBM8.addConstraint(0,1, clock_value(-1, false));
    testDBM8.addConstraint(3,1, clock_value(6, false));
    testDBM8.addConstraint(3,2, clock_value(4, false));
    return testDBM8;
}

DBM testDBM9()
{
    DBM testDBM9(4, make_c4());
    testDBM9.addConstraint(0,1, clock_value(-1, false));
    testDBM9.addConstraint(3,2, clock_value(4, false));
    return testDBM9;
}

DBM testDBM10()
{
    DBM testDBM10(4, make_c4());
    testDBM10.addConstraint(3,1, clock_value(6, false));
    testDBM10.addConstraint(3,2, clock_value(4, false));
    return testDBM10;
}

DBM testDBM11()
{
    DBM testDBM11(4, make_c4());
    testDBM11.addConstraint(2,0,clock_value(3, false));
    return testDBM11;
}

TEST(DBMTest, DefaultIsInfty)
{
  DBM INFTYDBM(3, make_c3());
  for(size_t i = 0; i < make_c3().size();i++) {
    for(size_t j = 0; j < make_c3().size(); j++){
      if(i == j || i == 0){
        INFTYDBM.addConstraint(i,j, zero(false));
      }
      else {
        INFTYDBM.addConstraint(i,j, infinity(true));
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
    expected.addConstraint(0,0, zero(false));
    expected.addConstraint(0,1, clock_value(-3, false));
    expected.addConstraint(0,2, clock_value(-8, false));
    expected.addConstraint(1,0, infinity(true));
    expected.addConstraint(1,1, zero(false));
    expected.addConstraint(1,2,  clock_value(-5, false));
    expected.addConstraint(2,0, infinity(true));
    expected.addConstraint(2,1, clock_value(7, false));
    expected.addConstraint(2,2,  zero(false));

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
    expected.addConstraint(0,0, zero(false));
    expected.addConstraint(0,1, clock_value(-1, false));
    expected.addConstraint(0,2, clock_value(-1, false));
    expected.addConstraint(1,0, clock_value(1, false));
    expected.addConstraint(1,1, zero(false));
    expected.addConstraint(1,2, zero(false));
    expected.addConstraint(2,0, clock_value(2, true));
    expected.addConstraint(2,1, clock_value(1, true));
    expected.addConstraint(2,2, zero(false));

    EXPECT_EQ(expected, canonical);
}

TEST(DBMTest, CanonicalDBM7)
{
    DBM canonical(testDBM7());
    canonical.cf();
    EXPECT_FALSE(canonical.emptiness());

    // DBM in canonical form (expected result)
    DBM expected(3, make_c3());
    expected.addConstraint(0,0, zero(false));
    expected.addConstraint(0,1, clock_value(-3, false));
    expected.addConstraint(0,2, clock_value(-1, false));
    expected.addConstraint(1,0, clock_value(3, false));
    expected.addConstraint(1,1, zero(false));
    expected.addConstraint(1,2, clock_value(2, false));
    expected.addConstraint(2,0, clock_value(6, true));
    expected.addConstraint(2,1, clock_value(3, true));
    expected.addConstraint(2,2, zero(false));

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
  expected.addConstraint(0,0, zero(false));
  expected.addConstraint(0,1, zero(false));
  expected.addConstraint(0,2, zero(false));
  expected.addConstraint(1,0, clock_value(3, true));
  expected.addConstraint(1,1, zero(false));
  expected.addConstraint(1,2, clock_value(3, true));
  expected.addConstraint(2,0, clock_value(7, true));
  expected.addConstraint(2,1, clock_value(7, true));
  expected.addConstraint(2,2, zero(false));

  EXPECT_EQ(expected, strict_pred);
}

TEST(DBMTest, AddDBM1)
{
    DBM add(testDBM1());
    add.addConstraint(0,1, clock_value(-2, false));

    DBM expected(3, make_c3());
    expected.addConstraint(0,0, zero(false));
    expected.addConstraint(0,1, clock_value(-2, false));
    expected.addConstraint(0,2, clock_value(-5, false));
    expected.addConstraint(1,0, clock_value(3, false));
    expected.addConstraint(1,1, zero(false));
    expected.addConstraint(1,2, infinity(true));
    expected.addConstraint(2,0, clock_value(7, false));
    expected.addConstraint(2,1, infinity(true));
    expected.addConstraint(2,2, zero(false));

    EXPECT_EQ(expected, add);
}

TEST(DBMTest, AddCanonicalDBM1)
{
    DBM add_canonical(testDBM1());
    add_canonical.addConstraint(0,1, clock_value(-2, false));
    add_canonical.cf();

    DBM expected(3, make_c3());
    expected.addConstraint(0,0, zero(false));
    expected.addConstraint(0,1, clock_value(-2, false));
    expected.addConstraint(0,2, clock_value(-5, false));
    expected.addConstraint(1,0, clock_value(3, false));
    expected.addConstraint(1,1, zero(false));
    expected.addConstraint(1,2, clock_value(-2, false));
    expected.addConstraint(2,0, clock_value(7, false));
    expected.addConstraint(2,1, clock_value(5, false));
    expected.addConstraint(2,2, zero(false));

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
    expected.addConstraint(0,0, zero(false));
    expected.addConstraint(0,1, clock_value(-3, false));
    expected.addConstraint(0,2, clock_value(-1, false));
    expected.addConstraint(1,0, clock_value(1, false));
    expected.addConstraint(1,1, zero(false));
    expected.addConstraint(1,2, zero(false));
    expected.addConstraint(2,0, clock_value(2, true));
    expected.addConstraint(2,1, clock_value(1, true));
    expected.addConstraint(2,2, zero(false));

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
    expected.addConstraint(0,0, zero(false));
    expected.addConstraint(0,1, clock_value(-3, false));
    expected.addConstraint(0,2, clock_value(-1, false));
    expected.addConstraint(1,0, clock_value(1, false));
    expected.addConstraint(1,1, zero(false));
    expected.addConstraint(1,2, zero(false));
    expected.addConstraint(2,0, clock_value(2, true));
    expected.addConstraint(2,1, clock_value(1, true));
    expected.addConstraint(2,2, zero(false));

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
    expected.addConstraint(0,0, zero(false));
    expected.addConstraint(0,1, clock_value(-3, false));
    expected.addConstraint(0,2, clock_value(-1, false));
    expected.addConstraint(1,0, clock_value(1, false));
    expected.addConstraint(1,1, zero(false));
    expected.addConstraint(1,2, zero(false));
    expected.addConstraint(2,0, clock_value(2, true));
    expected.addConstraint(2,1, clock_value(1, true));
    expected.addConstraint(2,2, zero(false));

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
    expected.addConstraint(0,0, zero(false));
    expected.addConstraint(0,1, clock_value(-3, false));
    expected.addConstraint(0,2, clock_value(-1, false));
    expected.addConstraint(1,0, clock_value(1, false));
    expected.addConstraint(1,1, zero(false));
    expected.addConstraint(1,2, zero(false));
    expected.addConstraint(2,0, clock_value(2, true));
    expected.addConstraint(2,1, clock_value(1, true));
    expected.addConstraint(2,2, zero(false));

    EXPECT_EQ(expected, *left);
    left->cf();
    EXPECT_TRUE(left->emptiness());
    EXPECT_EQ(emptyDBM3(), *left);
}

TEST(DBMTest, ccrepA)
{
  DBM ccrepA(5, make_c5());
  for (int i=0; i<5; i++) {
    ccrepA.addConstraint(i,0, zero(false));
  }

  EXPECT_FALSE(ccrepA.emptiness());
  ccrepA.cf();
  EXPECT_FALSE(ccrepA.emptiness());

  DBM expected(5, make_c5());
  for (int i=0; i < 5; i++) {
      for (int j=0; j < 5; j++) {
          expected.addConstraint(i,j, zero(false));
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
    test.addConstraint(0,2, clock_value(-3, false));
    test.addConstraint(1,0, clock_value(2, false));
    test.addConstraint(2,0, clock_value(2, false));
    EXPECT_FALSE(test.emptiness());

    test.cf();
    EXPECT_TRUE(test.emptiness());
    EXPECT_EQ(emptyDBM3(), test);
}

TEST(DBMTest, Bound1)
{
    /* Make DBM to try to test the correctnes of bound(maxc) */
    DBM test(3, make_c3());
    test.addConstraint(0,0, zero(false));
    test.addConstraint(0,1, clock_value(-3, false));
    test.addConstraint(0,2, infinity(true));
    test.addConstraint(1,0, infinity(true));
    test.addConstraint(1,1, zero(false));
    test.addConstraint(1,2, infinity(true));
    test.addConstraint(2,0, infinity(true));
    test.addConstraint(2,1, infinity(true));
    test.addConstraint(2,2, zero(false));

    EXPECT_FALSE(test.emptiness());
    DBM canonical(test);
    canonical.cf();
    EXPECT_EQ(test, canonical);
    EXPECT_FALSE(canonical.emptiness());

    test.bound(2);
    EXPECT_FALSE(test.emptiness());

    DBM expected(3, make_c3());
    expected.addConstraint(0,0, zero(false));
    expected.addConstraint(0,1, clock_value(-2, true));
    expected.addConstraint(0,2, infinity(true));
    expected.addConstraint(1,0, infinity(true));
    expected.addConstraint(1,1, zero(false));
    expected.addConstraint(1,2, infinity(true));
    expected.addConstraint(2,0, infinity(true));
    expected.addConstraint(2,1, infinity(true));
    expected.addConstraint(2,2, zero(false));

    EXPECT_EQ(expected, test);
}

TEST(DBMTest, Bound2)
{
    /* Make DBM to try to test the correctnes of bound(maxc) */
    DBM test(3, make_c3());
    test.addConstraint(0,0, zero(false));
    test.addConstraint(0,1, clock_value(-5, false));
    test.addConstraint(0,2, infinity(true));
    test.addConstraint(1,0, infinity(true));
    test.addConstraint(1,1, zero(false));
    test.addConstraint(1,2, infinity(true));
    test.addConstraint(2,0, infinity(true));
    test.addConstraint(2,1, clock_value(2, false));
    test.addConstraint(2,2, zero(false));

    EXPECT_FALSE(test.emptiness());
    DBM canonical(test);
    canonical.cf();
    EXPECT_EQ(test, canonical);
    EXPECT_FALSE(canonical.emptiness());

    test.bound(4);
    EXPECT_FALSE(test.emptiness());

    DBM expected(3, make_c3());
    expected.addConstraint(0,0, zero(false));
    expected.addConstraint(0,1, clock_value(-4, true));
    expected.addConstraint(0,2, infinity(true));
    expected.addConstraint(1,0, infinity(true));
    expected.addConstraint(1,1, zero(false));
    expected.addConstraint(1,2, infinity(true));
    expected.addConstraint(2,0, infinity(true));
    expected.addConstraint(2,1, infinity(true));
    expected.addConstraint(2,2, zero(false));

    EXPECT_EQ(expected, test);
}

TEST(DBMTest, Bound3)
{
    /* Make DBM to try to test the correctnes of bound(maxc) */
    DBM test(3, make_c3());
    test.addConstraint(0,0, zero(false));
    test.addConstraint(0,1, clock_value(-5, false));
    test.addConstraint(0,2, infinity(true));
    test.addConstraint(1,0, infinity(true));
    test.addConstraint(1,1, zero(false));
    test.addConstraint(1,2, infinity(true));
    test.addConstraint(2,0, clock_value(1, false));
    test.addConstraint(2,1, clock_value(2, false));
    test.addConstraint(2,2, zero(false));

    EXPECT_FALSE(test.emptiness());

    // DBM in canonical form, test canonisation works for this instance.
    DBM canonical(3, make_c3());
    canonical.addConstraint(0,0, zero(false));
    canonical.addConstraint(0,1, clock_value(-5, false));
    canonical.addConstraint(0,2, infinity(true));
    canonical.addConstraint(1,0, infinity(true));
    canonical.addConstraint(1,1, zero(false));
    canonical.addConstraint(1,2, infinity(true));
    canonical.addConstraint(2,0, clock_value(1, false));
    canonical.addConstraint(2,1, clock_value(-4, false));
    canonical.addConstraint(2,2, zero(false));

    test.cf();
    EXPECT_EQ(canonical, test);
    EXPECT_FALSE(canonical.emptiness());

    // Finally test bounding.
    DBM expected(3, make_c3());
    expected.addConstraint(0,0, zero(false));
    expected.addConstraint(0,1, clock_value(-4, true));
    expected.addConstraint(0,2, infinity(true));
    expected.addConstraint(1,0, infinity(true));
    expected.addConstraint(1,1, zero(false));
    expected.addConstraint(1,2, infinity(true));
    expected.addConstraint(2,0, clock_value(1, false));
    expected.addConstraint(2,1, clock_value(-3, true));
    expected.addConstraint(2,2, zero(false));

    test.bound(4);
    EXPECT_FALSE(test.emptiness());
    EXPECT_EQ(expected, test);
}

TEST(DBMTest, Bound4)
{
    /* Make DBM to try to test the correctnes of bound(maxc) */
    DBM test(3, make_c3());
    test.addConstraint(0,0, zero(false));
    test.addConstraint(0,1, clock_value(-5, false));
    test.addConstraint(0,2, infinity(true));
    test.addConstraint(1,0, infinity(true));
    test.addConstraint(1,1, zero(false));
    test.addConstraint(1,2, infinity(true));
    test.addConstraint(2,0, zero(false));
    test.addConstraint(2,1, clock_value(2, false));
    test.addConstraint(2,2, zero(false));

    EXPECT_FALSE(test.emptiness());

    // DBM in canonical form, test canonisation works for this instance.
    DBM canonical(3, make_c3());
    canonical.addConstraint(0,0, zero(false));
    canonical.addConstraint(0,1, clock_value(-5, false));
    canonical.addConstraint(0,2, infinity(true));
    canonical.addConstraint(1,0, infinity(true));
    canonical.addConstraint(1,1, zero(false));
    canonical.addConstraint(1,2, infinity(true));
    canonical.addConstraint(2,0, zero(false));
    canonical.addConstraint(2,1, clock_value(-5, false));
    canonical.addConstraint(2,2, zero(false));

    test.cf();
    EXPECT_EQ(canonical, test);
    EXPECT_FALSE(canonical.emptiness());

    // Finally test bounding.
    DBM expected(3, make_c3());
    expected.addConstraint(0,0, zero(false));
    expected.addConstraint(0,1, clock_value(-4, true));
    expected.addConstraint(0,2, infinity(true));
    expected.addConstraint(1,0, infinity(true));
    expected.addConstraint(1,1, zero(false));
    expected.addConstraint(1,2, infinity(true));
    expected.addConstraint(2,0, zero(false));
    expected.addConstraint(2,1, clock_value(-4, true));
    expected.addConstraint(2,2, zero(false));

    test.bound(4);
    EXPECT_FALSE(test.emptiness());
    EXPECT_EQ(expected, test);
}

TEST(DBMTest, Bound5)
{
    /* Make DBM to try to test the correctnes of bound(maxc) */
    DBM test(3, make_c3());
    test.addConstraint(0,0, zero(false));
    test.addConstraint(0,1, clock_value(-5, false));
    test.addConstraint(0,2, infinity(true));
    test.addConstraint(1,0, infinity(true));
    test.addConstraint(1,1, zero(false));
    test.addConstraint(1,2, infinity(true));
    test.addConstraint(2,0, clock_value(-1, false));
    test.addConstraint(2,1, clock_value(2, false));
    test.addConstraint(2,2, zero(false));

    EXPECT_FALSE(test.emptiness());

    // DBM in canonical form, test canonisation works for this instance.
    DBM canonical(3, make_c3());
    canonical.addConstraint(0,0, zero(false));
    canonical.addConstraint(0,1, clock_value(-5, false));
    canonical.addConstraint(0,2, infinity(true));
    canonical.addConstraint(1,0, infinity(true));
    canonical.addConstraint(1,1, zero(false));
    canonical.addConstraint(1,2, infinity(true));
    canonical.addConstraint(2,0, clock_value(-1, false));
    canonical.addConstraint(2,1, clock_value(-6, false));
    canonical.addConstraint(2,2, zero(false));

    test.cf();
    EXPECT_EQ(canonical, test);
    EXPECT_FALSE(canonical.emptiness());

    // Finally test bounding.
    DBM expected(3, make_c3());
    expected.addConstraint(0,0, zero(false));
    expected.addConstraint(0,1, clock_value(-4, true));
    expected.addConstraint(0,2, infinity(true));
    expected.addConstraint(1,0, infinity(true));
    expected.addConstraint(1,1, zero(false));
    expected.addConstraint(1,2, infinity(true));
    expected.addConstraint(2,0, clock_value(-1, false));
    expected.addConstraint(2,1, clock_value(-4, true));
    expected.addConstraint(2,2, zero(false));

    test.bound(4);
    EXPECT_FALSE(test.emptiness());
    EXPECT_EQ(expected, test);
}

TEST(DBMTest, Bound6)
{
    /* Make DBM to try to test the correctnes of bound(maxc) */
    DBM test(3, make_c3());
    test.addConstraint(0,0, zero(false));
    test.addConstraint(0,1, clock_value(-2, false));
    test.addConstraint(0,2, infinity(true));
    test.addConstraint(1,0, infinity(true));
    test.addConstraint(1,1, zero(false));
    test.addConstraint(1,2, clock_value(1, true));
    test.addConstraint(2,0, infinity(true));
    test.addConstraint(2,1, infinity(true));
    test.addConstraint(2,2, zero(false));

    EXPECT_FALSE(test.emptiness());

    // DBM in canonical form, test canonisation works for this instance.
    DBM canonical(3, make_c3());
    canonical.addConstraint(0,0, zero(false));
    canonical.addConstraint(0,1, clock_value(-2, false));
    canonical.addConstraint(0,2, clock_value(-1, true));
    canonical.addConstraint(1,0, infinity(true));
    canonical.addConstraint(1,1, zero(false));
    canonical.addConstraint(1,2, clock_value(1, true));
    canonical.addConstraint(2,0, infinity(true));
    canonical.addConstraint(2,1, infinity(true));
    canonical.addConstraint(2,2, zero(false));

    test.cf();
    EXPECT_EQ(canonical, test);
    EXPECT_FALSE(canonical.emptiness());

    // Finally test bounding.
    DBM expected(3, make_c3());
    expected.addConstraint(0,0, zero(false));
    expected.addConstraint(0,1, clock_value(-1, true));
    expected.addConstraint(0,2, clock_value(-1, true));
    expected.addConstraint(1,0, infinity(true));
    expected.addConstraint(1,1, zero(false));
    expected.addConstraint(1,2, clock_value(1, true));
    expected.addConstraint(2,0, infinity(true));
    expected.addConstraint(2,1, infinity(true));
    expected.addConstraint(2,2, zero(false));

    test.bound(1);
    EXPECT_FALSE(test.emptiness());
    EXPECT_EQ(expected, test);

    test.cf();
    EXPECT_EQ(expected, test);
}

TEST(DBMTest, Empty1)
{
    DBM test(3, make_c3());
    test.addConstraint(0,0, zero(false));
    test.addConstraint(0,1, clock_value(-5, false));
    test.addConstraint(0,2, infinity(true));
    test.addConstraint(1,0, infinity(true));
    test.addConstraint(1,1, zero(false));
    test.addConstraint(1,2, infinity(true));
    test.addConstraint(2,0, infinity(true));
    test.addConstraint(2,1, clock_value(2, false));
    test.addConstraint(2,2, zero(false));

    EXPECT_FALSE(test.emptiness());

    // DBM is already in cf
    DBM canonical(test);
    canonical.cf();
    EXPECT_EQ(test, canonical);

    // Normalize
    DBM expected(3, make_c3());
    expected.addConstraint(0,0, zero(false));
    expected.addConstraint(0,1, clock_value(-4, true));
    expected.addConstraint(0,2, infinity(true));
    expected.addConstraint(1,0, infinity(true));
    expected.addConstraint(1,1, zero(false));
    expected.addConstraint(1,2, infinity(true));
    expected.addConstraint(2,0, infinity(true));
    expected.addConstraint(2,1, infinity(true));
    expected.addConstraint(2,2, zero(false));

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
    canonical.addConstraint(0,0, zero(false));
    canonical.addConstraint(0,1, zero(false));
    canonical.addConstraint(0,2, zero(false));
    canonical.addConstraint(0,3, zero(false));
    canonical.addConstraint(1,0, infinity(true));
    canonical.addConstraint(1,1, zero(false));
    canonical.addConstraint(1,2, infinity(true));
    canonical.addConstraint(1,3, infinity(true));
    canonical.addConstraint(2,0, clock_value(3, false));
    canonical.addConstraint(2,1, clock_value(3, false));
    canonical.addConstraint(2,2, zero(false));
    canonical.addConstraint(2,3, clock_value(3, false));
    canonical.addConstraint(3,0, infinity(true));
    canonical.addConstraint(3,1, infinity(true));
    canonical.addConstraint(3,2, infinity(true));
    canonical.addConstraint(3,3, zero(false));

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
  expected.addConstraint(0,0, zero(false));
  expected.addConstraint(0,1, clock_value(-1, false));
  expected.addConstraint(0,2, zero(false));
  expected.addConstraint(0,3, zero(false));
  expected.addConstraint(1,0, infinity(true));
  expected.addConstraint(1,1, zero(false));
  expected.addConstraint(1,2, infinity(true));
  expected.addConstraint(1,3, infinity(true));
  expected.addConstraint(2,0, clock_value(3, false));
  expected.addConstraint(2,1, clock_value(3, false));
  expected.addConstraint(2,2, zero(false));
  expected.addConstraint(2,3, clock_value(3, false));
  expected.addConstraint(3,0, infinity(true));
  expected.addConstraint(3,1, clock_value(6, false));
  expected.addConstraint(3,2, clock_value(4, false));
  expected.addConstraint(3,3, zero(false));

  EXPECT_EQ(expected, left);

  DBM canonical(4, make_c4());
  canonical.addConstraint(0,0, zero(false));
  canonical.addConstraint(0,1, clock_value(-1, false));
  canonical.addConstraint(0,2, zero(false));
  canonical.addConstraint(0,3, zero(false));
  canonical.addConstraint(1,0, infinity(true));
  canonical.addConstraint(1,1, zero(false));
  canonical.addConstraint(1,2, infinity(true));
  canonical.addConstraint(1,3, infinity(true));
  canonical.addConstraint(2,0, clock_value(3, false));
  canonical.addConstraint(2,1, clock_value(2, false));
  canonical.addConstraint(2,2, zero(false));
  canonical.addConstraint(2,3, clock_value(3, false));
  canonical.addConstraint(3,0, clock_value(7, false));
  canonical.addConstraint(3,1, clock_value(6, false));
  canonical.addConstraint(3,2, clock_value(4, false));
  canonical.addConstraint(3,3, zero(false));

  left.cf();
  EXPECT_EQ(canonical, left);
}

TEST(DBMTest, IntersectDBM11DBM9)
{
  DBM left(testDBM11());
  DBM right(testDBM9());
  left.intersect(right);

  DBM expected(4, make_c4());
  expected.addConstraint(0,0, zero(false));
  expected.addConstraint(0,1, clock_value(-1, false));
  expected.addConstraint(0,2, zero(false));
  expected.addConstraint(0,3, zero(false));
  expected.addConstraint(1,0, infinity(true));
  expected.addConstraint(1,1, zero(false));
  expected.addConstraint(1,2, infinity(true));
  expected.addConstraint(1,3, infinity(true));
  expected.addConstraint(2,0, clock_value(3, false));
  expected.addConstraint(2,1, infinity(true));
  expected.addConstraint(2,2, zero(false));
  expected.addConstraint(2,3, infinity(true));
  expected.addConstraint(3,0, infinity(true));
  expected.addConstraint(3,1, infinity(true));
  expected.addConstraint(3,2, clock_value(4, false));
  expected.addConstraint(3,3, zero(false));
  EXPECT_EQ(expected, left);

  DBM canonical(4, make_c4());
  canonical.addConstraint(0,0, zero(false));
  canonical.addConstraint(0,1, clock_value(-1, false));
  canonical.addConstraint(0,2, zero(false));
  canonical.addConstraint(0,3, zero(false));
  canonical.addConstraint(1,0, infinity(true));
  canonical.addConstraint(1,1, zero(false));
  canonical.addConstraint(1,2, infinity(true));
  canonical.addConstraint(1,3, infinity(true));
  canonical.addConstraint(2,0, clock_value(3, false));
  canonical.addConstraint(2,1, clock_value(2, false));
  canonical.addConstraint(2,2, zero(false));
  canonical.addConstraint(2,3, clock_value(3, false));
  canonical.addConstraint(3,0, clock_value(7, false));
  canonical.addConstraint(3,1, clock_value(6, false));
  canonical.addConstraint(3,2, clock_value(4, false));
  canonical.addConstraint(3,3, zero(false));

  left.cf();
  EXPECT_EQ(canonical, left);
}

TEST(DBMTest, IntersectDBM11DBM10)
{
  DBM left(testDBM11());
  DBM right(testDBM10());
  left.intersect(right);

  DBM expected(4, make_c4());
  expected.addConstraint(0,0, zero(false));
  expected.addConstraint(0,1, zero(false));
  expected.addConstraint(0,2, zero(false));
  expected.addConstraint(0,3, zero(false));
  expected.addConstraint(1,0, infinity(true));
  expected.addConstraint(1,1, zero(false));
  expected.addConstraint(1,2, infinity(true));
  expected.addConstraint(1,3, infinity(true));
  expected.addConstraint(2,0, clock_value(3, false));
  expected.addConstraint(2,1, infinity(true));
  expected.addConstraint(2,2, zero(false));
  expected.addConstraint(2,3, infinity(true));
  expected.addConstraint(3,0, infinity(true));
  expected.addConstraint(3,1, clock_value(6, false));
  expected.addConstraint(3,2, clock_value(4, false));
  expected.addConstraint(3,3, zero(false));
  EXPECT_EQ(expected, left);

  DBM canonical(4, make_c4());
  canonical.addConstraint(0,0, zero(false));
  canonical.addConstraint(0,1, zero(false));
  canonical.addConstraint(0,2, zero(false));
  canonical.addConstraint(0,3, zero(false));
  canonical.addConstraint(1,0, infinity(true));
  canonical.addConstraint(1,1, zero(false));
  canonical.addConstraint(1,2, infinity(true));
  canonical.addConstraint(1,3, infinity(true));
  canonical.addConstraint(2,0, clock_value(3, false));
  canonical.addConstraint(2,1, clock_value(3, false));
  canonical.addConstraint(2,2, zero(false));
  canonical.addConstraint(2,3, clock_value(3, false));
  canonical.addConstraint(3,0, clock_value(7, false));
  canonical.addConstraint(3,1, clock_value(6, false));
  canonical.addConstraint(3,2, clock_value(4, false));
  canonical.addConstraint(3,3, zero(false));

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
