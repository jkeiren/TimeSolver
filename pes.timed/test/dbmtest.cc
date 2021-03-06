/**
  * Unit tests for DBM.
  *
  *
  * @author Peter Fontana
  * @author Jeroen Keiren
  * @copyright MIT Licence, see the accompanying LICENCE.txt.
  */

#include <climits>
#include "DBM.hh"
#include "testdbms.hh"
#include "gtest/gtest.h"

TEST(DBMTest, ClockZero)
{
  clock_value_t zero_strict = zero_less;
  EXPECT_EQ(0x0000, zero_strict);
  clock_value_t zero_nonstrict = zero_le;
  EXPECT_EQ(0x0001, zero_nonstrict);
  EXPECT_EQ(zero_strict, bound_to_constraint(0, strict));
  EXPECT_EQ(zero_nonstrict, bound_to_constraint(0, weak));
}

TEST(DBMTest, ClockInfty)
{
  clock_value_t infty_strict = infinity;
  EXPECT_EQ(infty_strict, std::numeric_limits<bound_t>::max() ^ 1);
}

TEST(DBMTest, ClockPositive)
{
  clock_value_t one_strict = bound_to_constraint(1, strict);
  EXPECT_EQ(0x0002, one_strict);
  clock_value_t one_nonstrict = bound_to_constraint(1, weak);
  EXPECT_EQ(0x0003, one_nonstrict);

  clock_value_t three_strict = bound_to_constraint(3, strict);
  EXPECT_EQ(0x0006, three_strict);
  clock_value_t three_nonstrict = bound_to_constraint(3, weak);
  EXPECT_EQ(0x0007, three_nonstrict);
}

TEST(DBMTest, ClockNegative)
{
  clock_value_t neg_one_strict = bound_to_constraint(-1, strict);
  EXPECT_EQ(static_cast<clock_value_t>(0xFFFE), neg_one_strict); // 2's complement repr. of -2
  clock_value_t neg_one_nonstrict = bound_to_constraint(-1, weak);
  EXPECT_EQ(static_cast<clock_value_t>(0xFFFF), neg_one_nonstrict); // 2's complement repr. of -1

  clock_value_t neg_three_strict = bound_to_constraint(-3, strict);
  EXPECT_EQ(static_cast<clock_value_t>(0xFFFA), neg_three_strict); // 2's complement repr. of -6
  clock_value_t neg_three_nonstrict = bound_to_constraint(-3, weak);
  EXPECT_EQ(static_cast<clock_value_t>(0xFFFB), neg_three_nonstrict); // 2's complement repr. of -5
}

DBM testDBM2()
{
    DBM testDBM2(testDBM1());
    testDBM2.addConstraint(2,1, bound_to_constraint(1, weak));
    return testDBM2;
}

DBM testDBM3()
{
    // Make a third test DBM
    DBM testDBM3(make_c2());
    testDBM3.addConstraint(0,0, bound_to_constraint(0, weak));
    testDBM3.addConstraint(0,1, bound_to_constraint(-3, weak));
    testDBM3.addConstraint(0,2, infinity);
    testDBM3.addConstraint(1,0, infinity);
    testDBM3.addConstraint(1,1, zero_le);
    testDBM3.addConstraint(1,2, bound_to_constraint(-5, weak));
    testDBM3.addConstraint(2,0, infinity);
    testDBM3.addConstraint(2,1, bound_to_constraint(7, weak));
    testDBM3.addConstraint(2,2,  zero_le);
    return testDBM3;
}

DBM testDBM4()
{
    // Make a fourth test DBM - empty
    // This is only empty because the (0, <=) becomes (0,<)
    // and illustrates a bug in cf()
    DBM testDBM4(make_c2());
    testDBM4.addConstraint(0,0, zero_le);
    testDBM4.addConstraint(0,1, bound_to_constraint(-3, weak));
    testDBM4.addConstraint(0,2, infinity);
    testDBM4.addConstraint(1,0, bound_to_constraint(3, strict));
    testDBM4.addConstraint(1,1, zero_le);
    testDBM4.addConstraint(1,2, infinity);
    testDBM4.addConstraint(2,0, infinity);
    testDBM4.addConstraint(2,1, infinity);
    testDBM4.addConstraint(2,2, zero_le);
    return testDBM4;
}

DBM testDBM5()
{
    // Make a fifth test DBM - empty
    DBM testDBM5(make_c2());
    testDBM5.addConstraint(0,0, zero_le);
    testDBM5.addConstraint(0,1, bound_to_constraint(-4, weak));
    testDBM5.addConstraint(0,2, infinity);
    testDBM5.addConstraint(1,0, bound_to_constraint(2, strict));
    testDBM5.addConstraint(1,1, zero_le);
    testDBM5.addConstraint(1,2, infinity);
    testDBM5.addConstraint(2,0, infinity);
    testDBM5.addConstraint(2,1, infinity);
    testDBM5.addConstraint(2,2, zero_le);
    return testDBM5;
}

DBM testDBM6()
{
    // Make a sixth test DBM - empty
    DBM testDBM6(make_c2());
    testDBM6.addConstraint(0,0, zero_le);
    testDBM6.addConstraint(0,1, bound_to_constraint(-1, weak));
    testDBM6.addConstraint(0,2, bound_to_constraint(-1, weak));
    testDBM6.addConstraint(1,0, bound_to_constraint(1, weak));
    testDBM6.addConstraint(1,1, zero_le);
    testDBM6.addConstraint(1,2, zero_le);
    testDBM6.addConstraint(2,0, bound_to_constraint(2, strict));
    testDBM6.addConstraint(2,1, bound_to_constraint(1, weak));
    testDBM6.addConstraint(2,2, zero_le);
    return testDBM6;
}

DBM testDBM7()
{
    // Make a seventh test DBM - empty
    DBM testDBM7(make_c2());
    testDBM7.addConstraint(0,0, zero_le);
    testDBM7.addConstraint(0,1, bound_to_constraint(-3, weak));
    testDBM7.addConstraint(0,2, bound_to_constraint(-1, weak));
    testDBM7.addConstraint(1,0, bound_to_constraint(3, weak));
    testDBM7.addConstraint(1,1, zero_le);
    testDBM7.addConstraint(1,2, bound_to_constraint(3, weak));
    testDBM7.addConstraint(2,0, bound_to_constraint(6, strict));
    testDBM7.addConstraint(2,1, bound_to_constraint(3, weak));
    testDBM7.addConstraint(2,2, zero_le);
    return testDBM7;
}

DBM testDBM8()
{
    DBM testDBM8(make_c3());
    testDBM8.addConstraint(0,1, bound_to_constraint(-1, weak));
    testDBM8.addConstraint(3,1, bound_to_constraint(6, weak));
    testDBM8.addConstraint(3,2, bound_to_constraint(4, weak));
    return testDBM8;
}

DBM testDBM9()
{
    DBM testDBM9(make_c3());
    testDBM9.addConstraint(0,1, bound_to_constraint(-1, weak));
    testDBM9.addConstraint(3,2, bound_to_constraint(4, weak));
    return testDBM9;
}

DBM testDBM10()
{
    DBM testDBM10(make_c3());
    testDBM10.addConstraint(3,1, bound_to_constraint(6, weak));
    testDBM10.addConstraint(3,2, bound_to_constraint(4, weak));
    return testDBM10;
}

DBM testDBM11()
{
    DBM testDBM11(make_c3());
    testDBM11.addConstraint(2,0,bound_to_constraint(3, weak));
    return testDBM11;
}

TEST(DBMTest, DefaultIsInfty)
{
  DBM INFTYDBM(make_c2());
  for(size_t i = 0; i <= make_c2()->size();i++) {
    for(size_t j = 0; j < make_c2()->size(); j++){
      if(i == j || i == 0){
        INFTYDBM.addConstraint(i,j, zero_le);
      }
      else {
        INFTYDBM.addConstraint(i,j, infinity);
      }
    }
  }
  DBM defaultDBM(make_c2());
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
    EXPECT_FALSE(testDBM1().cf().emptiness());
    EXPECT_TRUE(testDBM2().cf().emptiness());
    EXPECT_FALSE(testDBM3().cf().emptiness());
    EXPECT_TRUE(testDBM4().cf().emptiness());
    EXPECT_TRUE(testDBM5().cf().emptiness());
    EXPECT_FALSE(testDBM6().cf().emptiness());
    EXPECT_FALSE(testDBM7().cf().emptiness());
    EXPECT_FALSE(DBM(make_c2()).cf().emptiness());
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
    EXPECT_TRUE(emptyDBM3().cf().emptiness());
    EXPECT_EQ(emptyDBM3(), emptyDBM3().cf());
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
    DBM expected(make_c2());
    expected.addConstraint(0,0, zero_le);
    expected.addConstraint(0,1, bound_to_constraint(-3, weak));
    expected.addConstraint(0,2, bound_to_constraint(-8, weak));
    expected.addConstraint(1,0, infinity);
    expected.addConstraint(1,1, zero_le);
    expected.addConstraint(1,2, bound_to_constraint(-5, weak));
    expected.addConstraint(2,0, infinity);
    expected.addConstraint(2,1, bound_to_constraint(7, weak));
    expected.addConstraint(2,2, zero_le);

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
    DBM expected(make_c2());
    expected.addConstraint(0,0, zero_le);
    expected.addConstraint(0,1, bound_to_constraint(-1, weak));
    expected.addConstraint(0,2, bound_to_constraint(-1, weak));
    expected.addConstraint(1,0, bound_to_constraint(1, weak));
    expected.addConstraint(1,1, zero_le);
    expected.addConstraint(1,2, zero_le);
    expected.addConstraint(2,0, bound_to_constraint(2, strict));
    expected.addConstraint(2,1, bound_to_constraint(1, strict));
    expected.addConstraint(2,2, zero_le);

    EXPECT_EQ(expected, canonical);
}

TEST(DBMTest, CanonicalDBM7)
{
    DBM canonical(testDBM7());
    canonical.cf();
    EXPECT_FALSE(canonical.emptiness());

    // DBM in canonical form (expected result)
    DBM expected(make_c2());
    expected.addConstraint(0,0, zero_le);
    expected.addConstraint(0,1, bound_to_constraint(-3, weak));
    expected.addConstraint(0,2, bound_to_constraint(-1, weak));
    expected.addConstraint(1,0, bound_to_constraint(3, weak));
    expected.addConstraint(1,1, zero_le);
    expected.addConstraint(1,2, bound_to_constraint(2, weak));
    expected.addConstraint(2,0, bound_to_constraint(6, strict));
    expected.addConstraint(2,1, bound_to_constraint(3, strict));
    expected.addConstraint(2,2, zero_le);

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
  DBM expected(make_c2());
  expected.addConstraint(0,0, zero_le);
  expected.addConstraint(0,1, zero_le);
  expected.addConstraint(0,2, zero_le);
  expected.addConstraint(1,0, bound_to_constraint(3, strict));
  expected.addConstraint(1,1, zero_le);
  expected.addConstraint(1,2, bound_to_constraint(3, strict));
  expected.addConstraint(2,0, bound_to_constraint(7, strict));
  expected.addConstraint(2,1, bound_to_constraint(7, strict));
  expected.addConstraint(2,2, zero_le);

  EXPECT_EQ(expected, strict_pred);
}

TEST(DBMTest, AddDBM1)
{
    DBM add(testDBM1());
    add.addConstraint(0,1, bound_to_constraint(-2, weak));

    DBM expected(make_c2());
    expected.addConstraint(0,0, zero_le);
    expected.addConstraint(0,1, bound_to_constraint(-2, weak));
    expected.addConstraint(0,2, bound_to_constraint(-5, weak));
    expected.addConstraint(1,0, bound_to_constraint(3, weak));
    expected.addConstraint(1,1, zero_le);
    expected.addConstraint(1,2, infinity);
    expected.addConstraint(2,0, bound_to_constraint(7, weak));
    expected.addConstraint(2,1, infinity);
    expected.addConstraint(2,2, zero_le);

    EXPECT_EQ(expected, add);
}

TEST(DBMTest, AddCanonicalDBM1)
{
    DBM add_canonical(testDBM1());
    add_canonical.addConstraint(0,1, bound_to_constraint(-2, weak));
    add_canonical.cf();

    DBM expected(make_c2());
    expected.addConstraint(0,0, zero_le);
    expected.addConstraint(0,1, bound_to_constraint(-2, weak));
    expected.addConstraint(0,2, bound_to_constraint(-5, weak));
    expected.addConstraint(1,0, bound_to_constraint(3, weak));
    expected.addConstraint(1,1, zero_le);
    expected.addConstraint(1,2, bound_to_constraint(-2, weak));
    expected.addConstraint(2,0, bound_to_constraint(7, weak));
    expected.addConstraint(2,1, bound_to_constraint(5, weak));
    expected.addConstraint(2,2, zero_le);

    EXPECT_EQ(expected, add_canonical);
}

// TODO: The following test is copied from the original, but it should be
// performed on the DBM that has not been changed to canonical form, I think.
TEST(DBMTest, CanonicalBound3DBM2)
{
    DBM bound3(testDBM2());
    bound3.cf();
    bound3.bound(3);
    bound3.cf();

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

    DBM expected(make_c2());
    expected.addConstraint(0,0, zero_le);
    expected.addConstraint(0,1, bound_to_constraint(-3, weak));
    expected.addConstraint(0,2, bound_to_constraint(-1, weak));
    expected.addConstraint(1,0, bound_to_constraint(1, weak));
    expected.addConstraint(1,1, zero_le);
    expected.addConstraint(1,2, zero_le);
    expected.addConstraint(2,0, bound_to_constraint(2, strict));
    expected.addConstraint(2,1, bound_to_constraint(1, strict));
    expected.addConstraint(2,2, zero_le);

    EXPECT_EQ(expected, left);

    left.cf();
    EXPECT_TRUE(left.emptiness());
}

TEST(DBMTest, IntersectDBM8DBM6)
{
    DBM left(testDBM7());
    left.cf();
    DBM right(testDBM6());
    right.cf();

    left.intersect(right);

    DBM expected(make_c2());
    expected.addConstraint(0,0, zero_le);
    expected.addConstraint(0,1, bound_to_constraint(-3, weak));
    expected.addConstraint(0,2, bound_to_constraint(-1, weak));
    expected.addConstraint(1,0, bound_to_constraint(1, weak));
    expected.addConstraint(1,1, zero_le);
    expected.addConstraint(1,2, zero_le);
    expected.addConstraint(2,0, bound_to_constraint(2, strict));
    expected.addConstraint(2,1, bound_to_constraint(1, strict));
    expected.addConstraint(2,2, zero_le);

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

    DBM expected(make_c2());
    expected.addConstraint(0,0, zero_le);
    expected.addConstraint(0,1, bound_to_constraint(-3, weak));
    expected.addConstraint(0,2, bound_to_constraint(-1, weak));
    expected.addConstraint(1,0, bound_to_constraint(1, weak));
    expected.addConstraint(1,1, zero_le);
    expected.addConstraint(1,2, zero_le);
    expected.addConstraint(2,0, bound_to_constraint(2, strict));
    expected.addConstraint(2,1, bound_to_constraint(1, strict));
    expected.addConstraint(2,2, zero_le);

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

    DBM expected(make_c2());
    expected.addConstraint(0,0, zero_le);
    expected.addConstraint(0,1, bound_to_constraint(-3, weak));
    expected.addConstraint(0,2, bound_to_constraint(-1, weak));
    expected.addConstraint(1,0, bound_to_constraint(1, weak));
    expected.addConstraint(1,1, zero_le);
    expected.addConstraint(1,2, zero_le);
    expected.addConstraint(2,0, bound_to_constraint(2, strict));
    expected.addConstraint(2,1, bound_to_constraint(1, strict));
    expected.addConstraint(2,2, zero_le);

    EXPECT_EQ(expected, *left);
    left->cf();
    EXPECT_TRUE(left->emptiness());
    EXPECT_EQ(emptyDBM3(), *left);
}

TEST(DBMTest, ccrepA)
{
  DBM ccrepA(make_c4());
  for (int i=0; i<5; i++) {
    ccrepA.addConstraint(i,0, zero_le);
  }

  ccrepA.cf();
  EXPECT_FALSE(ccrepA.emptiness());

  DBM expected(make_c4());
  for (int i=0; i < 5; i++) {
      for (int j=0; j < 5; j++) {
          expected.addConstraint(i,j, zero_le);
      }
  }
  EXPECT_EQ(expected, ccrepA);

}

TEST(DBMTest, empty)
{
    DBM expected(make_c2());
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
    DBM test(make_c2());
    test.addConstraint(0,2, bound_to_constraint(-3, weak));
    test.addConstraint(1,0, bound_to_constraint(2, weak));
    test.addConstraint(2,0, bound_to_constraint(2, weak));

    test.cf();
    EXPECT_TRUE(test.emptiness());
    EXPECT_EQ(emptyDBM3(), test);
}

TEST(DBMTest, Bound1)
{
    /* Make DBM to try to test the correctnes of bound(maxc) */
    DBM test(make_c2());
    test.addConstraint(0,0, zero_le);
    test.addConstraint(0,1, bound_to_constraint(-3, weak));
    test.addConstraint(0,2, infinity);
    test.addConstraint(1,0, infinity);
    test.addConstraint(1,1, zero_le);
    test.addConstraint(1,2, infinity);
    test.addConstraint(2,0, infinity);
    test.addConstraint(2,1, infinity);
    test.addConstraint(2,2, zero_le);

    DBM canonical(test);
    canonical.cf();
    EXPECT_EQ(test, canonical);
    EXPECT_FALSE(canonical.emptiness());

    test.bound(2);
    test.cf();
    EXPECT_FALSE(test.emptiness());

    DBM expected(make_c2());
    expected.addConstraint(0,0, zero_le);
    expected.addConstraint(0,1, bound_to_constraint(-2, strict));
    expected.addConstraint(0,2, infinity);
    expected.addConstraint(1,0, infinity);
    expected.addConstraint(1,1, zero_le);
    expected.addConstraint(1,2, infinity);
    expected.addConstraint(2,0, infinity);
    expected.addConstraint(2,1, infinity);
    expected.addConstraint(2,2, zero_le);

    EXPECT_EQ(expected, test);
}

TEST(DBMTest, Bound2)
{
    /* Make DBM to try to test the correctnes of bound(maxc) */
    DBM test(make_c2());
    test.addConstraint(0,0, zero_le);
    test.addConstraint(0,1, bound_to_constraint(-5, weak));
    test.addConstraint(0,2, infinity);
    test.addConstraint(1,0, infinity);
    test.addConstraint(1,1, zero_le);
    test.addConstraint(1,2, infinity);
    test.addConstraint(2,0, infinity);
    test.addConstraint(2,1, bound_to_constraint(2, weak));
    test.addConstraint(2,2, zero_le);

    DBM canonical(test);
    canonical.cf();
    EXPECT_EQ(test, canonical);
    EXPECT_FALSE(canonical.emptiness());

    test.bound(4);
    test.cf();
    EXPECT_FALSE(test.emptiness());

    DBM expected(make_c2());
    expected.addConstraint(0,0, zero_le);
    expected.addConstraint(0,1, bound_to_constraint(-4, strict));
    expected.addConstraint(0,2, infinity);
    expected.addConstraint(1,0, infinity);
    expected.addConstraint(1,1, zero_le);
    expected.addConstraint(1,2, infinity);
    expected.addConstraint(2,0, infinity);
    expected.addConstraint(2,1, infinity);
    expected.addConstraint(2,2, zero_le);

    EXPECT_EQ(expected, test);
}

TEST(DBMTest, Bound3)
{
    /* Make DBM to try to test the correctnes of bound(maxc) */
    DBM test(make_c2());
    test.addConstraint(0,0, zero_le);
    test.addConstraint(0,1, bound_to_constraint(-5, weak));
    test.addConstraint(0,2, infinity);
    test.addConstraint(1,0, infinity);
    test.addConstraint(1,1, zero_le);
    test.addConstraint(1,2, infinity);
    test.addConstraint(2,0, bound_to_constraint(1, weak));
    test.addConstraint(2,1, bound_to_constraint(2, weak));
    test.addConstraint(2,2, zero_le);

    // DBM in canonical form, test canonisation works for this instance.
    DBM canonical(make_c2());
    canonical.addConstraint(0,0, zero_le);
    canonical.addConstraint(0,1, bound_to_constraint(-5, weak));
    canonical.addConstraint(0,2, infinity);
    canonical.addConstraint(1,0, infinity);
    canonical.addConstraint(1,1, zero_le);
    canonical.addConstraint(1,2, infinity);
    canonical.addConstraint(2,0, bound_to_constraint(1, weak));
    canonical.addConstraint(2,1, bound_to_constraint(-4, weak));
    canonical.addConstraint(2,2, zero_le);

    test.cf();
    EXPECT_EQ(canonical, test);
    EXPECT_FALSE(test.emptiness());

    // Finally test bounding.
    DBM expected(make_c2());
    expected.addConstraint(0,0, zero_le);
    expected.addConstraint(0,1, bound_to_constraint(-4, strict));
    expected.addConstraint(0,2, infinity);
    expected.addConstraint(1,0, infinity);
    expected.addConstraint(1,1, zero_le);
    expected.addConstraint(1,2, infinity);
    expected.addConstraint(2,0, bound_to_constraint(1, weak));
    expected.addConstraint(2,1, bound_to_constraint(-3, strict));
    expected.addConstraint(2,2, zero_le);

    test.bound(4);
    test.cf();
    EXPECT_FALSE(test.emptiness());
    EXPECT_EQ(expected, test);
}

TEST(DBMTest, Bound4)
{
    /* Make DBM to try to test the correctnes of bound(maxc) */
    DBM test(make_c2());
    test.addConstraint(0,0, zero_le);
    test.addConstraint(0,1, bound_to_constraint(-5, weak));
    test.addConstraint(0,2, infinity);
    test.addConstraint(1,0, infinity);
    test.addConstraint(1,1, zero_le);
    test.addConstraint(1,2, infinity);
    test.addConstraint(2,0, zero_le);
    test.addConstraint(2,1, bound_to_constraint(2, weak));
    test.addConstraint(2,2, zero_le);

    // DBM in canonical form, test canonisation works for this instance.
    DBM canonical(make_c2());
    canonical.addConstraint(0,0, zero_le);
    canonical.addConstraint(0,1, bound_to_constraint(-5, weak));
    canonical.addConstraint(0,2, infinity);
    canonical.addConstraint(1,0, infinity);
    canonical.addConstraint(1,1, zero_le);
    canonical.addConstraint(1,2, infinity);
    canonical.addConstraint(2,0, zero_le);
    canonical.addConstraint(2,1, bound_to_constraint(-5, weak));
    canonical.addConstraint(2,2, zero_le);

    test.cf();
    EXPECT_EQ(canonical, test);
    EXPECT_FALSE(test.emptiness());

    // Finally test bounding.
    DBM expected(make_c2());
    expected.addConstraint(0,0, zero_le);
    expected.addConstraint(0,1, bound_to_constraint(-4, strict));
    expected.addConstraint(0,2, infinity);
    expected.addConstraint(1,0, infinity);
    expected.addConstraint(1,1, zero_le);
    expected.addConstraint(1,2, infinity);
    expected.addConstraint(2,0, zero_le);
    expected.addConstraint(2,1, bound_to_constraint(-4, strict));
    expected.addConstraint(2,2, zero_le);

    test.bound(4);
    test.cf();
    EXPECT_FALSE(test.emptiness());
    EXPECT_EQ(expected, test);
}

TEST(DBMTest, Bound5)
{
    /* Make DBM to try to test the correctnes of bound(maxc) */
    DBM test(make_c2());
    test.addConstraint(0,0, zero_le);
    test.addConstraint(0,1, bound_to_constraint(-5, weak));
    test.addConstraint(0,2, infinity);
    test.addConstraint(1,0, infinity);
    test.addConstraint(1,1, zero_le);
    test.addConstraint(1,2, infinity);
    test.addConstraint(2,0, bound_to_constraint(-1, weak));
    test.addConstraint(2,1, bound_to_constraint(2, weak));
    test.addConstraint(2,2, zero_le);

    // DBM in canonical form, test canonisation works for this instance.
    DBM canonical(make_c2());
    canonical.addConstraint(0,0, zero_le);
    canonical.addConstraint(0,1, bound_to_constraint(-5, weak));
    canonical.addConstraint(0,2, infinity);
    canonical.addConstraint(1,0, infinity);
    canonical.addConstraint(1,1, zero_le);
    canonical.addConstraint(1,2, infinity);
    canonical.addConstraint(2,0, bound_to_constraint(-1, weak));
    canonical.addConstraint(2,1, bound_to_constraint(-6, weak));
    canonical.addConstraint(2,2, zero_le);

    test.cf();
    EXPECT_EQ(canonical, test);
    EXPECT_FALSE(test.emptiness());

    // Finally test bounding.
    DBM expected(make_c2());
    expected.addConstraint(0,0, zero_le);
    expected.addConstraint(0,1, bound_to_constraint(-4, strict));
    expected.addConstraint(0,2, infinity);
    expected.addConstraint(1,0, infinity);
    expected.addConstraint(1,1, zero_le);
    expected.addConstraint(1,2, infinity);
    expected.addConstraint(2,0, bound_to_constraint(-1, weak));
    expected.addConstraint(2,1, bound_to_constraint(-4, strict));
    expected.addConstraint(2,2, zero_le);

    test.bound(4);
    EXPECT_EQ(expected, test);
    test.cf();
    EXPECT_FALSE(test.emptiness());
}

TEST(DBMTest, Bound6)
{
    /* Make DBM to try to test the correctnes of bound(maxc) */
    DBM test(make_c2());
    test.addConstraint(0,0, zero_le);
    test.addConstraint(0,1, bound_to_constraint(-2, weak));
    test.addConstraint(0,2, infinity);
    test.addConstraint(1,0, infinity);
    test.addConstraint(1,1, zero_le);
    test.addConstraint(1,2, bound_to_constraint(1, strict));
    test.addConstraint(2,0, infinity);
    test.addConstraint(2,1, infinity);
    test.addConstraint(2,2, zero_le);

    // DBM in canonical form, test canonisation works for this instance.
    DBM canonical(make_c2());
    canonical.addConstraint(0,0, zero_le);
    canonical.addConstraint(0,1, bound_to_constraint(-2, weak));
    canonical.addConstraint(0,2, bound_to_constraint(-1, strict));
    canonical.addConstraint(1,0, infinity);
    canonical.addConstraint(1,1, zero_le);
    canonical.addConstraint(1,2, bound_to_constraint(1, strict));
    canonical.addConstraint(2,0, infinity);
    canonical.addConstraint(2,1, infinity);
    canonical.addConstraint(2,2, zero_le);

    test.cf();
    EXPECT_EQ(canonical, test);
    EXPECT_FALSE(test.emptiness());

    // Finally test bounding.
    DBM expected(make_c2());
    expected.addConstraint(0,0, zero_le);
    expected.addConstraint(0,1, bound_to_constraint(-1, strict));
    expected.addConstraint(0,2, bound_to_constraint(-1, strict));
    expected.addConstraint(1,0, infinity);
    expected.addConstraint(1,1, zero_le);
    expected.addConstraint(1,2, bound_to_constraint(1, strict));
    expected.addConstraint(2,0, infinity);
    expected.addConstraint(2,1, infinity);
    expected.addConstraint(2,2, zero_le);

    test.bound(1);
    test.cf();
    EXPECT_FALSE(test.emptiness());
    EXPECT_EQ(expected, test);
}

TEST(DBMTest, Empty1)
{
    DBM test(make_c2());
    test.addConstraint(0,0, zero_le);
    test.addConstraint(0,1, bound_to_constraint(-5, weak));
    test.addConstraint(0,2, infinity);
    test.addConstraint(1,0, infinity);
    test.addConstraint(1,1, zero_le);
    test.addConstraint(1,2, infinity);
    test.addConstraint(2,0, infinity);
    test.addConstraint(2,1, bound_to_constraint(2, weak));
    test.addConstraint(2,2, zero_le);

    // DBM is already in cf
    DBM canonical(test);
    canonical.cf();
    EXPECT_EQ(test, canonical);
    EXPECT_FALSE(canonical.emptiness());

    // Normalize
    DBM expected(make_c2());
    expected.addConstraint(0,0, zero_le);
    expected.addConstraint(0,1, bound_to_constraint(-4, strict));
    expected.addConstraint(0,2, infinity);
    expected.addConstraint(1,0, infinity);
    expected.addConstraint(1,1, zero_le);
    expected.addConstraint(1,2, infinity);
    expected.addConstraint(2,0, infinity);
    expected.addConstraint(2,1, infinity);
    expected.addConstraint(2,2, zero_le);

    test.bound(4);
    test.cf();
    EXPECT_EQ(expected, test);
    EXPECT_FALSE(test.emptiness());

    DBM canonical_bound(test);
    canonical_bound.cf();
    EXPECT_EQ(test, canonical_bound);
}

TEST(DBMTest, Empty2)
{
    DBM test(testDBM8());

    // DBM is already in cf
    DBM canonical(test);
    canonical.cf();
    EXPECT_EQ(test, canonical);
    EXPECT_FALSE(canonical.emptiness());
}

TEST(DBMTest, Empty3)
{
    DBM test(testDBM9());

    // DBM is already in cf
    DBM canonical(test);
    canonical.cf();
    EXPECT_EQ(test, canonical);
    EXPECT_FALSE(canonical.emptiness());
}

TEST(DBMTest, Empty4)
{
    DBM test(testDBM10());

    // DBM is already in cf
    DBM canonical(test);
    canonical.cf();
    EXPECT_EQ(test, canonical);
    EXPECT_FALSE(canonical.emptiness());
}

TEST(DBMTest, Empty5)
{
    DBM test(testDBM11());

    DBM canonical(make_c3());
    canonical.addConstraint(0,0, zero_le);
    canonical.addConstraint(0,1, zero_le);
    canonical.addConstraint(0,2, zero_le);
    canonical.addConstraint(0,3, zero_le);
    canonical.addConstraint(1,0, infinity);
    canonical.addConstraint(1,1, zero_le);
    canonical.addConstraint(1,2, infinity);
    canonical.addConstraint(1,3, infinity);
    canonical.addConstraint(2,0, bound_to_constraint(3, weak));
    canonical.addConstraint(2,1, bound_to_constraint(3, weak));
    canonical.addConstraint(2,2, zero_le);
    canonical.addConstraint(2,3, bound_to_constraint(3, weak));
    canonical.addConstraint(3,0, infinity);
    canonical.addConstraint(3,1, infinity);
    canonical.addConstraint(3,2, infinity);
    canonical.addConstraint(3,3, zero_le);

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

  DBM expected(make_c3());
  expected.addConstraint(0,0, zero_le);
  expected.addConstraint(0,1, bound_to_constraint(-1, weak));
  expected.addConstraint(0,2, zero_le);
  expected.addConstraint(0,3, zero_le);
  expected.addConstraint(1,0, infinity);
  expected.addConstraint(1,1, zero_le);
  expected.addConstraint(1,2, infinity);
  expected.addConstraint(1,3, infinity);
  expected.addConstraint(2,0, bound_to_constraint(3, weak));
  expected.addConstraint(2,1, bound_to_constraint(3, weak));
  expected.addConstraint(2,2, zero_le);
  expected.addConstraint(2,3, bound_to_constraint(3, weak));
  expected.addConstraint(3,0, infinity);
  expected.addConstraint(3,1, bound_to_constraint(6, weak));
  expected.addConstraint(3,2, bound_to_constraint(4, weak));
  expected.addConstraint(3,3, zero_le);

  EXPECT_EQ(expected, left);

  DBM canonical(make_c3());
  canonical.addConstraint(0,0, zero_le);
  canonical.addConstraint(0,1, bound_to_constraint(-1, weak));
  canonical.addConstraint(0,2, zero_le);
  canonical.addConstraint(0,3, zero_le);
  canonical.addConstraint(1,0, infinity);
  canonical.addConstraint(1,1, zero_le);
  canonical.addConstraint(1,2, infinity);
  canonical.addConstraint(1,3, infinity);
  canonical.addConstraint(2,0, bound_to_constraint(3, weak));
  canonical.addConstraint(2,1, bound_to_constraint(2, weak));
  canonical.addConstraint(2,2, zero_le);
  canonical.addConstraint(2,3, bound_to_constraint(3, weak));
  canonical.addConstraint(3,0, bound_to_constraint(7, weak));
  canonical.addConstraint(3,1, bound_to_constraint(6, weak));
  canonical.addConstraint(3,2, bound_to_constraint(4, weak));
  canonical.addConstraint(3,3, zero_le);

  left.cf();
  EXPECT_EQ(canonical, left);
}

TEST(DBMTest, IntersectDBM11DBM9)
{
  DBM left(testDBM11());
  DBM right(testDBM9());
  left.intersect(right);

  DBM expected(make_c3());
  expected.addConstraint(0,0, zero_le);
  expected.addConstraint(0,1, bound_to_constraint(-1, weak));
  expected.addConstraint(0,2, zero_le);
  expected.addConstraint(0,3, zero_le);
  expected.addConstraint(1,0, infinity);
  expected.addConstraint(1,1, zero_le);
  expected.addConstraint(1,2, infinity);
  expected.addConstraint(1,3, infinity);
  expected.addConstraint(2,0, bound_to_constraint(3, weak));
  expected.addConstraint(2,1, infinity);
  expected.addConstraint(2,2, zero_le);
  expected.addConstraint(2,3, infinity);
  expected.addConstraint(3,0, infinity);
  expected.addConstraint(3,1, infinity);
  expected.addConstraint(3,2, bound_to_constraint(4, weak));
  expected.addConstraint(3,3, zero_le);
  EXPECT_EQ(expected, left);

  DBM canonical(make_c3());
  canonical.addConstraint(0,0, zero_le);
  canonical.addConstraint(0,1, bound_to_constraint(-1, weak));
  canonical.addConstraint(0,2, zero_le);
  canonical.addConstraint(0,3, zero_le);
  canonical.addConstraint(1,0, infinity);
  canonical.addConstraint(1,1, zero_le);
  canonical.addConstraint(1,2, infinity);
  canonical.addConstraint(1,3, infinity);
  canonical.addConstraint(2,0, bound_to_constraint(3, weak));
  canonical.addConstraint(2,1, bound_to_constraint(2, weak));
  canonical.addConstraint(2,2, zero_le);
  canonical.addConstraint(2,3, bound_to_constraint(3, weak));
  canonical.addConstraint(3,0, bound_to_constraint(7, weak));
  canonical.addConstraint(3,1, bound_to_constraint(6, weak));
  canonical.addConstraint(3,2, bound_to_constraint(4, weak));
  canonical.addConstraint(3,3, zero_le);

  left.cf();
  EXPECT_EQ(canonical, left);
}

TEST(DBMTest, IntersectDBM11DBM10)
{
  DBM left(testDBM11());
  DBM right(testDBM10());
  left.intersect(right);

  DBM expected(make_c3());
  expected.addConstraint(0,0, zero_le);
  expected.addConstraint(0,1, zero_le);
  expected.addConstraint(0,2, zero_le);
  expected.addConstraint(0,3, zero_le);
  expected.addConstraint(1,0, infinity);
  expected.addConstraint(1,1, zero_le);
  expected.addConstraint(1,2, infinity);
  expected.addConstraint(1,3, infinity);
  expected.addConstraint(2,0, bound_to_constraint(3, weak));
  expected.addConstraint(2,1, infinity);
  expected.addConstraint(2,2, zero_le);
  expected.addConstraint(2,3, infinity);
  expected.addConstraint(3,0, infinity);
  expected.addConstraint(3,1, bound_to_constraint(6, weak));
  expected.addConstraint(3,2, bound_to_constraint(4, weak));
  expected.addConstraint(3,3, zero_le);
  EXPECT_EQ(expected, left);

  DBM canonical(make_c3());
  canonical.addConstraint(0,0, zero_le);
  canonical.addConstraint(0,1, zero_le);
  canonical.addConstraint(0,2, zero_le);
  canonical.addConstraint(0,3, zero_le);
  canonical.addConstraint(1,0, infinity);
  canonical.addConstraint(1,1, zero_le);
  canonical.addConstraint(1,2, infinity);
  canonical.addConstraint(1,3, infinity);
  canonical.addConstraint(2,0, bound_to_constraint(3, weak));
  canonical.addConstraint(2,1, bound_to_constraint(3, weak));
  canonical.addConstraint(2,2, zero_le);
  canonical.addConstraint(2,3, bound_to_constraint(3, weak));
  canonical.addConstraint(3,0, bound_to_constraint(7, weak));
  canonical.addConstraint(3,1, bound_to_constraint(6, weak));
  canonical.addConstraint(3,2, bound_to_constraint(4, weak));
  canonical.addConstraint(3,3, zero_le);

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
