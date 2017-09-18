/**
  * Unit tests for prover.
  *
  * @author Jeroen Keiren
  * @copyright MIT Licence, see the accompanying LICENCE.txt.
  */

#include <limits>
#include <string>
#include "proof.hh"
#include "parse.hh"
#include "gtest/gtest.h"

static
std::string AllActBug(
    "CLOCKS: {x}\n"
    "CONTROL: {p=1}\n"
    "INITIALLY: x == 0\n"
    "PREDICATE: {X}\n"
    "START: X\n"
    "EQUATIONS: {\n"
    "1: mu X = \\AllAct(X) && p==1\n"
    "}\n"
    "INVARIANT:\n"
    "	p == 1 -> x == 0\n"
    "TRANSITIONS:\n"
    "	(p==1)->(p=2);\n");

TEST(ProofTest, AllActBugTest)
{
  pes p;
  ASSERT_NO_THROW(parse_pes_from_string(AllActBug, false, p));

  prover_options options;
  prover pr(p, options);
  EXPECT_FALSE(pr.do_proof_init(p));
}

TEST(ProofTest, AllActBugTestPlace)
{
  pes p;
  ASSERT_NO_THROW(parse_pes_from_string(AllActBug, false, p));

  prover_options options;
  prover pr(p, options);
  DBMList placeholder(DBM(p.initial_clock_zone()->clocks_size(), p.clocks()));
  EXPECT_FALSE(pr.do_proof_init(p, &placeholder));
}

static
std::string ExistsBug(
    "#define CA 3\n"
    "CLOCKS :{x1}\n"
    "CONTROL :{p1(1)}\n"
    "PREDICATE: {X}\n"
    "START: X\n"
    "EQUATIONS: {\n"
    "1: nu X = (\\exists time(x1 <= 2 && \\forall time(x1 >= 4)))\n"
    "	}\n");

TEST(ProofTest, ExistsBugTest)
{
  pes p;
  ASSERT_NO_THROW(parse_pes_from_string(ExistsBug, false, p));

  prover_options options;
  prover pr(p, options);

  EXPECT_FALSE(pr.do_proof_init(p));

}

// In the following example, the property does not hold. However, the placeholder
// that is computed for which the property does hold should be non-empty.
static
std::string ExistsRel(
    "CLOCKS: {x1,x2}\n"
    "CONTROL: {p1}\n"
    "INITIALLY: x1 <= 2 && x2<=1\n"
    "PREDICATE: {X}\n"
    "START: X\n"
    "EQUATIONS: {\n"
    "1: mu X = \\exists time\\rel[x1 <= 3](x2==3)\n"
    "}\n"
    "TRANSITIONS:\n"
    );

TEST(ProofTest, ExistsRelTestFalse)
{
  pes p;
  ASSERT_NO_THROW(parse_pes_from_string(ExistsRel, false, p));

  prover_options options;
  prover pr(p, options);

  DBMList placeholder(DBM(p.initial_clock_zone()->clocks_size(), p.clocks()));

  EXPECT_FALSE(pr.do_proof_init(p, &placeholder));
  placeholder.cf();

  DBM minimum_region(p.initial_clock_zone()->clocks_size(), p.clocks());
  minimum_region.addConstraint(1,0, clock_value(2, false));
  minimum_region.addConstraint(2,0, clock_value(1, false));
  minimum_region.addConstraint(1,2, clock_value(0, false));

  DBM maximum_region(p.initial_clock_zone()->clocks_size(), p.clocks());
  maximum_region.addConstraint(0,1, clock_value(0, false));
  maximum_region.addConstraint(0,2, clock_value(0, false));
  maximum_region.addConstraint(2,0, clock_value(3, false));
  maximum_region.addConstraint(1,2, clock_value(0, false));

  DBMList minimum_placeholder(minimum_region);
  minimum_placeholder.cf();
  EXPECT_TRUE(minimum_placeholder <= placeholder);

  DBMList maximum_placeholder(maximum_region);
  maximum_placeholder.cf();
  EXPECT_TRUE(placeholder <= maximum_placeholder);


  if(!(minimum_placeholder <= placeholder) || !(placeholder <= maximum_placeholder))
  {
    std::cerr << "Resulting placeholder: " << placeholder << std::endl;
    std::cerr << "Minimal placeholder: " << minimum_placeholder << std::endl;
    std::cerr << "Maximal placeholder: " << maximum_placeholder << std::endl;
  }
}

// In the following example, the initial region is exactly equal to the
// part of the initial region that must be included in the placeholder.
// Therefore, the property must hold.
static
std::string ExistsRelSmallRegion(
    "CLOCKS: {x1,x2}\n"
    "CONTROL: {p1}\n"
    "INITIALLY: x1 <= 2 && x2<=1 && x2 - x1 >= 0\n"
    "PREDICATE: {X}\n"
    "START: X\n"
    "EQUATIONS: {\n"
    "1: mu X = \\exists time\\rel[x1 <= 3](x2==3)\n"
    "}\n"
    "TRANSITIONS:\n"
    );

TEST(ProofTest, ExistsRelTestTrue)
{
  pes p;
  ASSERT_NO_THROW(parse_pes_from_string(ExistsRelSmallRegion, false, p));

  prover_options options;
  prover pr(p, options);

  DBMList placeholder(DBM(p.initial_clock_zone()->clocks_size(), p.clocks()));

  EXPECT_TRUE(pr.do_proof_init(p, &placeholder));
  placeholder.cf();

  DBM minimum_region(p.initial_clock_zone()->clocks_size(), p.clocks());
  minimum_region.addConstraint(1,0, clock_value(2, false));
  minimum_region.addConstraint(2,0, clock_value(1, false));
  minimum_region.addConstraint(1,2, clock_value(0, false));

  DBM maximum_region(p.initial_clock_zone()->clocks_size(), p.clocks());
  maximum_region.addConstraint(0,1, clock_value(0, false));
  maximum_region.addConstraint(0,2, clock_value(0, false));
  maximum_region.addConstraint(2,0, clock_value(3, false));
  maximum_region.addConstraint(1,2, clock_value(0, false));

  DBMList minimum_placeholder(minimum_region);
  minimum_placeholder.cf();
  EXPECT_TRUE(minimum_placeholder <= placeholder);

  DBMList maximum_placeholder(maximum_region);
  maximum_placeholder.cf();
  EXPECT_TRUE(placeholder <= maximum_placeholder);


  if(!(minimum_placeholder <= placeholder) || !(placeholder <= maximum_placeholder))
  {
    std::cerr << "Resulting placeholder: " << placeholder << std::endl;
    std::cerr << "Minimal placeholder: " << minimum_placeholder << std::endl;
    std::cerr << "Maximal placeholder: " << maximum_placeholder << std::endl;
  }
}

