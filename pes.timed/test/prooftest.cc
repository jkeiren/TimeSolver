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

static
std::string ForallRelBug(
    "CLOCKS :{x1}\n"
    "CONTROL :{p1}\n"
    "PREDICATE: {X}\n"
    "START: X\n"
    "EQUATIONS: {\n"
    "1: nu X = \\forall time\\rel[x1 >= 0](x1 >= 1)\n"
    "	}\n");

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

TEST(ProofTest, ExistsBugTest)
{
  pes p;
  ASSERT_NO_THROW(parse_pes_from_string(ExistsBug, false, p));

  prover_options options;
  prover pr(p, options);
  EXPECT_FALSE(pr.do_proof_init(p));
}

TEST(ProofTest, ForallRelBugTest)
{
  pes p;
  ASSERT_NO_THROW(parse_pes_from_string(ForallRelBug, false, p));

  prover_options options;
  prover pr(p, options);
  EXPECT_TRUE(pr.do_proof_init(p));
}
