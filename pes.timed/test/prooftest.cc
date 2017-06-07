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

std::string FDDI4bl(
    "CLOCKS: {x}\n"
    "CONTROL: {p=1}\n"
    "INITIALLY: x == 0\n"
    "PREDICATE: {X}\n"
    "START: X\n"
    "EQUATIONS: {\n"
    "1: mu X = \\forall time\\rel[FALSE](\\AllAct(X)) && p==1\n"
    "}\n"
    "INVARIANT:\n"
    "	p == 1 -> x == 0\n"
    "TRANSITIONS:\n"
    "	(p==1)->(p=2);\n");

TEST(ProofTest, FDDI4blTest)
{
  pes p;
  ASSERT_NO_THROW(parse_pes_from_string(FDDI4bl, false, p));

  prover_options options;
  prover pr(p, options);
  EXPECT_FALSE(pr.do_proof_init(p));
}

TEST(ProofTest, FDDI4blTestPlace)
{
  pes p;
  ASSERT_NO_THROW(parse_pes_from_string(FDDI4bl, false, p));

  prover_options options;
  prover pr(p, options);
  DBMList placeholder(DBM(p.initial_clock_zone()->clocks_size(), p.clocks()));
  EXPECT_FALSE(pr.do_proof_init(p, &placeholder));
}

