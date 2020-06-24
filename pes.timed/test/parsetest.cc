/**
  * Unit tests for Parsing.
  *
  * @author Jeroen Keiren
  * @copyright MIT Licence, see the accompanying LICENCE.txt.
  */

#include <limits>
#include <string>
#include "parse.hh"
#include "gtest/gtest.h"

#define QUOTE(name) #name
#define STR(macro) QUOTE(macro)
#define EXAMPLES_DIR_NAME STR(EXAMPLES_DIR)

std::string AFSpecA1String(
  "CLOCKS :{x1}\n"
  "CONTROL :{p1(2)}\n"
  "PREDICATE: {X1}\n"
  "START: X1\n"
  "EQUATIONS: {\n"
    "1: mu X1 = p1 == 1\n"
    "    || ((\\forall time( \n"
  "( (p1 == 0) -> (X1[p1=0][x1]))\n"
  "&& ( (p1 == 0) -> (X1[p1=1]))\n"
  "&& ( (p1 == 1) -> (X1[p1=1])))))\n"
  "}\n"
  "INVARIANT:\n"
    "  p1 == 0 -> x1 <= 2\n");

TEST(ParseTest, ParseFile)
{
  pes p;
  std::string filename(std::string(EXAMPLES_DIR_NAME) + "/CorrectnessTestSuite/Invalid/Liveness/AFSpecA1.in");
  ASSERT_NO_THROW(parse_pes(filename, false, p));

  EXPECT_EQ(1, p.clocks()->size());
  EXPECT_EQ(1, p.atomic()->size());
  EXPECT_EQ("X1", p.start_predicate());
}

TEST(ParseTest, ParseNonexistantFile)
{
  pes p;
  std::string filename(std::string(EXAMPLES_DIR_NAME) + "/Nonexistant.in");
  EXPECT_ANY_THROW(parse_pes(filename, false, p));
}

TEST(ParseTest, ParseString)
{
  pes p;
  ASSERT_NO_THROW(parse_pes_from_string(AFSpecA1String, false, p));

  EXPECT_EQ(1, p.clocks()->size());
  EXPECT_EQ(1, p.atomic()->size());
  EXPECT_EQ("X1", p.start_predicate());
}
