# For now, always build with debug symbols
DEBUG = 1

# Detect platform
ifeq ($(OS), Windows_NT)
	UNAME_S := Windows
else
	UNAME_S := $(shell uname -s)
endif

CFLAGS_ALL = -O -Wall
CFLAGS_PROFILE = -pg
CFLAGS_DEBUG = -g
CFLAGS_VALGRIND = -g3

CXXFLAGS_ALL = -O -Wall -Wextra -std=c++11
CXXFLAGS_PROFILE = -pg
CXXFLAGS_DEBUG = -g
#-fsanitize=undefined
# -fsanitize=address
CXXFLAGS_VALGRIND = -g3

LDFLAGS_ALL =
LDFLAGS_PROFILE = -pg -O
LDFLAGS_DEBUG = -g
LDFLAGS_VALGRIND =

# Assume sane defaults from the environment, and we add to this.
CFLAGS += $(CFLAGS_ALL)
CXXFLAGS += $(CXXFLAGS_ALL)
LDFLAGS += $(LDFLAGS_ALL)

# PROFILE=1 can be passed in from the command line, if so, profiling options
# are set
ifeq ($(PROFILE),1)
  CFLAGS += $(CFLAGS_PROFILE)
	CXXFLAGS += $(CXXFLAGS_PROFILE)
	LDFLAGS += $(LDFLAGS_PROFILE)
endif

# DEBUG=1 can be passed in from the command line.
ifeq ($(DEBUG),1)
  CFLAGS += $(CFLAGS_DEBUG)
	CXXFLAGS += $(CXXFLAGS_DEBUG)
	LDFLAGS += $(LDFLAGS_DEBUG)
endif

# VALGRIND=1 can be passed in from the command line.
ifeq ($(VALGRIND),1)
  CFLAGS += $(CFLAGS_VALGRIND)
  CXXFLAGS += $(CXXFLAGS_VALGRIND)
  LDFLAGS += $(LDFLAGS_VALGRIND)
endif

ifeq ($(UNAME_S), Darwin)
	# Stack size set to 4GB for Mac, since terminal hard limit is 64MB
	# My machine has 16GB of RAM
	# This number is the number of bytes in Hex
	LDFLAGS += -Wl,-stack_size,200000000
endif

# Export flags to make sure they are used by submakes, e.g. for testing
export CFLAGS
export CXXFLAGS
export LDFLAGS

FLEX = flex
BISON = bison
INCL_PATH = -I. -Iexternal/cpplogging/include

SRC_FILES := $(wildcard *.cc)
GENERATED_SRC_FILES := pes.lex.cc pes.tab.cc
HEADER_FILES := $(wildcard *.hh)
CHECK_FILES := $(filter-out $(GENERATED_SRC_FILES), $(SRC_FILES) $(HEADER_FILES))


.PHONY: default
default: all

all: timesolver-ta check

doc: timesolver-ta *.hh *.cc
	doxygen pes-timed_Doxyfile

timesolver-ta:	pes.tab.o pes.lex.o ExprNode.o timesolver-ta.o logger.o parse.o
	$(CXX) $(CXXFLAGS) pes.lex.o pes.tab.o ExprNode.o timesolver-ta.o external/cpplogging/logger.o parse.o $(LDFLAGS) -o timesolver-ta

timesolver-ta.o: timesolver-ta.cc DBM.hh ExprNode.hh DBMList.hh sequent_stack.hh proof.hh pes.hh transition.hh comp_ph.hh sequent.hh sequent_cache.hh
	$(CXX) $(CXXFLAGS) -c timesolver-ta.cc $(INCL_PATH)

ExprNode.o: ExprNode.cc ExprNode.hh DBM.hh DBMList.hh bidirectional_map.hh
	$(CXX) $(CXXFLAGS) -c ExprNode.cc $(INCL_PATH)

parse.o: parse.cc parse.hh pes.hh pes.tab.hh pes.lex.hh
	$(CXX) $(CXXFLAGS) -c parse.cc $(INCL_PATH)

pes.lex.o: pes.lex.cc
	$(CXX) $(CXXFLAGS) -c pes.lex.cc $(INCL_PATH) 

pes.lex.cc pes.lex.hh: pes.l ExprNode.hh transition.hh pes.tab.hh
	$(FLEX) --header-file=pes.lex.hh -p -8 -Ce -opes.lex.cc pes.l

pes.tab.o: pes.tab.cc pes.tab.hh DBM.hh
	$(CXX) $(CXXFLAGS) -c pes.tab.cc $(INCL_PATH)

pes.tab.cc pes.tab.hh: pes.y pes.hh ExprNode.hh transition.hh OneDIntArray.hh bidirectional_map.hh
	$(BISON) -t -d -v -o pes.tab.cc pes.y
	
logger.o:
	$(MAKE) -C external/cpplogging

check:
	$(MAKE) -C test check
	
tests:
	$(MAKE) -C test dbmtest
	$(MAKE) -C test dbmlisttest
	$(MAKE) -C test parsetest

checktool: timesolver-ta
	../TATest.py
	
checkall: check checktool
 
clean:
	-echo "Removing all object files!"
	-rm -f timesolver-ta *.o
	-echo "Removing intermediate C files!"
	-rm -f pes.lex.cc pes.tab.cc
	-echo "Removing intermediate header files!"
	-rm -f pes.tab.hh
	-echo "Removing other parser-generated files!"
	-rm -f pes.output
	-echo "Removing Doxygen-generated documentation files!"
	-rm -rf doc/DoxygenOutput/html
	-rm -rf doc/DoxygenOutput/latex
	-echo "Removing other tool-generated files!"
	-rm -rf timesolver-ta.dSYM
	-rm -f gmon.out
	$(MAKE) -C test clean
	$(MAKE) -C external/cpplogging clean

# Formatting using clang-format
# This uses .clang-format as specification for the rules.
clang-format:
	clang-format -style=file -i $(CHECK_FILES)
	