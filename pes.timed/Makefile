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

CXXFLAGS_ALL = -O -Wall -Wextra
CXXFLAGS_PROFILE = -pg
CXXFLAGS_DEBUG = -g
CXXFLAGS_VALGRIND = -g3

LDFLAGS_ALL =
LDFLAGS_PROFILE = -pg -O
LDFLAGS_DEBUG =
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
INCL_PATH = -I.
TEST_DIR = test

.PHONY: default
default: all

all: demo check

doc: demo *.hh *.cc
	doxygen pes-timed_Doxyfile

demo:	pes.tab.o pes.lex.o ExprNode.o demo.o
	$(CXX) $(CXXFLAGS) pes.lex.o pes.tab.o ExprNode.o demo.o $(LDFLAGS) -o demo

demo.o: demo.cc DBM.hh ExprNode.hh DBMList.hh
	$(CXX) $(CXXFLAGS) -c demo.cc $(INCL_PATH)

ExprNode.o: ExprNode.cc ExprNode.hh DBM.hh
	$(CXX) $(CXXFLAGS) -c ExprNode.cc $(INCL_PATH)

pes.lex.o: pes.lex.cc
	$(CXX) $(CXXFLAGS) -c pes.lex.cc $(INCL_PATH) 

pes.lex.cc: pes.l
	$(FLEX) -p -8 -Ce -opes.lex.cc pes.l

pes.tab.o: pes.tab.cc pes.tab.hh DBM.hh ExprNode.hh
	$(CXX) $(CXXFLAGS) -c pes.tab.cc $(INCL_PATH)

pes.tab.cc pes.tab.hh: pes.y
	$(BISON) -t -d -v -o pes.tab.cc pes.y

check:
	$(MAKE) -C $(TEST_DIR) check
 
clean:
	-echo "Removing all object files!"
	-rm -f demo *.o
	-echo "Removing intermediate C files!"
	-rm -f pes.lex.c pes.tab.c 
	-echo "Removing intermediate header files!"
	-rm -f pes.tab.hh
	-echo "Removing other parser-generated files!"
	-rm -f pes.output
	-echo "Removing Doxygen-generated documentation files!"
	-rm -rf doc/DoxygenOutput/html
	-rm -rf doc/DoxygenOutput/latex
	-echo "Removing other tool-generated files!"
	-rm -rf demo.dSYM
	-rm -f gmon.out
	$(MAKE) -C $(TEST_DIR) clean
