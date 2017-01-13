# Flags passed to the C compiler.
CFLAGS = -c -g -O -Wall

# Flags passed to the C++ compiler.
CXXFLAGS += -g -Wall -Wextra

FLEX = flex

LDFLAGS =  
INCL_PATH = -I.

.PHONY: default
default: all

all: demo testdbm testdbmlist check

doc: demo *.hh *.cc
	doxygen pes-timed_Doxyfile

demo:	pes.tab.o pes.lex.o ExprNode.o demo.o
	$(CC) -o demo pes.lex.o pes.tab.o ExprNode.o demo.o $(LDFLAGS) 

demo.o: demo.cc DBM.hh ExprNode.hh DBMList.hh
	$(CC) $(CFLAGS) demo.cc $(INCL_PATH)

ExprNode.o: ExprNode.cc ExprNode.hh DBM.hh
	$(CC) $(CFLAGS) ExprNode.cc $(INCL_PATH)

pes.lex.o: pes.lex.c
	$(CC) $(CFLAGS) pes.lex.c $(INCL_PATH) 

pes.lex.c: pes.l
	$(FLEX) -p -8 -Ce -opes.lex.c pes.l

pes.tab.o: pes.tab.c DBM.hh ExprNode.hh
	$(CC) $(CFLAGS) pes.tab.c $(INCL_PATH)

pes.tab.c: pes.y
	bison -t -d -v -o pes.tab.c pes.y

check:
	$(MAKE) -C test

testdbm: testdbm.cc
	$(CC) -o testdbm -g testdbm.cc

testdbmlist: testdbmlist.cc DBMList.hh DBM.hh
	$(CC) -o testdbmlist -g testdbmlist.cc
 
clean:
	-echo "Removing all object files!"
	-rm -f demo *.o
	-rm -f testdbm
	-rm -f testdbmlist
	-echo "Removing intermediate C files!"
	-rm -f pes.lex.c pes.tab.c 
	-echo "Removing intermediate header files!"
	-rm -f pes.tab.h
	-echo "Removing other parser-generated files!"
	-rm -f pes.output
	-echo "Removing Doxygen-generated documentation files!"
	-rm -rf doc/DoxygenOutput/html
	-rm -rf doc/DoxygenOutput/latex
	-echo "Removing other tool-generated files!"
	-rm -rf testdbmlist.dSYM
	-rm -rf testdbm.dSYM
	-rm -rf demo.dSYM
	-rm -f gmon.out
	@$(MAKE) -C test clean

cleanBin:
	-echo "Removing all object files!"
	-rm -f demo *.o
	-rm -f testdbm
	-rm -f testdbmlist
	-echo "Removing intermediate C files!"
	-rm -f pes.lex.c pes.tab.c 
	-echo "Removing intermediate header files!"
	-rm -f pes.tab.h
	-echo "Removing other parser-generated files!"
	-rm -f pes.output
	-echo "Removing other tool-generated files!"
	-rm -rf testdbmlist.dSYM
	-rm -rf testdbm.dSYM
	-rm -rf demo.dSYM
	-rm -f gmon.out
