CC = g++
CCOPTS = -c -g

all: csma fddi fischer grc leader pathos

csma: csma.o
	$(CC) -o csma csma.o

csma.o: csma.cc CsmaModel.hh
	$(CC) $(CCOPTS) csma.cc
	
fddi: fddi.o
	$(CC) -o fddi fddi.o

fddi.o: fddi.cc FddiModel.hh
	$(CC) $(CCOPTS) fddi.cc
	
fischer: fischer.o
	$(CC) -o fischer fischer.o

fischer.o: fischer.cc FischerModel.hh
	$(CC) $(CCOPTS) fischer.cc
	
grc: grc.o
	$(CC) -o grc grc.o

grc.o: grc.cc GrcModel.hh
	$(CC) $(CCOPTS) grc.cc
	
leader: leader.o
	$(CC) -o leader leader.o

leader.o: leader.cc LeaderModel.hh
	$(CC) $(CCOPTS) leader.cc
	
pathos: pathos.o
	$(CC) -o pathos pathos.o

pathos.o: pathos.cc PathosModel.hh
	$(CC) $(CCOPTS) pathos.cc

clean:
	rm -f csma
	rm -f csma.o
	rm -f fddi
	rm -f fddi.o
	rm -f fischer
	rm -f fischer.o
	rm -f grc
	rm -f grc.o
	rm -f leader
	rm -f leader.o
	rm -f pathos
	rm -f pathos.o

