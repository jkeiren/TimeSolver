INCL_PATH = -Iinclude

all: logger.o
	
logger.o: src/logger.cpp include/cpplogging/logger.h
	$(CXX) $(CXXFLAGS) -c src/logger.cpp $(INCL_PATH)
	
clean:
	-echo "Removing logger.o"
	-rm -f *.o