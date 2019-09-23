/** File with the class TATransition. Used to ease example printing
 * and adapt output to parser/example changes */

#ifndef TATRANSITION_H
#define TATRANSITION_H

#include <iostream>
#include <string>
#include <vector>
#include <stdlib.h>

using namespace std;


/** Class for Timed Automata transitions in PES Examples. Allows for
 * easier transition printing. This class takes substrings for the state, reset
 * and replace (clock assignment) components. */
class TATransition{
public :

  TATransition(string src, string grd, string dest, string clkReset, string clkReplace)
      : sourceState(src), sourceGuard(grd), destState(dest), reset(clkReset), replace(clkReplace) { 
  };
  
  TATransition(TATransition &T) {
    sourceState = T.sourceState;
    sourceGuard = T.sourceGuard;
    destState = T.destState;
    reset = T.reset;
    replace = T.replace;
  }
  
  ~TATransition(){};

  void print(std::ostream &os) {
      os << "\t";
      os << "("; 
      if(sourceState.size() != 0 && sourceGuard.size() != 0) { 
        os << sourceState << ", " << sourceGuard; 
      }
      else if(sourceState.size() != 0) {
        os << sourceState; 
      }
      else if(sourceGuard.size() != 0) {
        os << sourceGuard; 
      }
      os << ")->";
      if(destState.size() != 0) { 
        os <<  "(" << destState << ")";
      }
      if(reset.size() != 0) { 
        os << "{" << reset <<"}";
      }
      if(replace.size() != 0) { 
        os << "[";
        os << "[" << replace << "]";
        os << "]";
      }
      os << ";" <<endl;
  }
  
  /* Variables are string states */
  string sourceState;
  string sourceGuard;
  string destState;
  string reset;
  string replace;
};

#endif
