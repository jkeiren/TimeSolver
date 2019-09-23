//Model for the PATHOS Case Study

#ifndef FISCHERMODEL_H
#define FISCHERMODEL_H

#include "TATransition.h"

using namespace std;

#define STRLEN 64
#define FORALL 1
#define EXISTS 0

/** Nicknames for different states for each of the processes.
 * Here "ready" is the state "req" (or request). */
enum state {idle, run, pending};
enum IO {input, output, tau};

class PathosModel {

public:

  int process;

  /* For now, do not worry about constructors and destructors */
  
  PathosModel(int numProcess) {
    process = numProcess;
    generateModel(process);
  }

  void printModelPartBeforeSpec(std::ostream &os, string freezeClocks) {
    char line[STRLEN];
     
    os << "#define CPERIOD " << process <<endl;
    /* The default unit value is $1$, CPERIODUNIT is period - unit */
    os << "#define CPERIODUNIT " << (process - 1) << endl;
    // Add a constant two units before the deadline
	  os << "#define CPERIODUNITMTWO " << (process - 3) << endl;
	  
    os << "CLOCKS: {"; 
    for (int i = 1; i <= process; i++){
      sprintf(line, "x%d,y%d", i, i);
      os << line;
      if(i != process) os << "," ;
    }
    if(freezeClocks.empty()) {
      os << "}" <<endl;
    }
    else {
      os << ", " << freezeClocks << "}" << endl;
    }
  
    os << "CONTROL: {"; 
    for (int i = 1; i <= process; i++){
      sprintf(line, "p%d", i);
      os << line;
      if(i != process) os << "," ;
    }
    os << "}" << endl;
  
    os << "INITIALLY: " ;
    for (int i = 1; i <= process; i++){
      sprintf(line, "x%d >= CPERIOD", i);
      os << line;
      if(i != process) os << " && ";
    }
    os << endl;
    
    return;
  }
  
  
  void printModelPartAfterSpec(std::ostream &os) {
    char line[STRLEN];
    
    os << "INVARIANT:" << endl;
    for(int i = 1; i <= process; i++){
      sprintf(line, "p%d == 1 -> y%d <= 1", i,i);
      os << "\t" << line <<endl;
    }
  
    os << "TRANSITIONS:" << endl;
    // Now print out the previously generated transitions
    for (vector<TATransition*>::iterator ie = myTransitions.begin(); ie != myTransitions.end(); ie++) {
      (*ie)->print(os);
    }
  
    return;
  }
 
private:

  /* Use vector to store transitions */
  vector<TATransition *> myTransitions;
  
  void generateModel(int process) {
  
    char line[STRLEN];
    string source = "";
    string guard = "";
    string sublist = "";
    string reset = "";
    string replace = "";
  
    /* First group of transitions:
     * idle[i] -> run[i] */
    for (int i = 1; i <= process ; i++){
      sprintf(line, "p%d == %d ", i, idle);
      source = line;
      for (int j = 1; j <= process ; j++){
        if(j < i) {
        
          sprintf(line, " && ");
          source += line;

          sprintf(line, "p%d == %d", j, idle);
          source += line;

        }
        if(j == i) { // do nothing
        }
        if (j > i) {

          sprintf(line, " && ");
          source += line;

          sprintf(line, "p%d != %d", j, run);
          source += line;

        }
      
      }
    
      sprintf(line, "x%d >= CPERIOD", i);
      guard = line;
      sprintf(line, "p%d=%d", i, run);
      sublist = line;
      sprintf(line, "x%d,y%d", i, i);
      reset = line;
      sprintf(line, "");
      replace = line;
      TATransition *t = new TATransition(source, guard, sublist, reset, replace);
      myTransitions.push_back(t);
    }
  
    /* Second group of transitions:
     * idle[i] -> pending[i] */
    for (int i = 1; i <= process ; i++){
      sprintf(line, "(p%d == %d) && (", i, idle);
      source = line;
      bool firstText = true;
      for (int j = 1; j <= process ; j++){
        if(j < i) {
          if(firstText) {
            //firstText = false;
          }
          else {
            sprintf(line, " || ");
            source += line;
          }
          sprintf(line, "p%d != %d", j, idle);
          source += line;
          // Now set firstText to false to indicate we already have first text
          firstText = false;
        }
        if(j == i) { // do nothing
        }
        if (j > i) {
          if(firstText) {
            //firstText = false;
          }
          else {
            sprintf(line, " || ");
            source += line;
          }
          sprintf(line, "p%d == %d", j, run);
          source += line;
          // Now set firstText to false to indicate we already have first text
          firstText = false;
        }

      }
      sprintf(line, ")");
      source += line;
      sprintf(line, "x%d >= CPERIOD", i);
      guard= line;
    
      sprintf(line, "p%d=%d", i, pending);
      sublist = line;
      sprintf(line, "x%d", i);
      reset = line;
      sprintf(line, "");
      replace = line;
      TATransition *t = new TATransition(source, guard, sublist, reset, replace);
      myTransitions.push_back(t);
    }
  
    /* Third group of transitions:
     * run[i] -> idle[i] only */
    for (int i = 1; i <= process ; i++){
      sprintf(line, "(p%d == %d) ", i, run);
      source = line;
      for (int j = 1; j <= process ; j++){
        if(j != i) {

          sprintf(line, " && ");
          source += line;

          sprintf(line, "p%d != %d", j, pending);
          source += line;
        }
        if(j == i) { // do nothing
        }
      

      }
      sprintf(line, "y%d <= 1", i);
      guard = line;
      sprintf(line, "p%d=%d", i, idle);
      sublist = line;
      sprintf(line, "");
      reset = line;
      sprintf(line, "");
      replace = line;
      TATransition *t = new TATransition(source, guard, sublist, reset, replace);
      myTransitions.push_back(t);
    } 
    /* Fourth group of transitions:
     * run[i] -> idle[i] and pending[j] -> run[j] sync */
    for (int i = 1; i <= process ; i++){
      for(int j = 1; j <= process; j++) {
        if(j == i) {
          continue;
        }
        sprintf(line, "p%d == %d && p%d == %d", i, run, j, pending);
        source = line;
        sprintf(line, "y%d <= 1  && x%d <= CPERIODUNIT ", i, j);
        guard = line;
        bool firstText = true;
        for (int k = 1; k <= process ; k++){
          if(k != i && k < j) {

            sprintf(line, " && ");
            source += line;

            sprintf(line, "p%d == %d", k, idle);
            source += line;
          }
          // do nothing otherwise
        
  
        }
        sprintf(line, "p%d=%d,p%d=%d", i, idle, j, run);
        sublist = line;
        sprintf(line, "y%d", j);
        reset = line;
        sprintf(line, "");
        replace = line;
        TATransition *t = new TATransition(source, guard, sublist, reset, replace);
        myTransitions.push_back(t);
      }
    } 
	
	}
 
};

#endif
