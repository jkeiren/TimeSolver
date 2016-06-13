//Model for the FISCHER Case Study

#ifndef FISCHERMODEL_H
#define FISCHERMODEL_H

#include "TATransition.hh"

using namespace std;

#define STRLEN 64
#define FORALL 1
#define EXISTS 0

/** Nicknames for different states for each of the processes.
 * Here "ready" is the state "req" (or request). */
enum state {idle, ready, waiting, critical};
enum IO {input, output, tau};

class FischerModel {

public:

  int process;

  /* For now, do not worry about constructors and destructors */
  
  FischerModel(int numProcess) {
    process = numProcess;
    generateModel(process);
  }

  void printModelPartBeforeSpec(std::ostream &os, string freezeClocks) {
    char line[STRLEN];
     
    os << "#define CA " << 10 <<endl;
    os << "#define CB " << 19 <<endl;
    os << "CLOCKS: {"; 
    for (int i = 1; i <= process; i++){
        sprintf(line, "x%d", i);
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
        os << line << ",";
    }
    os << "p}" <<endl;

    
    return;
  }
  
  
  void printModelPartAfterSpec(std::ostream &os) {
    char line[STRLEN];
    
    // Now print out the Invariant
    os << "INVARIANT:" << endl;
    for(int i = 1; i <= process; i++){
      sprintf(line, "p%d == %d -> x%d < CA", i,1,i);
      os << "\t" << line << endl;
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
    // Generate the Timed Automata as Transitions
    for (int i = 1; i <= process ; i++){
      sprintf(line, "p%d==%d && p==0", i, idle );
      source = line;
      sprintf(line, "p%d=%d, p=0", i, ready);
      sublist = line;
      sprintf(line, "x%d", i);
      reset = line; 
      TATransition *idle_1 = new TATransition(source, guard, sublist, reset, replace);
      myTransitions.push_back(idle_1);
    
      sprintf(line, "p%d==%d", i, ready);
      source = line;
      sprintf(line,"x%d < CA", i); 
      guard = line;
      sprintf(line, "p%d=%d, p=%d", i, waiting, i);
      sublist = line;
      sprintf(line, "x%d", i);
      reset = line; 
      TATransition *ready_1 = new TATransition(source, guard, sublist, reset, replace);
      myTransitions.push_back(ready_1);
    
      sprintf(line, "p%d==%d && p==%d", i, waiting, i);
      source = line;
      sprintf(line, "x%d > CB", i);
      guard = line;
      sprintf(line, "p%d=%d, p=%d", i, critical,i);
      sublist = line;
      reset = "";
      TATransition *waiting_1 = new TATransition(source, guard, sublist, reset, replace);
      myTransitions.push_back(waiting_1);
    
      /* This used to be in this version, but we model a
      * different way out of starvation. */
      sprintf(line, "p%d==%d && p!=%d", i, waiting, i);
      source = line;
      guard = "";
      sprintf(line, "p%d=%d", i, idle);
      sublist = line;
      reset = "";
      TATransition *waiting_2 = new TATransition(source, guard, sublist, reset, replace);
      myTransitions.push_back(waiting_2);
    
      // Add third equation to represent edge to eliminate
      // starvation (resetting from waiting to requesting)
      //        sprintf(line, "p%d==%d && x%d > CB && p==%d", i, waiting, i, 0);
      //        condition = line;
      //        sprintf(line, "p%d=%d", i, ready);
      //        sublist = line;
      //        sprintf(line, "x%d", i);
      //        reset = line; 
      //        Equation *waiting_3 = new Equation(FORALL, condition, "X",  sublist, reset, "");
      //        eqnTab.push_back(waiting_3);
    
      sprintf(line, "p%d==%d", i, critical);
      source = line;
      guard = "";
      sprintf(line, "p%d=%d, p=0", i, idle);
      sublist = line;
      reset = "";
      TATransition *critical_1 = new TATransition(source, guard, sublist, reset, replace);
      myTransitions.push_back(critical_1);

    }
  }
 
};

#endif
