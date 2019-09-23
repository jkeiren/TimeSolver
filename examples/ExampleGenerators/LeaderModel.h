//Model for the LEADER Case Study

#ifndef LEADERMODEL_H
#define LEADERMODEL_H

#include "TATransition.h"

using namespace std;

#define STRLEN 64
#define FORALL 1
#define EXISTS 0


class LeaderModel {

public:

  int process;

  /* For now, do not worry about constructors and destructors */
  
  LeaderModel(int numProcess) {
    process = numProcess;
    generateModel(process);
  }

  void printModelPartBeforeSpec(std::ostream &os, string freezeClocks) {
    char line[STRLEN];
     
    os << "#define CPD 2" <<endl;
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
      os << line;
      if(i != process) os << "," ;
    }
    // Add additional control to indicate final state
    os << ", p";
    os << "}" <<endl;
    
    return;
  }
  
  
  void printModelPartAfterSpec(std::ostream &os) {
    char line[STRLEN];
    
    /* Modify invariant to only be for one process
     * in state 0 */
    os << "INVARIANT:" << endl;
    for(int i = 1; i <= process; i++){
      sprintf(line, "p%d == 0 && p==0 -> x%d <= CPD", i,i);
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
    for (int i = 1; i <= process ; i++){
      for (int j = 1; j <= process; j++){
        if (j<i){
          sprintf(line, "p%d == 0 && p%d == 0", i, j);
          source = line;
          sprintf(line, "x%d <= CPD && x%d <= CPD", i, j);
          guard = line;
          sprintf(line, "p%d = %d", i, j);
          sublist = line;
          sprintf(line, "x%d, x%d", i, j);
          reset =  line;
          TATransition *t = new TATransition(source, guard, sublist, reset, replace);
          myTransitions.push_back(t);
        }
      }
    }
  
    // Add transition to a final state when a leader is elected
    // This eliminates the timelock
    source = "p==0 && p1==0";
    for(int i = 2; i <= process; i++) {
      sprintf(line, " && p%d!=0", i);
      source += line;
    }
    guard = "";
    sublist = "p=1";
    reset="";
    replace="";
    for(int i = 1; i <= process; i++) {
      sprintf(line,"x%d",i);
      reset += line;
      if(i != process) {
        reset += ", ";
      }
    }
    TATransition *t = new TATransition(source, guard, sublist, reset, replace);
          myTransitions.push_back(t);
  }
 
};

#endif
