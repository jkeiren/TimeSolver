//Model for the GRC Case Study

#ifndef GRCMODEL_H
#define GRCMODEL_H

#include "TATransition.h"

using namespace std;

#define STRLEN 64
#define FORALL 1
#define EXISTS 0

/** Nicknames for different states for each of the processes.
 * Here "ready" is the state "req" (or request). */
enum gate_state {up, lower, down, raise};
enum train_state {far, near, in};

class GrcModel {

public:

  int process;

  /* For now, do not worry about constructors and destructors */
  
  GrcModel(int numProcess) {
    process = numProcess;
    generateModel(process);
  }

  void printModelPartBeforeSpec(std::ostream &os, string freezeClocks) {
    char line[STRLEN];
     
    /* Define all constants here */
    os << "#define CCD " << "1" <<endl;
    os << "#define CGLT " << "2" <<endl;
    os << "#define CGRT " << "2" <<endl;
    os << "#define CTP " << "4" <<endl;
    os << "#define CTDL " << "1" <<endl;
    os << "#define CTDU " << "15" <<endl;
  
    /* Define the clocks.
     * we have one clock per train, one for the controller  
     * and one for the gate.  the |process + 1| process
     * is the gate and the |process + 2| process is the
     * controller */
    os << "CLOCKS: {"; 
    for (int i = 1; i <= process + 2; i++){
      sprintf(line, "x%d", i);
      os << line;
      if(i != process + 2) os << "," ;
    }
    if(freezeClocks.empty()) {
      os << "}" <<endl;
    }
    else {
      os << ", " << freezeClocks << "}" << endl;
    }
    
    /* print comments for the example reader. */
    os << "// p1-p"<< process << " are the trains." << endl;
    os << "// p" << process + 1 << " is the gate." << endl;
    os << "// p" << process + 2 << " is the controller." << endl;
  
    /* Include gate and controller */
    os << "CONTROL: {"; 
    for (int i = 1; i <= process + 2; i++){
      sprintf(line, "p%d", i);
      os << line;
      if(i != process + 2) os << "," ;
    }
    os << "}" <<endl;
  
    /* Initially all clocks are 0 */
    os << "INITIALLY: " ;
    for (int i = 1; i <= process + 2; i++){
      sprintf(line, "x%d == 0", i);
      os << line;
      if(i != process + 2) os << " && ";
    }
    os << endl;

    
    return;
  }
  
  
  void printModelPartAfterSpec(std::ostream &os) {
    char line[STRLEN];
    
    /* Print invariants for all states */
    os << "INVARIANT:" << endl;
    // Invariants for each train
    for(int i = 1; i <= process; i++){
      sprintf(line, "p%d == %d -> x%d <= CTP", i, near, i);
      os << "\t" << line <<endl;
      sprintf(line, "p%d == %d -> x%d <= CTDU", i, in,i);
      os << "\t" << line <<endl;
    }
    // gate invariant
    sprintf(line, "p%d == %d -> x%d <= CGLT", process + 1, lower, process + 1);
    os << "\t" << line <<endl;
    sprintf(line, "p%d == %d -> x%d <= CGRT", process + 1, raise, process + 1);
    os << "\t" << line <<endl;
    // controller invariant
    for(int cnt = 1; cnt <= process; cnt++) {
      sprintf(line, "p%d == %d -> x%d <= CCD", process + 2, cnt, process + 2);
      os << "\t" << line <<endl;
    }
    sprintf(line, "p%d == %d -> x%d <= CCD", process + 2, (2*process) + 1, process + 2);
    os << "\t" << line <<endl;
  
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
     * A Train approaches: approach_i "*/
    for (int i = 1; i <= process ; i++){
      /* First train approaches (controller is up or at raise) */
      // Controller up
      sprintf(line, "p%d == %d && p%d == %d", i, far, process + 2, 0);
      source = line;
      sprintf(line, "p%d=%d, p%d=%d", i, near, process + 2, 1);
      sublist = line;
      sprintf(line, "x%d,x%d", i, process + 2);
      reset = line;
      sprintf(line, "");
      replace = line;
      TATransition *t = new TATransition(source, guard, sublist, reset, replace);
      myTransitions.push_back(t);
    
      // controller Raise
      sprintf(line, "p%d == %d && p%d == %d", i, far, process + 2, (2*process) + 1);
      source = line;
      sprintf(line, "p%d=%d, p%d=%d", i, near, process + 2, 1);
      sublist = line;
      sprintf(line, "x%d,x%d", i, process + 2);
      reset = line;
      sprintf(line, "");
      replace = line;
      TATransition *t2 = new TATransition(source, guard, sublist, reset, replace);
      myTransitions.push_back(t2);
    
      /* Another train approaches while one is approaching or in.
       * We know this and thus raise the counter. */
      // Controller lower
      for(int cnt = 1; cnt <= process - 1; cnt++){
        sprintf(line, "p%d == %d && p%d == %d", i, far, process + 2, cnt);
        source = line;
        sprintf(line, "p%d=%d, p%d=%d", i, near, process + 2, cnt+1);
        sublist = line;
        sprintf(line, "x%d", i);
        reset = line;
        sprintf(line, "");
        replace = line;
        TATransition *t3 = new TATransition(source, guard, sublist, reset, replace);
        myTransitions.push_back(t3);
      
        // Controller down
        sprintf(line, "p%d == %d && p%d == %d", i, far, process + 2, process+cnt);
        source = line;
        sprintf(line, "p%d=%d, p%d=%d", i, near, process+2, process+cnt+1);
        sublist = line;
        sprintf(line, "x%d", i);
        reset = line;
        sprintf(line, "");
        replace = line;
        TATransition *t4 = new TATransition(source, guard, sublist, reset, replace);
        myTransitions.push_back(t4);
      }
    }
  
    /* Second group of transitions: An approaching train enters */
    for (int i = 1; i <= process; i++) {
      sprintf(line, "p%d == %d", i, near);
      source = line;
      sprintf(line, "x%d == CTP", i);
      guard = line;
      sprintf(line, "p%d=%d", i, in);
      sublist = line;
      sprintf(line, "x%d", i);
      reset = line;
      sprintf(line, "");
      replace = line;
      TATransition *t = new TATransition(source, guard, sublist, reset, replace);
      myTransitions.push_back(t);
  
    }
  
    /* Third group of transitions: A train leaving */
    for (int i = 1; i <= process ; i++){
      /* Last train leaves */
      /* cnt == 1 */
      // Controller lower
      sprintf(line, "p%d == %d && p%d == %d", i, in, process + 2, 1);
      source = line;
      sprintf(line, "x%d >= CTDL", i);
      guard = line;
      sprintf(line, "p%d=%d, p%d=%d", i, far, process + 2, (2*process)+1);
      sublist = line;
      sprintf(line, "x%d", process+2);
      reset = line;
      sprintf(line, "");
      replace = line;
      TATransition *t1 = new TATransition(source, guard, sublist, reset, replace);
      myTransitions.push_back(t1);
    
      // Controller Down
      sprintf(line, "p%d == %d && p%d == %d", i, in, process + 2, process+1);
      source = line;
      sprintf(line, "x%d >= CTDL", i);
      guard = line;
      sprintf(line, "p%d=%d, p%d=%d", i, far, process + 2, (2*process)+1);
      sublist = line;
      sprintf(line, "x%d", process + 2);
      reset = line;
      sprintf(line, "");
      replace = line;
      TATransition *t2 = new TATransition(source, guard, sublist, reset, replace);
      myTransitions.push_back(t2);
    
      /* Other trains remain:  at least one train is near or in */
      for(int cnt=process; cnt >= 2; cnt--){
        // Controller lower
        sprintf(line, "p%d == %d && p%d == %d", i, in, process + 2, cnt);
        source = line;
        sprintf(line, "x%d >= CTDL", i);
        guard = line;
        sprintf(line, "p%d=%d, p%d=%d", i, far, process + 2, cnt-1);
        sublist = line;
        sprintf(line, "");
        reset = line;
        sprintf(line, "");
        replace = line;
        TATransition *t4 = new TATransition(source, guard, sublist, reset, replace);
        myTransitions.push_back(t4);
      
        // Controller Down
        sprintf(line, "p%d == %d && p%d == %d", i, in, process + 2, process+cnt);
        source = line;
        sprintf(line, "x%d >= CTDL", i);
        guard = line;
        sprintf(line, "p%d=%d, p%d=%d", i, far, process + 2, process+cnt-1);
        sublist = line;
        sprintf(line, "");
        reset = line;
        sprintf(line, "");
        replace = line;
        TATransition *t3 = new TATransition(source, guard, sublist, reset, replace);
        myTransitions.push_back(t3);
    
      }
    }
    /* Next group of transitions: Controller/Gate Syncing */
    // Want gate to raise 
    sprintf(line, "p%d == %d && p%d == %d", process +1, down, process + 2, 2*process + 1);
    source = line;
    guard = "";
    sprintf(line, "p%d=%d, p%d=%d", process + 1, raise, process + 2, 0);
    sublist = line;
    sprintf(line, "x%d", process + 1);
    reset = line;
    sprintf(line, "");
    replace = line;
    TATransition *tRaise = new TATransition(source, guard, sublist, reset, replace);
    myTransitions.push_back(tRaise);
  
    // This is when the gate is being lowered and it should raise
    sprintf(line, "p%d == %d && p%d == %d", process +1, lower, process + 2, 2*process + 1);
    source = line;
    sprintf(line, "p%d=%d, p%d=%d", process + 1, raise, process + 2, 0);
    sublist = line;
    sprintf(line, "x%d", process + 1);
    reset = line;
    sprintf(line, "");
    replace = line;
    TATransition *tr1 = new TATransition(source, guard, sublist, reset, replace);
    myTransitions.push_back(tr1);
  
    // Want gate to lower
    for(int cnt = 1; cnt <= process; cnt++) {
      sprintf(line, "p%d == %d && p%d == %d", process +1, up, process + 2, cnt);
      source = line;
      sprintf(line, "p%d=%d, p%d=%d", process + 1, lower, process + 2, process+cnt);
      sublist = line;
      sprintf(line, "x%d", process + 1);
      reset = line;
      sprintf(line, "");
      replace = line;
      TATransition *t2 = new TATransition(source, guard, sublist, reset, replace);
      myTransitions.push_back(t2);
    
      // Include when gate is in "raise" position
      // This is when the gate is being raised and it should lower
      sprintf(line, "p%d == %d && p%d == %d", process +1, raise, process + 2, cnt);
      source = line;
      sprintf(line, "p%d=%d, p%d=%d", process + 1, lower, process + 2, process+cnt);
      sublist = line;
      sprintf(line, "x%d", process + 1);
      reset = line;
      sprintf(line, "");
      replace = line;
      TATransition *t1b = new TATransition(source, guard, sublist, reset, replace);
      myTransitions.push_back(t1b);
    }
  
    /* Next group of transitions: Gate lowering/raising */ 
  
    // Gate has raised.
    sprintf(line, "p%d == %d", process +1, raise);
    source = line;
    sprintf(line, "x%d == CGRT", process + 1);
    guard = line;
    sprintf(line, "p%d=%d", process + 1, up);
    sublist = line;
    sprintf(line, "");
    reset = line;
    sprintf(line, "");
    replace = line;
    TATransition *tr2 = new TATransition(source, guard, sublist, reset, replace);
    myTransitions.push_back(tr2);
  
    //Gate has lowered. 
    sprintf(line, "p%d == %d", process + 1, lower);
    source = line;
    sprintf(line, "x%d == CGLT", process + 1);
    guard = line;
    sprintf(line, "p%d=%d", process + 1, down);
    sublist = line;
    sprintf(line, "");
    reset = line;
    sprintf(line, "");
    replace = line;
    TATransition *t12 = new TATransition(source, guard, sublist, reset, replace);
    myTransitions.push_back(t12);
	
	}
 
};

#endif
