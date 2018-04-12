//Model for the CSMA-CD Case Study

#ifndef CSMAMODEL_H
#define CSMAMODEL_H

#include "TATransition.hh"

using namespace std;

#define STRLEN 64
#define FORALL 1
#define EXISTS 0
#define bus_idle 0
#define bus_active 1
#define bus_collision 2
#define sender_wait 0
#define sender_transm 1
#define sender_retry 2

enum channel {c_begin, c_end, cd, busy};
enum IO {input, output};

class Trans{
  public :
  
  /** Helper class to generate transitions. */
  Trans(int iid, int n, IO p, channel ch, string en, string rset, int st, int ed)
  : id(iid), num(n), io(p), chan(ch),enable(en), reset(rset), start(st), end(ed){
	};
  ~Trans(){};
  
  int id;
  int num;
  IO io;
  channel chan;
  string enable;
  string reset;
  int start;
  int end;
};


class CsmaModel {

public:

    
  int process;

  /* For now, do not worry about constructors and destructors */
  
  CsmaModel(int numProcess) {
    process = numProcess;
    generateModel(process);
  }

  void printModelPartBeforeSpec(std::ostream &os, string freezeClocks) {
    char line[STRLEN];
     
    os << "#define CA       26" << endl;
    os << "#define CB       52" << endl;
    os << "#define CLAMBDA  808" << endl;
  
    os << "CLOCKS: {";
    for (int i = 1; i <= process; i++){
      sprintf(line, "x%d,", i);
      os << line;
    }
    if(freezeClocks.empty()) {
      os << "y}" <<endl;
    }
    else {
      os << "y, " << freezeClocks << "}" << endl;
    }
  
    os << "CONTROL: {";
    for (int i = 1; i <= process; i++){
      sprintf(line, "p%d,", i);
      os << line;
    }
    os << "p}" <<endl;
    
    return;
  }
  
  
  void printModelPartAfterSpec(std::ostream &os) {
    char line[STRLEN];
    
    os << "INVARIANT:" << endl;
    for(int i = 1; i <= process; i++){
      sprintf(line, "p%d == 1 -> x%d <= CLAMBDA", i,i);
      os << "\t" << line <<endl;
      sprintf(line, "p%d == 2 -> x%d < CB", i,i);
      os << "\t" << line <<endl;
    }
    /* Invariant on the bus missing, so added here.
     * We add that if the bus is in state 2 (collision),
     * its clock must ve less than CA */
    sprintf(line, "p == 2 -> y < CA");
    os << "\t" << line <<endl;
  
    os << "TRANSITIONS:" << endl;
    // Additional transitions for CSMACD
    for (vector<TATransition*>::iterator ie = tabTransitions.begin(); ie != tabTransitions.end(); ie++) {
      (*ie)->print(os);
    }
    // Now print out the previously generated transitions
    for (vector<TATransition*>::iterator ie = myTransitions.begin(); ie != myTransitions.end(); ie++) {
      (*ie)->print(os);
    }
  
    return;
  }
 
private:

  /* First vector of temporary transitions */
  vector<TATransition *> tabTransitions;
  /* Use vector to store transitions */
  vector<TATransition *> myTransitions;
  
  void generateModel(int process) {
  
    
    char line[STRLEN];
  
    vector <Trans *> transTableBus;
    vector <Trans *> transTableSender;
    /* Use temporary vector to store partial transitions */
    vector<TATransition *> tempTransitions;
    
    string source = "";
    string guard = "";
    string enable = "";
    string sublist = "";
    string reset = "";
    string replace = "";
  
    Trans *bus_begin1= new Trans(0, 1, input, c_begin, "", "y", bus_idle, bus_active);
    Trans *bus_end1= new Trans(0, 1, input, c_end, "", "y", bus_active, bus_idle);
    Trans *bus_busy1= new Trans(0, 1, output, busy, "y >= CA", "", bus_active, bus_active);
    Trans *bus_begin2= new Trans(0, 1, input, c_begin, "y < CA", "y", bus_active, bus_collision);
    Trans *bus_cd= new Trans(0, 2, output, cd, "y < CA", "y", bus_collision, bus_idle);
    transTableBus.push_back(bus_begin1);
    transTableBus.push_back(bus_end1);
    transTableBus.push_back(bus_busy1);
    transTableBus.push_back(bus_begin2);
    transTableBus.push_back(bus_cd);
  
    for (int i = 1; i <= process ; i++){
      enable = "";
      reset = "";
      Trans *sender_cd1 = new Trans(i, 1, input, cd, enable, reset, sender_wait, sender_wait);
    
      sprintf(line, "x%d", i);
      reset = string(line);
      Trans *sender_cd2 = new Trans(i, 1, input, cd, enable, reset, sender_wait, sender_retry);
      Trans *sender_begin1 = new Trans(i, 1, output, c_begin, enable, reset, sender_wait, sender_transm);
      Trans *sender_busy1 = new Trans(i, 1, input, busy, enable, reset, sender_wait, sender_retry);
    
      // Was "x%d <= CLAMBDA": Should be "x%d == CLAMBDA"
      sprintf(line, "x%d == CLAMBDA", i);
      enable = string(line);
      Trans *sender_end1 = new Trans(i, 1, output, c_end, enable, reset, sender_transm, sender_wait);
    
      /* Originally, this was "x%d < CB", but was corrected for "x%d < CA"
       * to match model in KRONOS */;
      sprintf(line, "x%d < CA", i);
      enable = string(line);
      Trans *sender_cd3 = new Trans(i, 1, input, cd, enable, reset, sender_transm, sender_retry);
      /* Copied Enable here to allow for different invariants for previous statement */
      sprintf(line, "x%d < CB", i);
      enable = string(line);
      Trans *sender_begin2 = new Trans(i, 1, output, c_begin, enable, reset, sender_retry, sender_transm);
    
      enable = "";
      Trans *sender_busy2 = new Trans(i, 1, input, busy, enable, reset, sender_retry, sender_retry);
    
      sprintf(line, "x%d < CB", i);
      enable = string(line);
      /* Fix Reset to add sender_retry for the reset, since the clock resets
       * here too */
      //reset = "";
      sprintf(line, "x%d", i);
      reset = string(line);
      Trans *sender_cd4 = new Trans(i, 1, input, cd, enable, reset, sender_retry, sender_retry);
      transTableSender.push_back(sender_cd1);
      transTableSender.push_back(sender_cd2);
      transTableSender.push_back(sender_cd3);
      transTableSender.push_back(sender_cd4);
      transTableSender.push_back(sender_begin1);
      transTableSender.push_back(sender_begin2);
      transTableSender.push_back(sender_busy1);
      transTableSender.push_back(sender_busy2);
      transTableSender.push_back(sender_end1);
    }
  
    for (vector<Trans*>::iterator ib =  transTableBus.begin(); ib != transTableBus.end(); ib++){
      if ((*ib)->num == 1){
        for (vector<Trans*>::iterator it =  transTableSender.begin(); it != transTableSender.end(); it++){
          if (((*ib)->chan == (*it)->chan) && ((*ib)->io != (*it)->io)){
            sprintf(line, "p==%d",(*ib)->start);
            source = string(line);
            guard = (*ib)->enable;
            sprintf(line, " && p%d==%d",(*it)->id, (*it)->start);
            source += line;
            if ((*it)->enable.size() != 0) {
              if(guard != "") {
                guard += " && ";
              }
              guard += (*it)->enable;
            }
          
            sprintf(line, "p=%d,p%d=%d",(*ib)->end, (*it)->id, (*it)->end);
            sublist = string(line);
          
            reset = (*ib)->reset;
            if ((*it)->reset.size() != 0) {
              if(reset.size() != 0) {
                reset += ",";
              }
              reset += (*it)->reset;
            }
            TATransition *t = new TATransition(source, guard, sublist, reset, replace);
            tabTransitions.push_back(t);
          }
        }
      }
    }
  
    TATransition *T = new TATransition("p == 2", "y < CA", "p=0", "y", "");
    myTransitions.push_back(T);
  
    /* Use input transitions to generate even more transitions */
  
    for(int i = 1; i <= process; i++){
      /* Another temporary vector of transitions */
      vector<TATransition *>eqnTransitions;
      for (vector<TATransition *>::iterator ie = myTransitions.begin(); ie != myTransitions.end(); ie++){
        for (vector<Trans*>::iterator it =  transTableSender.begin(); it != transTableSender.end(); it++){
          if ((*it)->id == i && (*it)->chan == cd && (*it)->io == input) {
            TATransition *t = new TATransition(*(*ie));
            sprintf(line, " && p%d==%d", i, (*it)->start);
            t->sourceState += line;
            if ((*it)->enable.size() != 0){
              t->sourceGuard += " && ";
              t->sourceGuard += (*it)->enable ;
            }
            sprintf(line, ",p%d=%d", i, (*it)->end);
            t->destState += line;
            if ((*it)->reset.size() != 0){
              t->reset += ",";
              t->reset += (*it)->reset ;
            }
            eqnTransitions.push_back(t);
          }
        }
      }
      eqnTransitions.swap(myTransitions);
    }
  }
 
};

#endif
