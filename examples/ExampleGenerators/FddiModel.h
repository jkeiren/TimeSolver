//Model for the FDDI Case Study

#ifndef FDDIMODEL_H
#define FDDIMODEL_H

#include "TATransition.h"

using namespace std;

#define STRLEN 64
#define FORALL 1
#define EXISTS 0
#define single 1

enum state{IDLE,SYNC,ASYNC};
enum IO {input, output, tau};

/** Helper class to generate transitions. */
class Trans{
  public :
  
  Trans(int iid, int n, IO p, int ch, string en, string rset, string rp, int st, int ed)
  : id(iid), num(n), io(p), chan(ch),enable(en), reset(rset), replace(rp), start(st), end(ed){
	};
  ~Trans(){};
  
  int id;
  int num;
  IO io;
  int chan;
  string enable;
  string reset;
  string replace;
  int start;
  int end;
};



class FddiModel {

public:

    
  int process;

  /* For now, do not worry about constructors and destructors */
  
  FddiModel(int numProcess) {
    process = numProcess;
    generateModel(process);
  }

  void printModelPartBeforeSpec(std::ostream &os, string freezeClocks) {
    char line[STRLEN];
     
    os << "#define CSA 20" <<endl;
    os << "#define Ctd 0" <<endl;
    sprintf(line, "#define CTRTT %d", (50*process+20) );
    os << line <<endl;
  
    os << "CLOCKS: {";
    for (int i = 1; i <= process; i++){
      sprintf(line, "x%d,y%d,", i,i);
      os << line;
    }
    if(freezeClocks.empty()) {
      os << "x}" <<endl;
    }
    else {
      os << "x, " << freezeClocks << "}" << endl;
    }
  
    os << "CONTROL: {";
    for (int i = 1; i <= process; i++){
      sprintf(line, "p%d,", i);
      os << line;
    }
    os << "p=1}" <<endl;
  
    os << "INITIALLY: " ;
    os << "x==0 && " ;
    for (int i = 1; i <= process; i++){
      sprintf(line, "x%d == 0 && y%d >= CTRTT", i, i);
      os << line;
      if(i != process) {
        os << " && ";
      }
    }
    os << endl;
    
    return;
  }
  
  
  void printModelPartAfterSpec(std::ostream &os) {
    char line[STRLEN];
    
    os << "INVARIANT:" << endl;
    for(int i = 1; i <= process; i++){
      sprintf(line, "p == %d -> x <= Ctd", 2*i-1);
      os << "\t" << line <<endl;
      sprintf(line, "p%d == %d -> x%d <= CSA", i,SYNC,i);
      os << "\t" << line <<endl;
      sprintf(line, "p%d == %d -> y%d <= CTRTT", i,ASYNC,i);
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
    vector <Trans *> transTableBus;
    vector <Trans *> transTableSender;
     
    string source = "";
    string guard = "";
    string enable = "";
    string sublist = "";
    string reset = "";
    string replace = "";
  
    for (int i = 1; i <= process ; i++){
      Trans *ring_to_i = new Trans(0, single, output, 2*i - 1, "x==Ctd", "", "", 2*i - 1, 2*i );
      Trans *ring_i = new Trans(0, single, input, 2*i, "", "x", "", 2*i, 2*i+1 );
      transTableBus.push_back(ring_to_i);
      transTableBus.push_back(ring_i);
    
      sprintf(line, "x%d", i);
      reset = line;
      sprintf(line, "y%d=x%d", i, i);
      replace = line;
      Trans *station_idle = new Trans(i, single, input, 2*i - 1, "", reset, replace, IDLE, SYNC );
    
      sprintf(line, "x%d == CSA && y%d >= CTRTT", i, i);
      enable = line;
      Trans *station_sync_1 = new Trans(i, single, output, 2*i, enable, "", "", SYNC, IDLE );
    
      sprintf(line, "x%d == CSA && y%d < CTRTT", i, i);
      enable = line;
      Trans *station_sync_2 = new Trans(i, single, tau, 0, enable, "", "", SYNC, ASYNC );
      Trans *station_async = new Trans(i, single, output, 2*i, "", "", "", ASYNC, IDLE );
      transTableSender.push_back(station_idle);
      transTableSender.push_back(station_sync_1);
      transTableSender.push_back(station_sync_2);
      transTableSender.push_back(station_async);
    }
  

    for (vector<Trans*>::iterator ib =  transTableBus.begin(); ib != transTableBus.end(); ib++){
      if ((*ib)->num == single){
        for (vector<Trans*>::iterator it =  transTableSender.begin(); it != transTableSender.end(); it++){
          if (((*ib)->chan == (*it)->chan) && ((*ib)->chan != 0) && ((*ib)->io != (*it)->io)){
            sprintf(line, "p==%d",(*ib)->start);
            source = string(line);
            guard = (*ib)->enable;
            sprintf(line, " && p%d==%d",(*it)->id, (*it)->start);
            source += line;
            if ((*it)->enable.size() != 0) {
              guard += (*it)->enable;
            }
          
            sprintf(line, "p=%d,p%d=%d",(*ib)->end, (*it)->id, (*it)->end);
            sublist = string(line);
          
            reset = (*ib)->reset;
            if ((*it)->reset.size() != 0) {
              if(reset.size() != 0)
                reset += ",";
              reset += (*it)->reset;
            }
          
            replace = (*ib)->replace;
            if ((*it)->replace.size() != 0){
              if(replace.size() != 0)
                replace += ",";
              replace += (*it)->replace;
            }
          
            TATransition *t = new TATransition(source, guard, sublist, reset, replace);
            myTransitions.push_back(t);
          }
        }
      }
    }
  
    guard = "";
    for (vector<Trans*>::iterator it =  transTableSender.begin(); it != transTableSender.end(); it++){
      if((*it)->chan == 0 && (*it)->io == tau){
        sprintf(line, "p%d==%d",(*it)->id, (*it)->start);
        source = line;
        guard = (*it)->enable;
        sprintf(line, "p%d=%d",(*it)->id, (*it)->end);
        sublist = string(line);
        reset = (*it)->reset;
        replace = (*it)->replace;
      
        TATransition *t = new TATransition(source, guard, sublist, reset, replace);
        myTransitions.push_back(t);
      }
    }
  }
 
};

#endif
