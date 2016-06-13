//To Generate the examples for fddi case study

#include <iostream>
#include <fstream>
#include <string>
#include <vector>
#include "TATransition.hh"
#include "FddiModel.hh"

using namespace std;

int main(int argc, char **argv) {
  if (argc < 2) {cerr << "must provide a number of processes; can provide a file path as an additional argument." << endl; exit(-1);}
  // In file
  int process = atoi(argv[1]);
  string fileBase;
  if (argc >= 3) {
    fileBase = argv[2];
  }
  else {
    fileBase = "./GeneratorOutputs/FDDI";
  }
  if( process < 1 || process > 20) {cerr << "process number between 2 and 20" << endl; exit(-1);}
  
  char line[STRLEN];
   
  /* Generate the Model */ 
  FddiModel myFDDI(process);
  
  /*=======================================================*/
  /*----------- Insert Specifications Here ----------------*/
  /*=======================================================*/
  ofstream ofs;
  string fileSuffix = ".in";
  string processStr = argv[1];
  string fileStr = "";
  
  /* variables used in specifications */
  string phi;
  string phi1;
  string phi2;
  string phi3;
  bool first;
  
  /*---- New Spec: AS */
  /*------------------------------------*/
  fileSuffix = "-" + processStr + "-a-s.in"; /* Give suffix */
  fileStr = fileBase + fileSuffix;
  ofs.open(fileStr.c_str());
  myFDDI.printModelPartBeforeSpec(ofs, "");
  
  ofs << "PREDICATE: {X}" <<endl;
  ofs << "START: X" <<endl;
  
  ofs << "EQUATIONS: {" <<endl;
  /* The specification does not need to iterate over all processes
   * Because the process behavior is symmetric and operators
   * are commutative and associative */
  //   ofs << "1: nu X = (";
  //   bool first = true;
  //   for(int i=1; i <= process - 1; i++) {
  // 	  for(int j=i+1; j <= process; j++) {
  //
  // 		  if(first) {first = false;}
  // 		  else { ofs << " && "; }
  // 		  sprintf(line, "(p%d == %d || p%d == %d)",i,IDLE,j,IDLE);
  // 		  ofs << line;
  // 	  }
  //   }
  //   ofs << ")" <<endl;
  //ofs << "1: nu X =  ((p1 != 1 && p1 != 2) || (p2 != 1 && p2 != 2))" <<endl;
  ofs << "1: nu X =  ((p1 == 0 || p2 == 0))";
  ofs << " && \\forall time(\\AllAct(X))" << endl;
  
  ofs << "}" <<endl;
  
  myFDDI.printModelPartAfterSpec(ofs);
  ofs.close();
  
  /*---- New Spec: BS */
  /*------------------------------------*/
  fileSuffix = "-" + processStr + "-b-s.in"; /* Give suffix */
  fileStr = fileBase + fileSuffix;
  ofs.open(fileStr.c_str());
  myFDDI.printModelPartBeforeSpec(ofs, "");
  
  ofs << "PREDICATE: {X}" <<endl;
  ofs << "START: X" <<endl;
  
  ofs << "EQUATIONS: {" <<endl;
  // Insert Buggy Spec Here
  /* Note: this is not symmetric and must require a full
  * iteration */
  ofs << "1: nu X =  \\forall time((";
   first = true;
  for(int i = 1; i <= process; i++) {
  	sprintf(line, "(x<%d || x > %d || p%d==2)", 20*i, 20*i,i);
	  if (first) first = false;
	  else ofs <<" && ";
	  ofs << line;
  }
  
  ofs << ")" << endl;
  ofs << " && \\AllAct(X))" << endl;
  
  
  ofs << "}" << endl;
  
  myFDDI.printModelPartAfterSpec(ofs);
  ofs.close();
  
  /*---- New Spec: AL */
  /*------------------------------------*/
  fileSuffix = "-" + processStr + "-a-l.in"; /* Give suffix */
  fileStr = fileBase + fileSuffix;
  ofs.open(fileStr.c_str());
  myFDDI.printModelPartBeforeSpec(ofs, "");
  
  ofs << "PREDICATE: {X}" <<endl;
  ofs << "START: X" <<endl;
  
  ofs << "EQUATIONS: {" <<endl;
  // for ease of generation, write the property phi first
  phi = "(";
  sprintf(line, "p==%d", 2*process);
  phi += line;
  phi += ")";
  
  ofs << "1: mu X = \\forall time\\rel[" << phi << "]";
  ofs << "(" << phi << " || " << "\\AllAct(X))" << " && ";
  ofs << "(UnableWaitInf || \\exists time(" << phi << "))" << endl;
  
  ofs << "}" <<endl;
  
  myFDDI.printModelPartAfterSpec(ofs);
  ofs.close();
  
  /*---- New Spec: BL */
  /*------------------------------------*/
  fileSuffix = "-" + processStr + "-b-l.in"; /* Give suffix */
  fileStr = fileBase + fileSuffix;
  ofs.open(fileStr.c_str());
  myFDDI.printModelPartBeforeSpec(ofs, "");
  
  ofs << "PREDICATE: {X}" <<endl;
  ofs << "START: X" <<endl;
  
  ofs << "EQUATIONS: {" <<endl;
  // for ease of generation, write the property phi first
  phi = "(";
  sprintf(line, "p%d==2", 2);
  phi += line;
  phi += ")";
  
  ofs << "1: mu X = \\forall time\\rel[" << phi << "]";
  ofs << "(" << phi << " || " << "\\AllAct(X))" << " && ";
  ofs << "(UnableWaitInf || \\exists time(" << phi << "))" << endl;
  
  ofs << "}" <<endl;
  
  myFDDI.printModelPartAfterSpec(ofs);
  ofs.close();
  
  /*---- New Spec: M1 */
  /*------------------------------------*/
  fileSuffix = "-" + processStr + "-M1.in"; /* Give suffix */
  fileStr = fileBase + fileSuffix;
  ofs.open(fileStr.c_str());
  myFDDI.printModelPartBeforeSpec(ofs, "");
  
  ofs << "PREDICATE: {X,X2}" <<endl;
  ofs << "START: X" <<endl;
  
  ofs << "EQUATIONS: {" <<endl;
    // for ease of generation, write the property phi first
  phi = "(";
  sprintf(line, "{p1 == 0} || X2");
  phi += line;
  phi += ")";
  
  ofs << "1: nu X = " << "\\forall time( " << phi << " && \\AllAct(X))" << endl;
  
  
  phi2 = "(";
  sprintf(line, "p1 == 0");
  phi2 += line;
  phi2 += ")";
  ofs << "2: mu X2 = \\forall time\\rel[" << phi2 << "]";
  ofs << "(" << phi2 << " || " << "\\AllAct(X2))" << " && ";
  ofs << "(UnableWaitInf || \\exists time(" << phi2 << "))" << endl;

  ofs << "}" <<endl;
  
  myFDDI.printModelPartAfterSpec(ofs);
  ofs.close();
  
  /*---- New Spec: M2 */
  /*------------------------------------*/
  fileSuffix = "-" + processStr + "-M2.in"; /* Give suffix */
  fileStr = fileBase + fileSuffix;
  ofs.open(fileStr.c_str());
  myFDDI.printModelPartBeforeSpec(ofs, "");
  
  ofs << "PREDICATE: {X}" <<endl;
  ofs << "START: X" <<endl;
  
  ofs << "EQUATIONS: {" <<endl;
    // for ease of generation, write the property phi first
  phi = "(";
  sprintf(line, "p2 == 2");
  phi += line;
  phi += ")";
  
  ofs << "1: mu X = " << "\\exists time( " << phi << " || \\ExistAct(X))" << endl;
  
  ofs << "}" <<endl;
  
  myFDDI.printModelPartAfterSpec(ofs);
  ofs.close();
  
  /*---- New Spec: M3 */
  /*------------------------------------*/
  fileSuffix = "-" + processStr + "-M3.in"; /* Give suffix */
  fileStr = fileBase + fileSuffix;
  ofs.open(fileStr.c_str());
  myFDDI.printModelPartBeforeSpec(ofs, "");
  
  ofs << "PREDICATE: {X}" <<endl;
  ofs << "START: X" <<endl;
  
  ofs << "EQUATIONS: {" <<endl;
  // for ease of generation, write the properties phi1 and phi2 first
	// phi1
  phi1 = "(";
  sprintf(line, "p3 == 0");
  phi1 += line;
  phi1 += ")";
  // phi2
  phi2 = "(";
  phi2 += "p == 5";
  phi2 += ")";
  
  ofs << "1: mu X = \\forall time\\rel[" << phi2 << "]( (" << phi1 << " || " << phi2 << ") && (" << phi2 << " || \\AllAct(X)))";
  ofs << " && ( UnableWaitInf || \\exists time\\rel[" << phi1 << "](" << phi2 << "))"; 
  ofs << "}" <<endl;
  
  myFDDI.printModelPartAfterSpec(ofs);
  ofs.close();
  
  /*---- New Spec: M4 */
  /*------------------------------------*/
  fileSuffix = "-" + processStr + "-M4.in"; /* Give suffix */
  fileStr = fileBase + fileSuffix;
  ofs.open(fileStr.c_str());
  myFDDI.printModelPartBeforeSpec(ofs, "");
  
  ofs << "PREDICATE: {X,X2,X3}" <<endl;
  ofs << "START: X" <<endl;
  
  ofs << "EQUATIONS: {" <<endl;
  // Store the amount of time to wait
  int waitTime = 3*(20 + 0 + (50*process + 20));
  // for ease of generation, write the property phi first
	// phi
  phi = "(";
  sprintf(line, "p==1 && X2", waitTime);
  phi += line;
  phi += ")";
  phi2 = "(";
  sprintf(line, "p!=1 && X3", waitTime);
  phi2 += line;
  phi2 += ")";
  phi3 = "(";
  sprintf(line, "p==1", waitTime);
  phi3 += line;
  phi3 += ")";
  
  ofs << "1: mu X = " << "\\exists time( " << phi << " || \\ExistAct(X))" << endl;
  ofs << "2: mu X2 = " << "\\exists time( " << phi2 << " || \\ExistAct(X2))" << endl;
  ofs << "3: mu X3 = " << "\\exists time( " << phi3 << " || \\ExistAct(X3))" << endl;
  
  ofs << "}" <<endl;
  
  myFDDI.printModelPartAfterSpec(ofs);
  ofs.close();
  
  
  return 1;
}
