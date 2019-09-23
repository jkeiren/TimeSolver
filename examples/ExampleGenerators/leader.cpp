//To Generate the examples for leader case study

#include <iostream>
#include <fstream>
#include <string>
#include <vector>
#include "TATransition.h"
#include "LeaderModel.h"
#include <stdlib.h>

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
    fileBase = "./GeneratorOutputs/LEADER";
  }
  if( process < 1 || process > 20) {cerr << "process number between 2 and 20" << endl; exit(-1);}
  
  char line[STRLEN];
   
  /* Generate the Model */ 
  LeaderModel myLEADER(process);
  
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
  myLEADER.printModelPartBeforeSpec(ofs, "");
  
  ofs << "PREDICATE: {X}" <<endl;
  ofs << "START: X" <<endl;
  
  ofs << "EQUATIONS: {" <<endl;
  ofs << "1: nu X = ";
  first = true;
  ofs << "(";
  /* This specification is stronger: it checks for
   * a more correct hierarchy */
  for (int i = 1; i <= process; i++){
    sprintf(line, "(p%d < %d)", i, i);
    if (first) first = false;
    else ofs <<"\t&&";
    ofs << line <<endl;
  }
  ofs << ")";
  ofs << " && \\forall time(\\AllAct(X))" << endl;
  
  ofs << "}" <<endl;
  
  myLEADER.printModelPartAfterSpec(ofs);
  ofs.close();
  
  /*---- New Spec: BS */
  /*------------------------------------*/
  fileSuffix = "-" + processStr + "-b-s.in"; /* Give suffix */
  fileStr = fileBase + fileSuffix;
  ofs.open(fileStr.c_str());
  myLEADER.printModelPartBeforeSpec(ofs, "");
  
  ofs << "PREDICATE: {X}" <<endl;
  ofs << "START: X" <<endl;
  
  ofs << "EQUATIONS: {" <<endl;
  ofs << "1: nu X = ";
  first = true;
  // Write Buggy Spec that at least three process
  // have no children
  // Include Parentheses for correctness
  /* Due to the symmetries being absored into the 
   * state machine, we must iterate the specification
   * for all processes */
  ofs << "(";
  for (int i = 1; i <= process - 2; i++) {
  	for(int j = i+1; j<= process - 1; j++) {
      for(int k=j+1; k<=process; k++) {
        if(i == j || i == k || j == k) {
          continue;
        }
        sprintf(line, "(p%d == 0 && p%d == 0 && p%d==0)", i, j,k);
        if (first) first = false;
        else ofs <<"\t||";
        ofs << line <<endl;
          
      }
    }
  }
  ofs << ")";
  ofs << " && \\forall time(\\AllAct(X))" << endl;
  
  ofs << "}" <<endl;
  
  myLEADER.printModelPartAfterSpec(ofs);
  ofs.close();
  
  /*---- New Spec: AL */
  /*------------------------------------*/
  fileSuffix = "-" + processStr + "-a-l.in"; /* Give suffix */
  fileStr = fileBase + fileSuffix;
  ofs.open(fileStr.c_str());
  myLEADER.printModelPartBeforeSpec(ofs, "");
  
  ofs << "PREDICATE: {X}" <<endl;
  ofs << "START: X" <<endl;
  
  ofs << "EQUATIONS: {" <<endl;
  
  // for ease of generation, write the property phi first
  phi = "(";
  phi += "(p1 == 0)";
  // first = true;
  for (int i = 2; i <= process; i++){
    sprintf(line, "(p%d != 0)", i);
   // if (first) first = false;
    phi += " && ";
    phi += line;
  }
  phi += ")";
  
  ofs << "1: mu X = " << "{" << phi << "}" << " || ";
  ofs << "(UnableWaitInf && \\forall time(\\AllAct(X)))" << endl; 
  
  ofs << "}" <<endl;
  
  myLEADER.printModelPartAfterSpec(ofs);
  ofs.close();
  
  /*---- New Spec: BL */
  /*------------------------------------*/
  fileSuffix = "-" + processStr + "-b-l.in"; /* Give suffix */
  fileStr = fileBase + fileSuffix;
  ofs.open(fileStr.c_str());
  myLEADER.printModelPartBeforeSpec(ofs, "");
  
  ofs << "PREDICATE: {X}" <<endl;
  ofs << "START: X" <<endl;
  
  ofs << "EQUATIONS: {" <<endl;
  
  // for ease of generation, write the property phi first
  phi = "( p3 == 1)";
  
  ofs << "1: mu X = " << "{" << phi << "}" << " || ";
  ofs << "(UnableWaitInf && \\forall time(\\AllAct(X)))" << endl; 
  
  ofs << "}" <<endl;
  
  myLEADER.printModelPartAfterSpec(ofs);
  ofs.close();
  
  /*---- New Spec: M1 */
  /*------------------------------------*/
  fileSuffix = "-" + processStr + "-M1.in"; /* Give suffix */
  fileStr = fileBase + fileSuffix;
  ofs.open(fileStr.c_str());
  myLEADER.printModelPartBeforeSpec(ofs,"");
  
  ofs << "PREDICATE: {X}" <<endl;
  ofs << "START: X" <<endl;
  
  ofs << "EQUATIONS: {" <<endl;
  
  // for ease of generation, write the properties phi1 and phi2 first
	// phi1
	phi1 = "(";
  first = true;
  for (int i = 1; i <= process; i++){
    sprintf(line, "(p%d != 2)", i);
    if (first) first = false;
    else phi1 += " && ";
    phi1 += line;
  }
  phi1 += ")";
  // phi2
  phi2 = "(";
  sprintf(line, "p%d != 0", 2);
  phi2 += line;
  phi2 += ")";
 
  ofs << "1: mu X = \\forall time\\rel[" << phi2 << "]( (" << phi1 << " || " << phi2 << ") && (" << phi2 << " || \\AllAct(X)))";
  ofs << " && ( UnableWaitInf || \\exists time\\rel[" << phi1 << "](" << phi2 << "))"; 
  ofs << "}" <<endl;
  
  myLEADER.printModelPartAfterSpec(ofs);
  ofs.close();
  
  /*---- New Spec: M2 */
  /*------------------------------------*/
  fileSuffix = "-" + processStr + "-M2.in"; /* Give suffix */
  fileStr = fileBase + fileSuffix;
  ofs.open(fileStr.c_str());
  myLEADER.printModelPartBeforeSpec(ofs, "");
  
  ofs << "PREDICATE: {X,X2}" <<endl;
  ofs << "START: X" <<endl;
  
  ofs << "EQUATIONS: {" <<endl;
  
  // for ease of generation, write the properties phi1 and phi2 first
	// phi1
	phi1 = "(";
  phi1 += "{p3 == 0} || X2";
  phi1 += ")";
  phi2 = "(";
  phi2 += "p3 != 0";
  phi2 += ")";
  
  ofs << "1: nu X = \\forall time((" << phi1 << ") && \\AllAct(X))";
  ofs << "2: nu X2 = \\forall time((" << phi2 << ") && \\AllAct(X2))";
  
  ofs << "}" << endl;
  
  myLEADER.printModelPartAfterSpec(ofs);
  ofs.close();
  
  /*---- New Spec: M3 */
  /*------------------------------------*/
  fileSuffix = "-" + processStr + "-M3.in"; /* Give suffix */
  fileStr = fileBase + fileSuffix;
  ofs.open(fileStr.c_str());
  myLEADER.printModelPartBeforeSpec(ofs, "z");
  
  ofs << "PREDICATE: {X, X2}" <<endl;
  ofs << "START: X" <<endl;
  
  ofs << "EQUATIONS: {" <<endl;
  
  // for ease of generation, write the properties phi1 and phi2 first
	// phi1
	phi = "(";
  phi += "p == 0 && z>=3";
  phi += ")";

  
  ofs << "1: mu X = X2[z]";
  ofs << "2: mu X2 = \\exists time((" << phi << ") || \\ExistAct(X2))";
  
  ofs << "}" << endl;
  
  myLEADER.printModelPartAfterSpec(ofs);
  ofs.close();
  
  /*---- New Spec: M4 */
  /*------------------------------------*/
  fileSuffix = "-" + processStr + "-M4.in"; /* Give suffix */
  fileStr = fileBase + fileSuffix;
  ofs.open(fileStr.c_str());
  myLEADER.printModelPartBeforeSpec(ofs, "");
  
  ofs << "PREDICATE: {X}" <<endl;
  ofs << "START: X" <<endl;
  
  ofs << "EQUATIONS: {" <<endl;
  
  // for ease of generation, write the properties phi1 and phi2 first
	// phi1
	phi = "(";
  phi += "p == 1";
  phi += ")";

  
  ofs << "1: nu X = " << "\\forall time( " << phi << " || \\AllAct(";
  ofs << "\\forall time( " << phi << " || \\AllAct(" << "\\forall time( " << phi << " || \\AllAct(" << "\\forall time( " << phi << " || \\AllAct(" << "\\forall time( " << phi << ")) )) )) )) )" << endl;
  
  ofs << "}" <<endl;
  
  myLEADER.printModelPartAfterSpec(ofs);
  ofs.close();
  
  
  return 1;
}
