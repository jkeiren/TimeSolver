//To Generate the examples for fischer case study

#include <iostream>
#include <fstream>
#include <string>
#include <vector>
#include "TATransition.h"
#include "FischerModel.h"
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
    fileBase = "./GeneratorOutputs/FISCHER";
  }
  if( process < 1 || process > 20) {cerr << "process number between 2 and 20" << endl; exit(-1);}
  
  char line[STRLEN];
   
  /* Generate the Model */ 
  FischerModel myFISCHER(process);
  
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
  myFISCHER.printModelPartBeforeSpec(ofs, "");
  
  ofs << "PREDICATE: {X}" <<endl;
  ofs << "START: X" <<endl;

  ofs << "EQUATIONS: {" <<endl;
  ofs << "1: nu X = ";

  // Print out the property specification
  /* The specification does not need to iterate over all processors 
   * Because the processor behavior is symmetric and operators
   * are commutative and associative */
  ofs << "(p1 != 3 |s| p2 != 3) && \\forall time(\\AllAct(X))" << endl;
 
  ofs << "}" <<endl;
  
  myFISCHER.printModelPartAfterSpec(ofs);
  ofs.close();
  
  /*---- New Spec: BS */
  /*------------------------------------*/
  fileSuffix = "-" + processStr + "-b-s.in"; /* Give suffix */
  fileStr = fileBase + fileSuffix;
  ofs.open(fileStr.c_str());
  myFISCHER.printModelPartBeforeSpec(ofs, "");
  
  ofs << "PREDICATE: {X}" <<endl;
  ofs << "START: X" <<endl;

  ofs << "EQUATIONS: {" <<endl;
  ofs << "1: nu X = ";

  // Print out the property specification
  /* The specification does not need to iterate over all processors 
   * Because the processor behavior is symmetric and operators
   * are commutative and associative */
  if(process < 5) { // Then this is true, so print out vacuous spec
	  ofs << "(p1 != 5)";
  }
  else{  // At least one of the first five processes is not waiting
	  ofs << "(p1 != 2 |s| p2 != 2 |s| p3 != 2 |s| p4 != 2 |s| p5 != 2)";
  }
  ofs << "&& \\forall time(\\AllAct(X))" << endl;
  ofs << "}" <<endl;
  
  myFISCHER.printModelPartAfterSpec(ofs);
  ofs.close();
  
  /*---- New Spec: AL */
  /*------------------------------------*/
  fileSuffix = "-" + processStr + "-a-l.in"; /* Give suffix */
  fileStr = fileBase + fileSuffix;
  ofs.open(fileStr.c_str());
  myFISCHER.printModelPartBeforeSpec(ofs, "");
  
  ofs << "PREDICATE: {X}" <<endl;
  ofs << "START: X" <<endl;

  ofs << "EQUATIONS: {" <<endl;
  // for ease of generation, write the property phi first
  phi = "(";
  first = true;
  for (int i = 1; i <= process; i++) {
    sprintf(line, "(p%d == 0)", i);
    if (first) first = false;
    else phi += " && ";
    phi += line;
  }
  phi += ")";
  
  ofs << "1: mu X = " << "{" << phi << "}" << " || ";
  ofs << "(UnableWaitInf && \\forall time(\\AllAct(X)))" << endl; 
  ofs << "}" <<endl;
  
  myFISCHER.printModelPartAfterSpec(ofs);
  ofs.close();
  
  /*---- New Spec: BL */
  /*------------------------------------*/
  fileSuffix = "-" + processStr + "-b-l.in"; /* Give suffix */
  fileStr = fileBase + fileSuffix;
  ofs.open(fileStr.c_str());
  myFISCHER.printModelPartBeforeSpec(ofs, "");
  
  ofs << "PREDICATE: {X}" <<endl;
  ofs << "START: X" <<endl;

  ofs << "EQUATIONS: {" <<endl;
  // for ease of generation, write the property phi first
  phi = "(";
  first = true;
  for (int i = 1; i <= process; i++){
    sprintf(line, "(p%d == 2)", i);
    if (first) first = false;
    else phi += " |s| ";
    phi += line;
  }
  phi += ")";
  
  ofs << "1: mu X = " << "{" << phi << "}" << " || ";
  ofs << "(UnableWaitInf && \\forall time(\\AllAct(X)))" << endl; 
  ofs << "}" <<endl;
  
  myFISCHER.printModelPartAfterSpec(ofs);
  ofs.close();
  
  /*---- New Spec: M1 */
  /*------------------------------------*/
  fileSuffix = "-" + processStr + "-M1.in"; /* Give suffix */
  fileStr = fileBase + fileSuffix;
  ofs.open(fileStr.c_str());
  myFISCHER.printModelPartBeforeSpec(ofs,"");
  
  ofs << "PREDICATE: {X,X2}" <<endl;
  ofs << "START: X" <<endl;

  ofs << "EQUATIONS: {" <<endl;
   // for ease of generation, write the property phi first
  phi = "(";
  sprintf(line, "{p%d == 0} || X2", 1);
  phi += line;
  phi += ")";
  
  ofs << "1: nu X = " << "\\forall time( " << phi << " && \\AllAct(X))" << endl;
  
  
  phi2 = "(";
  sprintf(line, "p%d == 3", 1);
  phi2 += line;
  phi2 += ")";
  ofs << "2: mu X2 = " << "{" << phi2 << "}" << " || ";
  ofs << "(UnableWaitInf && \\forall time(\\AllAct(X2)))" << endl; 
  ofs << "}" <<endl;
  
  myFISCHER.printModelPartAfterSpec(ofs);
  ofs.close();
  
  /*---- New Spec: M2 */
  /*------------------------------------*/
  fileSuffix = "-" + processStr + "-M2.in"; /* Give suffix */
  fileStr = fileBase + fileSuffix;
  ofs.open(fileStr.c_str());
  myFISCHER.printModelPartBeforeSpec(ofs, "");
  
  ofs << "PREDICATE: {X,X2}" <<endl;
  ofs << "START: X" <<endl;

  ofs << "EQUATIONS: {" <<endl;
   // for ease of generation, write the property phi first
  phi = "(";
  sprintf(line, "{p%d == 0} || X2", 3);
  phi += line;
  phi += ")";
  
  ofs << "1: nu X = " << "\\forall time( " << phi << " && \\AllAct(X))" << endl;
  
  
  phi2 = "(";
  sprintf(line, "p%d == 3", 3);
  phi2 += line;
  phi2 += ")";
  ofs << "2: mu X2 = " << "{" << phi2 << "}" << " || ";
  ofs << "(UnableWaitInf && \\forall time(\\AllAct(X2)))" << endl; 
  ofs << "}" <<endl;
  
  myFISCHER.printModelPartAfterSpec(ofs);
  ofs.close();
  
  /*---- New Spec: M3 */
  /*------------------------------------*/
  fileSuffix = "-" + processStr + "-M3.in"; /* Give suffix */
  fileStr = fileBase + fileSuffix;
  ofs.open(fileStr.c_str());
  myFISCHER.printModelPartBeforeSpec(ofs, "");
  
  ofs << "PREDICATE: {X}" <<endl;
  ofs << "START: X" <<endl;

  ofs << "EQUATIONS: {" <<endl;
    // for ease of generation, write the property phi first
  phi = "(";
  sprintf(line, "p1 == 3 && x1 <= 0");
  phi += line;
  phi += ")";
  
  ofs << "1: mu X = " << "\\exists time( " << phi << " || \\ExistAct(X))" << endl;
  
  ofs << "}" <<endl;
  
  myFISCHER.printModelPartAfterSpec(ofs);
  ofs.close();
  
  /*---- New Spec: M4 */
  /*------------------------------------*/
  fileSuffix = "-" + processStr + "-M4.in"; /* Give suffix */
  fileStr = fileBase + fileSuffix;
  ofs.open(fileStr.c_str());
  myFISCHER.printModelPartBeforeSpec(ofs, "");
  
  ofs << "PREDICATE: {X}" <<endl;
  ofs << "START: X" <<endl;

  ofs << "EQUATIONS: {" <<endl;
    // for ease of generation, write the property phi first
  phi = "(";
  first = true;
  for (int i = 1; i <= process; i++){
    sprintf(line, "(p%d == 3)", i);
    if (first) first = false;
    else phi += " |s| ";
    phi += line;
  }
  phi += ")";
  
  ofs << "1: nu X = " << "\\forall time( " << phi << " || \\AllAct(";
  ofs << "\\forall time( " << phi << " || \\AllAct(" << "\\forall time( " << phi << " || \\AllAct(" << "\\forall time( " << phi << " || \\AllAct(" << "\\forall time( " << phi << " || \\AllAct(" << phi << ")) )) )) )) ))" << endl;
  
  ofs << "}" <<endl;
  
  myFISCHER.printModelPartAfterSpec(ofs);
  ofs.close();
  
  
  return 1;
}
