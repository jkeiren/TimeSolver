//To Generate the examples for pathos case study

#include <iostream>
#include <fstream>
#include <string>
#include <vector>
#include "TATransition.h"
#include "PathosModel.h"

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
    fileBase = "./GeneratorOutputs/PATHOS";
  }
  if( process < 1 || process > 20) {cerr << "process number between 2 and 20" << endl; exit(-1);}
  
  char line[STRLEN];
   
  /* Generate the Model */ 
  PathosModel myPATHOS(process);
  
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
  myPATHOS.printModelPartBeforeSpec(ofs, "");
  
  ofs << "PREDICATE: {X}" <<endl;
	ofs << "START: X" <<endl;
	
	ofs << "EQUATIONS: {" <<endl;
	/* Based on scheduling, the highest number is the last process to run.
	 * thus, if it finishes on time, then all processes must finish on time */
	sprintf(line, "1: nu X = \\forall time( ((p%d != 2) || (x%d <= CPERIODUNIT))", process, process);
	ofs << line;
	ofs << " && \\AllAct(X))" << endl;
	
	ofs << "}" <<endl;
  
  myPATHOS.printModelPartAfterSpec(ofs);
  ofs.close();
  
  /*---- New Spec: BS */
  /*------------------------------------*/
  fileSuffix = "-" + processStr + "-b-s.in"; /* Give suffix */
  fileStr = fileBase + fileSuffix;
  ofs.open(fileStr.c_str());
  myPATHOS.printModelPartBeforeSpec(ofs, "");
  
  ofs << "PREDICATE: {X}" <<endl;
	ofs << "START: X" <<endl;
	
	ofs << "EQUATIONS: {" <<endl;
	/* Based on scheduling, the highest number is the last process to run.
	 * thus, if it finishes on time, then all processes must finish on time */
	// Change Spec to be two units earlier.
  sprintf(line, "1: nu X = \\forall time(((p%d != 2) || (x%d <= CPERIODUNITMTWO))", process, process);
  	ofs << line;
	ofs << " && \\AllAct(X))" << endl;
	
	ofs << "}" <<endl;
  
  myPATHOS.printModelPartAfterSpec(ofs);
  ofs.close();
  
  /*---- New Spec: AL */
  /*------------------------------------*/
  fileSuffix = "-" + processStr + "-a-l.in"; /* Give suffix */
  fileStr = fileBase + fileSuffix;
  ofs.open(fileStr.c_str());
  myPATHOS.printModelPartBeforeSpec(ofs, "");
  
  ofs << "PREDICATE: {X}" <<endl;
	ofs << "START: X" <<endl;
	
	ofs << "EQUATIONS: {" <<endl;
	// for ease of generation, write the property phi first
  phi = "(";
  first = true;
  for (int i = 1; i <= process; i++){
    for(int j = 2; j <= process; j++) {
      if(i < j) {
        sprintf(line, "(p%d == 0 && p%d == 0)", i,j);
        if (first) first = false;
        else phi += " || ";
        phi += line;
      }
    }
  }
  phi += ")";
  
  ofs << "1: mu X = \\forall time\\rel[" << phi << "]";
  ofs << "(" << phi << " || " << "\\AllAct(X))" << " && ";
  ofs << "(UnableWaitInf || \\exists time(" << phi << "))" << endl;
  
  ofs << "}" <<endl;
  
  myPATHOS.printModelPartAfterSpec(ofs);
  ofs.close();
  
  /*---- New Spec: BL */
  /*------------------------------------*/
  fileSuffix = "-" + processStr + "-b-l.in"; /* Give suffix */
  fileStr = fileBase + fileSuffix;
  ofs.open(fileStr.c_str());
  myPATHOS.printModelPartBeforeSpec(ofs, "");
  
  ofs << "PREDICATE: {X}" <<endl;
	ofs << "START: X" <<endl;
	
	ofs << "EQUATIONS: {" <<endl;
	// for ease of generation, write the property phi first
  phi = "(p1==1)";
  
  ofs << "1: mu X = \\forall time\\rel[" << phi << "]";
  ofs << "(" << phi << " || " << "\\AllAct(X))" << " && ";
  ofs << "(UnableWaitInf || \\exists time(" << phi << "))" << endl;
  
  ofs << "}" <<endl;
  
  myPATHOS.printModelPartAfterSpec(ofs);
  ofs.close();
  
  /*---- New Spec: M1 */
  /*------------------------------------*/
  fileSuffix = "-" + processStr + "-M1.in"; /* Give suffix */
  fileStr = fileBase + fileSuffix;
  ofs.open(fileStr.c_str());
  myPATHOS.printModelPartBeforeSpec(ofs,"");
  
  ofs << "PREDICATE: {X, X2}" <<endl;
	ofs << "START: X" <<endl;
	
	ofs << "EQUATIONS: {" <<endl;
	phi = "(";
  sprintf(line, "{p%d != 1} || X2", 1);
  phi += line;
  phi += ")";
  
  ofs << "1: nu X = " << "\\forall time( " << phi << " && \\AllAct(X))" << endl;
  
  phi2 = "(";
  sprintf(line, "p%d == 0", 1);
  phi2 += line;
  phi2 += ")";
  ofs << "2: mu X2 = \\forall time\\rel[" << phi2 << "]";
  ofs << "(" << phi2 << " || " << "\\AllAct(X2))" << " && ";
  ofs << "(UnableWaitInf || \\exists time(" << phi2 << "))" << endl;
  ofs << "}" <<endl;
  
  myPATHOS.printModelPartAfterSpec(ofs);
  ofs.close();
  
  /*---- New Spec: M2 */
  /*------------------------------------*/
  fileSuffix = "-" + processStr + "-M2.in"; /* Give suffix */
  fileStr = fileBase + fileSuffix;
  ofs.open(fileStr.c_str());
  myPATHOS.printModelPartBeforeSpec(ofs, "");
  
  ofs << "PREDICATE: {X, X2}" <<endl;
	ofs << "START: X" <<endl;
	
	ofs << "EQUATIONS: {" <<endl;
	phi = "(";
  sprintf(line, "p%d == 2 && AbleWaitInf", 3);
  phi += line;
  phi += ")";
  
  ofs << "1: mu X = \\exists time((" << phi << ") || \\ExistAct(X))";
  ofs << "}" <<endl;
  
  myPATHOS.printModelPartAfterSpec(ofs);
  ofs.close();
  
  /*---- New Spec: M3 */
  /*------------------------------------*/
  fileSuffix = "-" + processStr + "-M3.in"; /* Give suffix */
  fileStr = fileBase + fileSuffix;
  ofs.open(fileStr.c_str());
  myPATHOS.printModelPartBeforeSpec(ofs, "");
  
  ofs << "PREDICATE: {X, X2}" <<endl;
	ofs << "START: X" <<endl;
	
	ofs << "EQUATIONS: {" <<endl;
	// for ease of generation, write the properties phi1 and phi2 first
	// phi1
  phi1 = "(";
  sprintf(line, "{p%d == 0} || p%d == 2", 2, 2);
  phi1 += line;
  phi1 += ")";
  // phi2
  phi2 = "(";
  first = true;
  sprintf(line, "p%d == 1", 2, 2);
  phi2 += line;
  phi2 += ")";
  ofs << "1: mu X = \\forall time\\rel[" << phi2 << "]( (" << phi1 << " || " << phi2 << ") && (" << phi2 << " || \\AllAct(X)))";
  ofs << " && ( UnableWaitInf || \\exists time\\rel[" << phi1 << "](" << phi2 << "))"; 
  ofs << "}" <<endl;
  
  myPATHOS.printModelPartAfterSpec(ofs);
  ofs.close();
  
  /*---- New Spec: M4 */
  /*------------------------------------*/
  fileSuffix = "-" + processStr + "-M4.in"; /* Give suffix */
  fileStr = fileBase + fileSuffix;
  ofs.open(fileStr.c_str());
  myPATHOS.printModelPartBeforeSpec(ofs, "");
  
  ofs << "PREDICATE: {X, X2}" <<endl;
	ofs << "START: X" <<endl;
	
	ofs << "EQUATIONS: {" <<endl;
	// for ease of generation, write the properties phi1 and phi2 first
	// phi1
  phi1 = "(";
  sprintf(line, "{p%d == 0} || p%d == 2", 2, 2);
  phi1 += line;
  phi1 += ")";
  // phi2
  phi2 = "(";
  first = true;
  sprintf(line, "p%d == 1", 2, 2);
  phi2 += line;
  phi2 += ")";
  // Here, we are only examining paths with an infinite number of
  // actions, and we simplify since phi_1 and phi_2 only involve
  // atomic propositions
  ofs << "1: mu X = " << phi2 << " || (" << phi1 << " && \\forall time(";
  ofs << "\\AllAct(X)))" << endl;
  
  ofs << "}" <<endl;
  
  myPATHOS.printModelPartAfterSpec(ofs);
  ofs.close();
  
  
  return 1;
}
