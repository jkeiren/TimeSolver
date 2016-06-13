//To Generate the examples for fischer case study

#include <iostream>
#include <fstream>
#include <string>
#include <vector>
#include "TATransition.hh"
#include "GrcModel.hh"
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
    fileBase = "./GeneratorOutputs/GRC";
  }
  if( process < 1 || process > 20) {cerr << "process number between 2 and 20" << endl; exit(-1);}
  
  char line[STRLEN];
   
  /* Generate the Model */ 
  GrcModel myGRC(process);
  
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
  myGRC.printModelPartBeforeSpec(ofs, "");
  
  ofs << "PREDICATE: {X}" <<endl;
	ofs << "START: X" <<endl;
	
	ofs << "EQUATIONS: {" <<endl;
	ofs << "1: nu X = ";
	/* GRC Spec A (Safety Spec):  It is always the case
	 * that if any train is in (on the tracks), then the gate is down.*/
	/*  Iteration is not required to extend it since the processes are symmetric
	 * and operations are commutative and associative, we can only use
  	 * the first part of the spec for a safety property. */
	sprintf(line, "((p%d != %d) |s| (p%d == %d))", 1, in, 
				process + 1, down);
	ofs << line << " && \\forall time(\\AllAct(X))" << endl;
	ofs << "}" <<endl;
  
  myGRC.printModelPartAfterSpec(ofs);
  ofs.close();
  
  /*---- New Spec: BS */
  /*------------------------------------*/
  fileSuffix = "-" + processStr + "-b-s.in"; /* Give suffix */
  fileStr = fileBase + fileSuffix;
  ofs.open(fileStr.c_str());
  myGRC.printModelPartBeforeSpec(ofs, "");
  
  ofs << "PREDICATE: {X}" <<endl;
	ofs << "START: X" <<endl;
	
	ofs << "EQUATIONS: {" <<endl;
	ofs << "1: nu X = ";
	/* GRC Spec B (Invalid Spec):  It is always the case
	 * that if the gate is raising, then the controller is not getting ready 
	 * lower the gate when a new train approaches.
	 * This shows that we need the (raise->lower) edge for the gate. */
	/* Since it only involves the gate and the controller,
	 * it is concise without resulting in symmetry, since
	 * we are only checking the controller for the edge when the first
	 * train approaches. */
	sprintf(line, "((p%d != %d) |s| (p%d != %d))", process + 1, raise, 
				process + 2, 1);
	ofs << line << " && \\forall time(\\AllAct(X))" << endl;
	ofs << "}" <<endl;
  
  myGRC.printModelPartAfterSpec(ofs);
  ofs.close();
  
  /*---- New Spec: AL */
  /*------------------------------------*/
  fileSuffix = "-" + processStr + "-a-l.in"; /* Give suffix */
  fileStr = fileBase + fileSuffix;
  ofs.open(fileStr.c_str());
  myGRC.printModelPartBeforeSpec(ofs, "");
  
  ofs << "PREDICATE: {X}" <<endl;
	ofs << "START: X" <<endl;
	
	ofs << "EQUATIONS: {" <<endl;
	 // for ease of generation, write the property phi first
  phi = "(";
  sprintf(line, "p%d==0", process + 1);
  phi += line;
  phi += ")";
  
  ofs << "1: mu X = " << "{" << phi << "}" << " || ";
  ofs << "(UnableWaitInf && \\forall time(\\AllAct(X)))" << endl; 
  
  ofs << "}" <<endl;
  
  myGRC.printModelPartAfterSpec(ofs);
  ofs.close();
  
  /*---- New Spec: BL */
  /*------------------------------------*/
  fileSuffix = "-" + processStr + "-b-l.in"; /* Give suffix */
  fileStr = fileBase + fileSuffix;
  ofs.open(fileStr.c_str());
  myGRC.printModelPartBeforeSpec(ofs, "");
  
  ofs << "PREDICATE: {X}" <<endl;
	ofs << "START: X" <<endl;
	
	ofs << "EQUATIONS: {" <<endl;
	// for ease of generation, write the property phi first
  phi = "(";
  first = true;
  for (int i = 1; i <= process; i++){
    sprintf(line, "(p%d == 1)", i);
    if (first) first = false;
    else phi += " |s| ";
    phi += line;
  }
  phi += ")";
  
  ofs << "1: mu X = " << "{" << phi << "}" << " || ";
  ofs << "(UnableWaitInf && \\forall time(\\AllAct(X)))" << endl; 
  
  ofs << "}" <<endl;
  
  myGRC.printModelPartAfterSpec(ofs);
  ofs.close();
  
  /*---- New Spec: M1 */
  /*------------------------------------*/
  fileSuffix = "-" + processStr + "-M1.in"; /* Give suffix */
  fileStr = fileBase + fileSuffix;
  ofs.open(fileStr.c_str());
  myGRC.printModelPartBeforeSpec(ofs,"");
  
  ofs << "PREDICATE: {X, X2}" <<endl;
	ofs << "START: X" <<endl;
	
	ofs << "EQUATIONS: {" <<endl;
	 // for ease of generation, write the property phi first
  phi = "(";
  sprintf(line, "{p%d != 2} || X2", process +1);
  phi += line;
  phi += ")";
  
  ofs << "1: nu X = " << "\\forall time( " << phi << " && \\AllAct(X))" << endl;
  
  phi2 = "(";
  sprintf(line, "p%d == 0", process +1);
  phi2 += line;
  phi2 += ")";
  ofs << "2: mu X2 = " << "{" << phi2 << "}" << " || ";
  ofs << "(UnableWaitInf && \\forall time(\\AllAct(X2)))" << endl; 

  ofs << "}" <<endl;
  
  myGRC.printModelPartAfterSpec(ofs);
  ofs.close();
  
  /*---- New Spec: M2 */
  /*------------------------------------*/
  fileSuffix = "-" + processStr + "-M2.in"; /* Give suffix */
  /* Use CWAIT = 2 */
  fileStr = fileBase + fileSuffix;
  ofs.open(fileStr.c_str());
  myGRC.printModelPartBeforeSpec(ofs, "z");
  
  ofs << "PREDICATE: {X, X2}" <<endl;
	ofs << "START: X" <<endl;
	
	ofs << "EQUATIONS: {" <<endl;
	 // for ease of generation, write the property phi first
  phi = "(";
  sprintf(line, "{p%d != 2} || X2[z]", process +1);
  phi += line;
  phi += ")";
  
  ofs << "1: nu X = " << "\\forall time( " << phi << " && \\AllAct(X))" << endl;
  
  phi2 = "(";
  sprintf(line, "p%d == 0 && z <= 2", process +1);
  phi2 += line;
  phi2 += ")";
  ofs << "2: mu X2 = \\forall time\\rel[" << phi2 << "]";
  ofs << "(" << phi2 << " || " << "\\AllAct(X2))" << " && ";
  ofs << "(UnableWaitInf || \\exists time(" << phi2 << "))" << endl;
  
  ofs << "}" <<endl;
  
  myGRC.printModelPartAfterSpec(ofs);
  ofs.close();
  
  /*---- New Spec: M3 */
  /*------------------------------------*/
  fileSuffix = "-" + processStr + "-M3.in"; /* Give suffix */
  fileStr = fileBase + fileSuffix;
  ofs.open(fileStr.c_str());
  myGRC.printModelPartBeforeSpec(ofs, "");
  
  ofs << "PREDICATE: {X}" <<endl;
	ofs << "START: X" <<endl;
	
	ofs << "EQUATIONS: {" <<endl;
	
  phi = "(";
  sprintf(line, "{p1 != 2} || p2 != 2");
  phi += line;
  phi += ")";
  
  ofs << "1: nu X = " << phi << " && " << "\\forall time(\\AllAct(X))" << endl;
  
  ofs << "}" <<endl;
  
  myGRC.printModelPartAfterSpec(ofs);
  ofs.close();
  
  /*---- New Spec: M4 */
  /*------------------------------------*/
  fileSuffix = "-" + processStr + "-M4.in"; /* Give suffix */
  fileStr = fileBase + fileSuffix;
  ofs.open(fileStr.c_str());
  myGRC.printModelPartBeforeSpec(ofs, "");
  
  ofs << "PREDICATE: {X}" <<endl;
	ofs << "START: X" <<endl;
	
	ofs << "EQUATIONS: {" <<endl;
	// for ease of generation, write the properties phi1 and phi2 first
	// phi1
  phi1 = "(";
  sprintf(line, "p%d == 0", process+1);
  phi1 += line;
  phi1 += ")";
  // phi2
  phi2 = "(";
  first = true;
  for (int i = 1; i <= process; i++){
    sprintf(line, "(p%d == 1)", i);
    if (first) first = false;
    else phi2 += " |s| ";
    phi2 += line;
  }
  phi2 += ")";
  // Here, we are only examining paths with an infinite number of
  // actions, and we simplify since phi_1 and phi_2 only involve
  // atomic propositions
  ofs << "1: mu X = " << phi2 << " || (" << phi1 << " && \\forall time(";
  ofs << "\\AllAct(X)))" << endl;
  
  ofs << "}" <<endl;
  
  myGRC.printModelPartAfterSpec(ofs);
  ofs.close();
  
   /*---- New Spec: M4ap */
  /*------------------------------------*/
  fileSuffix = "-" + processStr + "-M4ap.in"; /* Give suffix */
  fileStr = fileBase + fileSuffix;
  ofs.open(fileStr.c_str());
  myGRC.printModelPartBeforeSpec(ofs, "");
  
  ofs << "PREDICATE: {X}" <<endl;
	ofs << "START: X" <<endl;
	
	ofs << "EQUATIONS: {" <<endl;
	// for ease of generation, write the properties phi1 and phi2 first
	// phi1
  phi1 = "(";
  sprintf(line, "p%d == 0", process+1);
  phi1 += line;
  phi1 += ")";
  // phi2
  phi2 = "(";
  first = true;
  for (int i = 1; i <= process; i++){
    sprintf(line, "(p%d == 1)", i);
    if (first) first = false;
    else phi2 += " |s| ";
    phi2 += line;
  }
  phi2 += ")";

  ofs << "1: mu X = \\forall time\\rel[" << phi2 << "]( (" << phi1 << " || " << phi2 << ") && (" << phi2 << " || \\AllAct(X)))";
  ofs << " && ( UnableWaitInf || \\exists time\\rel[" << phi1 << "](" << phi2 << "))"; 
  ofs << "}" <<endl;
  
  myGRC.printModelPartAfterSpec(ofs);
  ofs.close();
  
  return 1;
}
