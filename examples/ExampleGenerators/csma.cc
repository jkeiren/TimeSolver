//To Generate the examples for csma-cd case study

#include <iostream>
#include <fstream>
#include <string>
#include <vector>
#include "TATransition.hh"
#include "CsmaModel.hh"
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
    fileBase = "./GeneratorOutputs/CSMA";
  }
  if( process < 1 || process > 20) {cerr << "process number between 2 and 20" << endl; exit(-1);}
  
  char line[STRLEN];
   
  /* Generate the Model */ 
  CsmaModel myCSMA(process);
  
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
  bool first;
  
  /*---- New Spec: AS */
  /*------------------------------------*/
  fileSuffix = "-" + processStr + "-a-s.in"; /* Give suffix */
  fileStr = fileBase + fileSuffix;
  ofs.open(fileStr.c_str());
  myCSMA.printModelPartBeforeSpec(ofs, "");
  
  ofs << "PREDICATE: {X}" <<endl;
  ofs << "START: X" <<endl;
  
  ofs << "EQUATIONS: {" <<endl;
  /* The original specification seems to be for two processes only,
   * so this attempts to extend it to n processes
   * Iteration is not required to extend it since the processes are symmetric
   * and operations are commutative and associative, we can only use
   * the first part of the spec for a safety property. */
  ofs << "1: nu X = \\forall time(";
  ofs << "({p1 != 1} || ({p2 != 1} || ((x1 < CB) && (x2 < CB)))) && \\AllAct(X))" << endl;
  ofs << "}" <<endl;
  
  myCSMA.printModelPartAfterSpec(ofs);
  ofs.close();
  
  /*---- New Spec: BS */
  /*------------------------------------*/
  fileSuffix = "-" + processStr + "-b-s.in"; /* Give suffix */
  fileStr = fileBase + fileSuffix;
  ofs.open(fileStr.c_str());
  myCSMA.printModelPartBeforeSpec(ofs, "");
  
  ofs << "PREDICATE: {X}" <<endl;
  ofs << "START: X" <<endl;
  
  ofs << "EQUATIONS: {" <<endl;
  /* Change Specification here. (Difference from csmaA)
   * This requires enumerating over the processors */
  /* Since the processes are symmetric, as well as the operations
   * being commutative and associative we can simplify the spec
   * part to only involving a few processes. 
   * Note: Spec is vacuously true for 2 processes. */
  if(process == 2) {
	  // Spec Vacuously true for two processes
	  ofs << "1: nu X = (((p1==1 && p2==1)->(p1 == 1)))" << endl;
  }
  else {
	  ofs << "1: nu X =  (((p1==1 && p2==1)->(p3==2)) && ((p1==1 && p3==1)->(p2==2)) && ((p2==1 && p3==1)->(p1==2)))" << endl;
  }
  ofs << " && \\forall time(\\AllAct(X))" << endl;
  ofs << "}" <<endl;
  
  myCSMA.printModelPartAfterSpec(ofs);
  ofs.close();
  
  /*---- New Spec: AL */
  /*------------------------------------*/
 //  fileSuffix = "-" + processStr + "-a-l.in"; /* Give suffix */
//   fileStr = fileBase + fileSuffix;
//   ofs.open(fileStr.c_str());
//   myCSMA.printModelPartBeforeSpec(ofs, "");
//   
//   ofs << "PREDICATE: {X}" <<endl;
//   ofs << "START: X" <<endl;
//   
//   ofs << "EQUATIONS: {" <<endl;
//   // for ease of generation, write the property phi first
//   phi = "(";
//   first = true;
//   for (int i = 1; i <= process; i++){
//     sprintf(line, "(p%d == 0 && x%d >= 1)", i,i);
//     if (first) first = false;
//     else phi += " || ";
//     phi += line;
//   }
//   phi += ")";
//   
//   ofs << "1: mu X = \\forall time\\rel[" << phi << "]";
//   ofs << "(" << phi << " || " << "\\AllAct(X))" << " && ";
//   ofs << "(UnableWaitInf || \\exists time(" << phi << "))" << endl;
//   
//   ofs << "}" <<endl;
//   
//   myCSMA.printModelPartAfterSpec(ofs);
//   ofs.close();
  fileSuffix = "-" + processStr + "-a-l.in"; /* Give suffix */
  fileStr = fileBase + fileSuffix;
  ofs.open(fileStr.c_str());
  myCSMA.printModelPartBeforeSpec(ofs, "");
  
  ofs << "PREDICATE: {X}" <<endl;
  ofs << "START: X" <<endl;
  
  ofs << "EQUATIONS: {" <<endl;
  // for ease of generation, write the property phi first
  phi = "(";
  first = true;
  for (int i = 1; i <= process; i++){
    sprintf(line, "(p%d == 0)", i,i);
    if (first) first = false;
    else phi += " && ";
    phi += line;
  }
  phi += ")";
  
  ofs << "1: mu X = " << "{" << phi << "}" << " || ";
  ofs << "(UnableWaitInf && \\forall time(\\AllAct(X)))" << endl; 
  ofs << "}" <<endl;
  
  myCSMA.printModelPartAfterSpec(ofs);
  ofs.close();
  
  /*---- New Spec: BL */
  /*------------------------------------*/
  fileSuffix = "-" + processStr + "-b-l.in"; /* Give suffix */
  fileStr = fileBase + fileSuffix;
  ofs.open(fileStr.c_str());
  myCSMA.printModelPartBeforeSpec(ofs, "");
  
  ofs << "PREDICATE: {X}" <<endl;
  ofs << "START: X" <<endl;
  ofs << "EQUATIONS: {" <<endl;
  /* While iteration might not be required due to symmetry, we iterate 
   * anyway. */
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
  
  myCSMA.printModelPartAfterSpec(ofs);
  ofs.close();
  
  /*---- New Spec: M1 */
  /*------------------------------------*/
  fileSuffix = "-" + processStr + "-M1.in"; /* Give suffix */
  fileStr = fileBase + fileSuffix;
  ofs.open(fileStr.c_str());
  myCSMA.printModelPartBeforeSpec(ofs, "");
  
  ofs << "PREDICATE: {X,X2}" <<endl;
  ofs << "START: X" <<endl;
  
  ofs << "EQUATIONS: {" <<endl;
   // for ease of generation, write the property phi first
  phi = "(";
  sprintf(line, "{p1 != 2} || X2");
  phi += line;
  phi += ")";
  
  ofs << "1: nu X = " << "\\forall time( " << phi << " && \\AllAct(X))" << endl;
  
  phi2 = "(";
  sprintf(line, "p1 == 1");
  phi2 += line;
  phi2 += ")";
  ofs << "2: mu X2 = {" << phi2 << "}" << " || ";
  ofs << "(UnableWaitInf && \\forall time(\\AllAct(X2)))" << endl;
  ofs << "}" <<endl;
  
  myCSMA.printModelPartAfterSpec(ofs);
  ofs.close();
  
  /*---- New Spec: M2 */
  /*------------------------------------*/
  fileSuffix = "-" + processStr + "-M2.in"; /* Give suffix */
  fileStr = fileBase + fileSuffix;
  ofs.open(fileStr.c_str());
  myCSMA.printModelPartBeforeSpec(ofs, "");
  
  ofs << "PREDICATE: {X,X2}" <<endl;
  ofs << "START: X" <<endl;
  
  ofs << "EQUATIONS: {" <<endl;
   // for ease of generation, write the property phi first
  phi = "(";
  sprintf(line, "{p != 2} || X2");
  phi += line;
  phi += ")";
  
  ofs << "1: nu X = " << "\\forall time( " << phi << " && \\AllAct(X))" << endl;

  phi2 = "(";
  sprintf(line, "p == 0");
  phi2 += line;
  phi2 += ")";
  ofs << "2: mu X2 = {" << phi2 << "} || ";
  ofs << "(UnableWaitInf && \\forall time(\\AllAct(X2)))" << endl;
  ofs << "}" <<endl;
  
  myCSMA.printModelPartAfterSpec(ofs);
  ofs.close();
  
  /*---- New Spec: M3 */
  /*------------------------------------*/
  fileSuffix = "-" + processStr + "-M3.in"; /* Give suffix */
  fileStr = fileBase + fileSuffix;
  ofs.open(fileStr.c_str());
  myCSMA.printModelPartBeforeSpec(ofs, "");
  
  ofs << "PREDICATE: {X}" <<endl;
  ofs << "START: X" <<endl;
  
  ofs << "EQUATIONS: {" <<endl;
  // for ease of generation, write the properties phi1 and phi2 first
	// phi1
  phi1 = "(";
  sprintf(line, "p == 0");
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
  
  myCSMA.printModelPartAfterSpec(ofs);
  ofs.close();
  
  /*---- New Spec: M4 */
  /*------------------------------------*/
  fileSuffix = "-" + processStr + "-M4.in"; /* Give suffix */
  fileStr = fileBase + fileSuffix;
  ofs.open(fileStr.c_str());
  myCSMA.printModelPartBeforeSpec(ofs, "");
  
  ofs << "PREDICATE: {X}" <<endl;
  ofs << "START: X" <<endl;
  
  ofs << "EQUATIONS: {" <<endl;
  // for ease of generation, write the properties phi1 and phi2 first
	// phi1
  phi1 = "(";
  sprintf(line, "p == 0");
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
  ofs << "1: mu X = " << "{" << phi2 << "}" << " || (" << phi1 << " && \\forall time(";
  ofs << "\\AllAct(X)))" << endl;
  ofs << "}" <<endl;
  
  myCSMA.printModelPartAfterSpec(ofs);
  ofs.close();
  
  
  return 1;
}
