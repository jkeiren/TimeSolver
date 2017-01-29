/** \mainpage CWB-RT PES Tool pes.timed 1.0
 *
 * A proof-based timed automata model checker.
 * @author Peter Fontana, Dezhuang Zhang, and Rance Cleaveland. 
 * @version 1.21
 * @date November 8, 2013 */

/** \file demo.cc
 * The main file of the timed automata model checker. This file
 * contains the bulk of the proof engine and the model checking
 * algorithms, including the implementation of the PES proof rules.
 * @author Peter Fontana, Dezhuang Zhang, and Rance Cleaveland. 
 * @version 1.21
 * @date November 8, 2013 */

#include <iostream>
#include <string.h>
#include <stdio.h>
#include <map>
#include <set>
#include <deque>
#include <vector>
#include <list>
#include <utility>
#include <sys/timeb.h>
#include <time.h>
#include <unistd.h>
#include "ExprNode.hh"
#include "proof_data.hh"
#include "proof.hh"
#include "errno.h"

using namespace std;

/** Defines DEBUG mode to True (1)
 * if not already defined. */
#ifndef DEBUG
#define DEBUG 1
#endif

/** The location of the File pointer
 * for the lexer.
 * @see pes.l and pes.lex.c (lexer files). */
extern FILE *yyin;
/** A variable representing the line number. */
extern  int yyline;
/** The number of errors (syntax or otherwise) in the expressions.
 * I believe the inital value is 0. */
int numErrs;
/** The method that parses the lexed file
 * and creates the ExprNode objects.
 * @return 0 if successful, 1 if syntax error,
 * and 2 if out of memory error (usually).
 * @see pes.y pes.tab.h and pes.tab.c (parser files). */
extern int yyparse(bool debug, std::vector<Transition *> *transList,
                   std::vector<ExprNode*>& invs, int& MAXC,
                   std::string& start_predicate, int& predicateInd, DBM*& InitC,
                   bidirectional_map<std::string, int>* declared_clocks,
                   bidirectional_map<std::string, int>* declared_atomic,
                   std::map<std::string,ExprNode*>* declared_predicates,
                   std::map<int,int>* InitSub);

/** Prints out an error if it occurs during the parsing process.
 * This method is only used in the parser.
 * @param s (*) The error string to print out.
 * @return None */
void
yyerror(bool /*debug*/, std::vector<Transition *>* /*transList*/,
        std::vector<ExprNode*>& /*invs*/, int& /*MAXC*/, std::string& /*start_predicate*/,
        int& /*predicateInd*/, DBM*& /*InitC*/, bidirectional_map<std::string, int>* /*declared_clocks*/,
        bidirectional_map<std::string, int>* /* declared_atomic*/,
        std::map<std::string, ExprNode*>*,
        std::map<int,int>*, char *s)
{
  std::cerr << " line " << yyline << ": ";
  if (s == NULL) cerr << "syntax error";
  else std::cerr << s;
  std::cerr << endl;
  numErrs++;
}

/** A Hash table storing a list of PES variables, with their 
 * string labels
 * and the right hand side expressions in their equations. */
extern map <string, ExprNode *> equations;

/** This represents the number of clocks in the timed automata, which
 * is referred to the number of dimensions (the space) of the automata.
 * This number includes the dummy "zero" clock.
 * @see ExprNode.cc*/
extern int spaceDimension;

/** Prints out the "help" info for the user or
 * the information that is displayed when the
 * user does not give or format the argument properly.
 * @return none.*/
void printUsage(){
  cout << "usage: demo options input_file_name" << endl;
  cout << "\t option: -d  print debug information which includes the proof tree" << endl;
  cout << "\t option: -t print out the end caches of sequents" << endl;
  cout << "\t option: -h  this help info" << endl;
  cout << "\t option: -n (no caching) disables performance-optimizing known true and known false caches. Circularity stack caching still used." << endl;
}

/** Structure to collect the options passed to the tool, and passed into the
 * algorithm */
struct tool_options
{
    /** True if debug mode is on, and
     * False if debug mode is off. Running the
     * program with -d sets it to true. */
    bool debug;

    /** If True, use tables in the output.  Else (False),
     * print regular output. */
    bool tabled;

    /** The size of the Hash table of Sequents: nBits + 1 */
    int nHash;

    /** The maximum number of bits used in the hashing function
     * when storing discrete states. */
    int nbits;

    /** Debug boolean to enable or disable known true and known false caches.
     * This parameter does not influence caching of circularities. As a result,
     * correctness is guaranteed but performance is slowed if set to FALSE */
    bool useCaching;

    /** This is the size of the atomic data, used for
     * hashing sequents.
     * This is set within the main(0) method of (demo.cc). */
    int aSize;

    /** Public variable that stores the number of hashing bins.
     * used for ease of locating the proper bin for each sequent,
     * especially when multiple predicate variables exist. */
    int seqStSize;

    /** Filename for the input */
    std::string input_filename;

    tool_options()
      : debug(false),
        tabled(false),
        nHash(16),
        nbits(0xF),
        useCaching(true),
        aSize(0),
        seqStSize(0xF)
    {}
};

/** Parsers the command line */
void parse_command_line(int argc, char** argv, tool_options& opt)
{
  /* Sets parameters and looks for inputs from the command line. */
  char c;

  while ( (c = getopt(argc, argv, "dhntH:")) != -1) {
    switch (c) {
      case 'd' :
        opt.debug = true; // Turn on Debug Mode
        break;
      case 't' : // Turn on tabled output
        /* This outputs the lists of tabled sequents
         * used in sequent caching */
        opt.tabled = true;
        break;
      case 'H' : // change the Hash Size
        opt.nHash = atoi(optarg);
        opt.nbits = opt.nHash - 1;
        if(opt.nHash < 1) {
          cerr << "Hashed number must be greater than 0." << endl;
          exit(-1);
        }
        break;
      case 'n':
        opt.useCaching = false;
        break;
      case 'h' : // Help: print the Usage.
        printUsage();
        exit(1);
    }
  }
  if (argc < 2){
    fprintf(stderr, "Must have an input file argument.\n" );
    printUsage();
    exit(-1);
  }

  for (int i = 0; i < argc; i++){
    cout << argv[i] << " ";
  }
  cout <<endl;

  opt.input_filename = std::string(argv[argc-1]);
}

/** The main method that takes in an example file
 * and then does Real-Time Model Checking on it.
 * basic syntax is "demo options input_file_name".
 * @param argc The number of input arguments (the program
 * name is the first argument).
 * @param argv (**) The array of strings containing
 * the program arguments.
 * @return 0 for a normal exit, -1 for an exit upon an error. */
int main(int argc, char** argv){

  tool_options opt;

  cout << "\n\n====Begin Program Input==============================" << endl;
  /* Get times for lexing and parsing files: */
  time_t rawtime_lp;
  time(&rawtime_lp);
  /* print Starting time */ 
  if(opt.debug) {
    cout <<"Program start time: "<< ctime(&rawtime_lp) ;
  }
  clock_t begin_lp = clock();
  
  parse_command_line(argc, argv, opt);
  
  /** The list of transitions of the state machine
   * from the timed automaton and/or PES description. */
  vector<Transition *> *transList = new vector<Transition *>;

  /** This is a vector (list) of all invariants with their
   * ExprNodes.
   * This is constructed by the parser while the ExprNode Trees
   * are being generated.
   * @see pes.y and pes.tab.c (parser files). */
  vector<ExprNode *> invs;

  /** This parameter is the size of the maximum
   * constant (in the clock constraints).  There
   * is one constant for all of the clocks
   * This is modified by the program and the parser. */
  int MAXC = 0;

  /** The string label of the starting predicate, which
   * should be label the root ExprNode of the expression tree.
   * @see pes.y and pes.tab.c (parser files). */
  //extern char * start_predicate;
  std::string start_predicate;

  /** A global variable that both counts the number
   * of predicates (predicate variables) as well as gives
   * each predicate variable a hashing index. Used to
   * separate sequent storage to give each predicate
   * variable its own bin(s). */
  int predicateInd = 0;

  /** This DBM represents the initial DBM provided
   * if one is provided by the parser. */
  DBM *InitC;

  bidirectional_map<std::string, int>* declared_clocks = new bidirectional_map<std::string,int>();

  /** A Hash table of Atomic values used to store discrete state
   * variables, mapping string names to id values.
   * @see ExprNode.cc. */
  bidirectional_map<std::string, int>* declared_atomic = new bidirectional_map<std::string,int>();

  /** A Hash table storing the list of declared predicates,
   * matching their label with their expression. */
  std::map <std::string, ExprNode *>* declared_predicates = new std::map<std::string,ExprNode*>();

  /** A Hash table of ints storing integer
   * substituations for atomic variables.
   * This maps atomic ids to atomic values, representing
   * the "inital" state for each control (atomic) variable.
   * The map is represented as: (id, val).  0 is the default value.
   * @see ExprNode.cc */
  std::map <int, int>* InitSub = new std::map<int,int>();

  /* Read and lex the input file to tokens for the parser to use. */
  yyin = fopen(opt.input_filename.c_str(), "r");
  if (!yyin) {
    std::cerr << "Cannot open input file " << opt.input_filename << std::endl;
    exit(-1);
  }

  /* Parses the Example File (and produces the ExprNode structure.)
   * Returns 0 if successful, 1 for Syntax Error, and 2 for out of Memory 
   * (usually). */
  int parseError = yyparse(opt.debug, transList, invs, MAXC, start_predicate,
                           predicateInd, InitC, declared_clocks, declared_atomic,
                           declared_predicates, InitSub);
  
  if(parseError) {
    cout << endl << "**Syntax Error: Error Parsing file.**" << endl << endl;
    cout << "==--End of Program Execution-----------------------==" << endl;
    return 1;
  }
  
  /* Inputs have now be approved and values set.  Here
   * the Real-Time Model Checking begins */
  /* Start the Model Checking */
  cout << "Program input file (timed automaton + MES): " << opt.input_filename << endl;
  cout << "max constant in clock constraints: " << MAXC << endl << endl;
  
  
  /* Find the root expression of the Expression tree generated by the parser.
   */
  ExprNode* start = lookup_predicate(start_predicate.c_str(), declared_predicates);
  
  if(start == NULL){
    cout << "Start predicate is not properly given." << endl;
    exit(-1);
  }
  
  opt.aSize = declared_atomic->size();
  /* A Placeholder to remember the current parity;
   * false = lfp parity, true = gfp parity. */
  bool currParityGfp = start->get_Parity();
  /* A Placeholder to remember the previous parity;
   * false = lfp parity, true = gfp parity. */
  bool prevParityGfp = currParityGfp;
  opt.seqStSize = opt.nHash;
  
  /* Create the initial substituation list,
   * either empty or from the initial list 
   * that was generated by the parser. */
  SubstList *sublist = new SubstList(opt.aSize, declared_atomic);
  for(int i=0; i < opt.aSize; i++){
    map <int, int>::iterator it = InitSub->find(i);
    sublist->operator[](i) = (*it).second;
  }
  
  /* Give a default DBM initialization of a DBM
   * to use for the proofs, that represents
   * the current DBM if an inital one is
   * not provided. 
   * This DBM sets all clocks equal to 0. */
  DBM *dbm = new DBM(spaceDimension, declared_clocks);
  for (int i=0; i<spaceDimension; i++) {
    dbm->addConstraint(i,0, 0x1);
  }
  dbm->cf();

  // This number converts system time to seconds.
  // If the runtime is not correct, you may need to change
  // this value
  double clockToSecs = 0.000001;
#ifdef __APPLE__
  // Defined so it produces the right time values
  // Find this my timing a few examples and comparing
  clockToSecs = .000001;
#elif defined __WIN32__ || defined _WIN64 
  clockToSecs = 0.001;
#elif defined __CYGWIN__
  clockToSecs = 0.001; 
#else
  // Use the default clockToSecs value as defined above
#endif
  
  /* Now finished with lexing and parsing */
  clock_t end_lp = clock();
  time(&rawtime_lp);
  
  time_t rawtime;
  time(&rawtime);
  /* print Starting time */ 
  if(opt.debug) {
    cout << "##--Beginning of Proof==-------------------" << endl;
    cout <<"Prover start time: "<< ctime(&rawtime) ;
  }
  clock_t begin = clock();
  bool suc;
  
  #if DEBUG
  // Print Transitions
  if(opt.debug) {
    cout << endl << "TRANSITIONS:" << endl;
    for(vector<Transition *>::iterator it = transList->begin();
        it != transList->end(); it++ ) {
        Transition * tempT = *it;
        print_Transition(tempT, cout);
        cout << endl;   
    }
    cout << endl;
  }
  #endif

  /* Call the Model Checker with the given ExprNode
   * to prove or disprove the specification. */
  prover p(invs, transList,
           currParityGfp,prevParityGfp,opt.useCaching,predicateInd,opt.nHash,
           opt.debug, MAXC, opt.nbits, opt.seqStSize, opt.aSize, declared_clocks,
           declared_predicates);
  
  if (InitC != NULL) {
		InitC->setIsCfFalse();
    InitC->cf();
    suc = p.do_proof(0, InitC, start, sublist);
  }
  else {
    suc = p.do_proof(0, dbm, start, sublist);
  }
  
  /* Now finished with the proof/disproof, so output the result of the Model Checker */
  clock_t end = clock();
  time(&rawtime);
  if(opt.debug) {
   
    cout <<"Prover end time: "<< ctime(&rawtime);
     cout << "##--End of Proof==------------------" << endl << endl;
  }
  if (suc) {
    cout << "--==Program Result:  **Valid**  ==-------------------" << endl;
    cout << "Valid proof found. The timed automaton satisfies the MES." << endl << endl;
  }
  else {
    cout << "--==Program Result:  **Invalid**  ==-----------------" << endl;
    cout << "Invalid proof found. The timed automaton does not satisfy the MES." << endl << endl;
  }
  double totalTime = clockToSecs*(end_lp + begin_lp) + clockToSecs*(end - begin);
  
  cout << "--==Program Time:  **" << clockToSecs*(end_lp + begin_lp) + clockToSecs*(end - begin) << " seconds**  ==----------" << endl;
  cout << "Lexer and parser running time: " << clockToSecs*(end_lp - begin_lp) << " seconds" << endl;
  cout << "Prover running time: " << clockToSecs*(end - begin) << " seconds" << endl; 
  cout << "Combined running time: " << totalTime  << " seconds" << endl;
  
  cout << "Number of locations: " << p.getNumLocations() << endl;
  
  #if DEBUG
  if(opt.tabled){
    p.printTabledSequents(cout);
  }
  #endif
  
  
	// Clean Up Dynamic Memory to eliminate Memory Leaks
  delete dbm;
  if(InitC != NULL)
  {
    delete InitC;
  }

  // Since Vectors and Maps do not call the destructors of its elements
  // We must iterate and delete

  //delete start;
  // Do Extra Work to Delete Elements at the End
	for(vector<ExprNode *>::iterator it = invs.begin(); 
    	it != invs.end(); it++) {
    ExprNode *ls = (*it);
    delete ls;
  }
  // Clear Vectors to free up dynamic memory
  invs.clear();
  
  // Do Extra Work to delete Dynamically Allocated Elements
	for(map<string, ExprNode *>::iterator it = equations.begin(); 
     	it != equations.end(); it++) {
    ExprNode *ls = (*it).second;
    delete ls;
  }
  // Do Extra Work to delete Dynamically Allocated Elements
  // Delete the predicates here since the ExprNode Destructor
  // Does not traverse predicates to make sure of no inconsistencies.
  for(map<string, ExprNode *>::iterator it = declared_predicates->begin();
      it != declared_predicates->end(); it++) {
    ExprNode *ls = (*it).second;
    /* While we should delete, this has problems when an equation
     * is just a predicate. (?)*/
    ls->deletePredicate();
    delete ls;
    
  }
  declared_predicates->clear();
  delete declared_predicates;
  equations.clear();
  
  /* Delete Transitions in transition list */
  for(vector<Transition *>::iterator it = transList->begin();
    it != transList->end(); it++ )
  {
    delete (*it);
  }
  transList->clear();
  delete transList;

  // Clear Maps to free up dynamic memory
  declared_atomic->clear();
  declared_clocks->clear();
  InitSub->clear();
  delete declared_atomic;
  delete declared_clocks;
  delete InitSub;


  // delete other parts
  delete sublist;

  // Close File for good file handling
  fclose(yyin);

  cout << "==--End of Program Execution-----------------------==" << endl;

  return 0;
}

