/** \mainpage TimeSolver-TA 1.1
 *
 * A proof-based timed automata model checker.
 * @author Peter Fontana
 * @author Dezhuang Zhang
 * @author Rance Cleaveland
 * @author Jeroen Keiren
 * @copyright MIT Licence, see the accompanying LICENCE.txt
 */

/** \file timesolver-ta.cc
 * The main file of the timed automata model checker. This file handles options,
 * parses the inputs, and subsequently calls the solver.
 * @author Peter Fontana
 * @author Dezhuang Zhang
 * @author Rance Cleaveland
 * @author Jeroen Keiren
 * @copyright MIT Licence, see the accompanying LICENCE.txt
 */

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
#include "cpplogging/logger.h"
#include "ExprNode.hh"
#include "sequent_stack.hh"
#include "proof.hh"
#include "errno.h"
#include "pes.hh"
#include "parse.hh"

/** Defines DEBUG mode to True (1)
 * if not already defined. */
#ifndef DEBUG
#define DEBUG 1
#endif

/** Prints out the "help" info for the user or
 * the information that is displayed when the
 * user does not give or format the argument properly.
 * @return none.*/
void printUsage() {
  std::cerr << "usage: demo options input_file_name" << std::endl;
  std::cerr
      << "\t option: -d  print debug information which includes the proof tree"
      << std::endl;
  std::cerr << "\t option: -t print out the end caches of sequents" << std::endl;
  std::cerr << "\t option: -h  this help info" << std::endl;
  std::cerr << "\t option: -n (no caching) disables performance-optimizing "
               "known true and known false caches. Circularity stack caching "
               "still used."
            << std::endl;
}

/** Structure to collect the options passed to the tool, and passed into the
 * algorithm */
struct tool_options {
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

  /** Filename for the input */
  std::string input_filename;

  tool_options()
      : debug(false), tabled(false), nHash(16), nbits(0xF), useCaching(true) {}
};

/** Parsers the command line */
void parse_command_line(int argc, char** argv, tool_options& opt) {
  /* Sets parameters and looks for inputs from the command line. */
  char c;

  while ((c = getopt(argc, argv, "dhntH:")) != -1) {
    switch (c) {
      case 'd':
        opt.debug = true; // Turn on Debug Mode
        break;
      case 't': // Turn on tabled output
        /* This outputs the lists of tabled sequents
         * used in sequent caching */
        opt.tabled = true;
        break;
      case 'H': // change the Hash Size
        opt.nHash = atoi(optarg);
        opt.nbits = opt.nHash - 1;
        if (opt.nHash < 1) {
          std::cerr << "Hashed number must be greater than 0." << std::endl;
          exit(-1);
        }
        break;
      case 'n':
        opt.useCaching = false;
        break;
      case 'h': // Help: print the Usage.
        printUsage();
        exit(1);
    }
  }
  if (argc < 2) {
    fprintf(stderr, "Must have an input file argument.\n");
    printUsage();
    exit(-1);
  }

  for (int i = 0; i < argc; i++) {
    std::cerr << argv[i] << " ";
  }
  std::cerr << std::endl;

  opt.input_filename = std::string(argv[argc - 1]);
}

/** The main method that takes in an example file
 * and then does Real-Time Model Checking on it.
 * basic syntax is "demo options input_file_name".
 * @param argc The number of input arguments (the program
 * name is the first argument).
 * @param argv (**) The array of strings containing
 * the program arguments.
 * @return 0 for a normal exit, -1 for an exit upon an error. */
int main(int argc, char** argv) {
  cpplogging::logger::register_output_policy(cpplogging::plain_output_policy());
  cpplogging::logger::unregister_output_policy(
      cpplogging::default_output_policy());

  tool_options opt;
  parse_command_line(argc, argv, opt);
  if (opt.debug) {
    cpplogging::logger::set_reporting_level(cpplogging::debug);
  }

  cpplog(cpplogging::info)
      << "\n\n====Begin Program Input==============================" << std::endl;
  /* Get times for lexing and parsing files: */
  time_t rawtime_lp;
  time(&rawtime_lp);
  /* print Starting time */
  cpplog(cpplogging::debug) << "Program start time: " << ctime(&rawtime_lp);

  clock_t begin_lp = clock();

  pes input_pes;
  parse_pes(opt.input_filename, opt.debug, input_pes);

  /* Inputs have now be approved and values set.  Here
   * the Real-Time Model Checking begins */
  /* Start the Model Checking */
  cpplog(cpplogging::info) << "Program input file (timed automaton + MES): "
                           << opt.input_filename << std::endl;
  cpplog(cpplogging::info) << "max constant in clock constraints: " << input_pes.max_constant()
                           << std::endl
                           << std::endl;

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
  cpplog(cpplogging::debug)
      << "##--Beginning of Proof==-------------------" << std::endl
      << "Prover start time: " << ctime(&rawtime);

  clock_t begin = clock();
  bool suc;

  if (cpplogEnabled(cpplogging::debug)) {
    // Print Transitions
    cpplog(cpplogging::debug) << std::endl << "TRANSITIONS:" << std::endl;
    for (std::vector<const Transition*>::const_iterator it =
             input_pes.transitions().begin();
         it != input_pes.transitions().end(); it++) {
      cpplog(cpplogging::debug) << **it << std::endl;
    }
    cpplog(cpplogging::debug) << std::endl;
  }

  /* Call the Model Checker with the given ExprNode
   * to prove or disprove the specification. */
  prover p(input_pes, opt.useCaching, opt.nHash, opt.nbits);

  suc = p.do_proof_init(input_pes);

  /* Now finished with the proof/disproof, so output the result of the Model
   * Checker */
  clock_t end = clock();
  time(&rawtime);

  cpplog(cpplogging::debug) << "Prover end time: " << ctime(&rawtime);
  cpplog(cpplogging::debug) << "##--End of Proof==------------------" << std::endl
                            << std::endl;
  if (suc) {
    cpplog(cpplogging::info)
        << "--==Program Result:  **Valid**  ==-------------------" << std::endl;
    cpplog(cpplogging::info)
        << "Valid proof found. The timed automaton satisfies the MES." << std::endl
        << std::endl;
  } else {
    cpplog(cpplogging::info)
        << "--==Program Result:  **Invalid**  ==-----------------" << std::endl;
    cpplog(cpplogging::info)
        << "Invalid proof found. The timed automaton does not satisfy the MES."
        << std::endl
        << std::endl;
  }

  double totalTime =
      clockToSecs * (end_lp + begin_lp) + clockToSecs * (end - begin);

  cpplog(cpplogging::info) << "--==Program Time:  **"
                           << clockToSecs * (end_lp + begin_lp) +
                                  clockToSecs * (end - begin)
                           << " seconds**  ==----------" << std::endl;
  cpplog(cpplogging::info) << "Lexer and parser running time: "
                           << clockToSecs * (end_lp - begin_lp) << " seconds"
                           << std::endl;
  cpplog(cpplogging::info) << "Prover running time: "
                           << clockToSecs * (end - begin) << " seconds" << std::endl;
  cpplog(cpplogging::info) << "Combined running time: " << totalTime
                           << " seconds" << std::endl;

  cpplog(cpplogging::info) << "Number of locations: " << p.getNumLocations()
                           << std::endl;

  if (cpplogEnabled(cpplogging::debug) && opt.tabled) {
    p.printTabledSequents(std::cerr);
  }

  cpplog(cpplogging::info)
      << "==--End of Program Execution-----------------------==" << std::endl;

  return 0;
}
