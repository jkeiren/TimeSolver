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

#include <getopt.h>
#include <cstdlib>
#include <iostream>
#include <cerrno>
#include <cstring>
#include <cstdio>
#include <map>
#include <set>
#include <deque>
#include <vector>
#include <list>
#include <utility>
#include <sys/timeb.h>
#include <ctime>
#include <unistd.h>
#include "cpplogging/logger.h"
#include "ExprNode.hh"
#include "sequent_stack.hh"
#include "prover_options.hh"
#include "proof.hh"
#include "pes.hh"
#include "parse.hh"
#include "version.hh"

#ifndef DEBUG
#define DEBUG true
#endif

#define DEBUG_PLACEHOLDER_PROVER false

/** Prints out the "help" info for the user or
 * the information that is displayed when the
 * user does not give or format the argument properly.
 * @return none.*/
void printUsage() {
  std::cerr << "usage: timesolver-ta options input_file_name" << std::endl;
  std::cerr << "\t option: --debug/-d  print debug information which includes the proof tree"
      << std::endl;
  std::cerr << "\t option: --tabled/-t print out the end caches of sequents" << std::endl;
  std::cerr << "\t option: --hash/-H   sets the number of hashing bins to the number specified. Should be a power of 2" << std::endl;
  std::cerr << "\t option: --help/-h   this help info" << std::endl;
  std::cerr << "\t option: --version   print the version of the tool" << std::endl;
  std::cerr << "\t option: --no-caching/-n disables performance-optimizing "
               "known true and known false caches. Circularity stack caching " << "still used." << std::endl;
  std::cerr << "\t option: --checking-vacuity/-C enables simple vacuity checking "
            << std::endl;
  std::cerr << "\t option: --vacuity-full/-V enables full vacuity checking "
            << std::endl;
}

void printVersion() {
  std::cerr << version() << std::endl;
}

/** Parsers the command line */
void parse_command_line(int argc, char** argv, prover_options& opt) {
  /* Sets parameters and looks for inputs from the command line. */
  const char* const short_opts = "dDhntHCV:";
  const option long_opts[] {
    {"debug", 0, nullptr, 'd'},
    {"full-debug", 0, nullptr, 'D'},
    {"help", 0, nullptr, 'h'},
    {"no-caching", 0, nullptr, 'n'},
    {"tabled-output", 0, nullptr, 't'},
    {"hash", 1, nullptr, 'H'},
    {"version", 0, nullptr, 'v'},
    {"simple-vacuity", 0, nullptr, 'C'},
    {"full-vacuity", 0, nullptr, 'V'},
    {nullptr, 0, nullptr, 0}
  };

  while(true) {
    const auto g_opt = getopt_long(argc, argv, short_opts, long_opts, nullptr);

    if (-1 == g_opt) {
      break;
    }

    switch (g_opt) {
      case 'd':
        opt.debug = true; // Turn on Debug Mode
        break;
      case 'D':
        opt.full_debug = true; // Turn on Debug Mode
        break;
      case 't': // Turn on tabled output
        /* This outputs the lists of tabled sequents
         * used in sequent caching */
        opt.tabled = true;
        break;
      case 'H': // change the Hash Size
        opt.nHash = strtoul(optarg, nullptr, 0);
        if (opt.nHash < 1) {
          std::cerr << "Number of hashing bins must be greater than 0." << std::endl;
          exit(-1);
        }
        if (!is_power_of_two(opt.nHash)) {
          std::cerr << "Number of hashing bins must be a power of 2." << std::endl;
          exit(-1);
        }
        break;
      case 'n':
        opt.useCaching = false;
        break;
      case 'C':
        opt.simple_vacuity = true;
        break;
      case 'V':
        opt.full_vacuity = true;
        break;
      case 'v':
        printVersion();
        exit(1);
      case 'h': // Help: print the Usage.
        printUsage();
        exit(1);
      case '?': // Unrecognised option
        printUsage();
        exit(-1);
    }
  }

  if (argc < 2) {
    std::cerr << "Must have an input file argument." << std::endl;
    printUsage();
    exit(-1);
  }

  for (int i = 0; i < argc; i++) {
    std::cerr << argv[i] << " ";
  }
  std::cerr << std::endl;
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

  prover_options opt;
  parse_command_line(argc, argv, opt);
  if (opt.debug) {
    cpplogging::logger::set_reporting_level(cpplogging::debug);
  }
  if (opt.full_debug) {
    cpplogging::logger::set_reporting_level(cpplogging::debug5);
  }

  /** Filename for the input */
  std::string input_filename(argv[argc - 1]);

  cpplog(cpplogging::info)
      << "\n\n====Begin Program Input==============================" << std::endl;
  /* Get times for lexing and parsing files: */
  time_t rawtime_lp;
  time(&rawtime_lp);
  /* print Starting time */
  cpplog(cpplogging::debug) << "Program start time: " << ctime(&rawtime_lp);

  clock_t begin_lp = clock();

  pes input_pes;
  parse_pes(input_filename, opt.debug, input_pes);

  /* Inputs have now be approved and values set.  Here
   * the Real-Time Model Checking begins */
  /* Start the Model Checking */
  cpplog(cpplogging::info) << "Program input file (timed automaton + MES): "
                           << input_filename << std::endl;
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
    for (Transition* const transition: input_pes.transitions()) {
      cpplog(cpplogging::debug) << *transition << std::endl;
    }
    cpplog(cpplogging::debug) << std::endl;
  }

  /* Call the Model Checker with the given ExprNode
   * to prove or disprove the specification. */
  prover p(input_pes, opt);

  suc = p.do_proof_init(input_pes);

#if DEBUG_PLACEHOLDER_PROVER
  if (opt.debug) {
    cpplogging::logger::set_reporting_level(cpplogging::warning);
  }
  prover pplace(input_pes, opt);
  DBMList placeholder(DBM(input_pes.initial_clock_zone()->clocks_size(), input_pes.clocks()));
  bool tmp = pplace.do_proof_init(input_pes, &placeholder);
  if (suc != tmp)
  {
    cpplog(cpplogging::error) << "Different results from proof with and without placeholder for input " << input_filename << "." << std::endl
                              << "  without placeholder: " << suc << std::endl
                              << "  with placeholder: " << tmp << std::endl
                              << "  the initial clock zone was: " << *input_pes.initial_clock_zone() << std::endl
                              << "  the resulting placeholder is: " << placeholder << std::endl;
  }
  if (opt.debug) {
    cpplogging::logger::set_reporting_level(cpplogging::debug);
  }
  assert(suc == tmp);
#endif

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
