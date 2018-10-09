/** \file parse.cc
 * Main functions for parsing PESs from input file. See also the flex/bison parser generators.
 * @author Peter Fontana
 * @author Dezhuang Zhang
 * @author Rance Cleaveland
 * @author Jeroen Keiren
 * @copyright MIT Licence, see the accompanying LICENCE.txt
 */

#include "parse.hh"
#include "pes.tab.hh"
#include "pes.lex.hh"

/** The method that parses the lexed file
 * and creates the ExprNode objects.
 * @return 0 if successful, 1 if syntax error,
 * and 2 if out of memory error (usually).
 * @see pes.y pes.tab.h and pes.tab.c (parser files). */
extern int yyparse(void* scanner, bool debug, pes& input_pes);

/** Prints out an error if it occurs during the parsing process.
 * This method is only used in the parser.
 * @param s (*) The error string to print out.
 * @return None */
void yyerror(yyscan_t scanner, bool /*debug*/, pes&, char* s) {
  std::cerr << "Error at symbol \"" << yyget_text(scanner)
            << "\" on line " << yyget_lineno(scanner) << ": ";
  if (s == nullptr) {
    std::cerr << "syntax error";
  } else {
    std::cerr << s;
}
  std::cerr << std::endl;
}

void parse_pes(const std::string& input_filename, bool debug, pes& result) {
  /* Read and lex the input file to tokens for the parser to use. */
  FILE* input_file = fopen(input_filename.c_str(), "r");
  if (input_file == nullptr) {
    throw std::runtime_error("Cannot open input file " + input_filename);
  }

  /* Parses the Example File (and produces the ExprNode structure.)
   * Returns 0 if successful, 1 for Syntax Error, and 2 for out of Memory
   * (usually). */
  yyscan_t scanner;
  yylex_init(&scanner);
  yyset_in(input_file, scanner);

  YY_BUFFER_STATE buf = yy_create_buffer(yyget_in(scanner), YY_BUF_SIZE, scanner);
  yy_switch_to_buffer(buf, scanner);
  yyset_lineno(1, scanner);

  int parseError = yyparse(scanner, debug, result);

  yylex_destroy(scanner);
  // Close File for good file handling
  fclose(input_file);

  if (parseError != 0) {
    throw std::runtime_error("\n**Syntax Error: Error Parsing file.**\n\n"
                             "==--End of Program Execution-----------------------==\n");
  }

}

void parse_pes_from_string(const std::string& input_string, bool debug, pes& result)
{
  yyscan_t scanner;
  yylex_init(&scanner);

  YY_BUFFER_STATE buf = yy_scan_string(input_string.c_str(), scanner);
  yyset_lineno(1, scanner);

  int parseError = yyparse(scanner, debug, result);

  yy_delete_buffer(buf, scanner);
  yylex_destroy(scanner);

  if (parseError != 0) {
    throw std::runtime_error("\n**Syntax Error: Error Parsing file.**\n\n"
                             "==--End of Program Execution-----------------------==\n");
  }
}
