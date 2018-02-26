#!/usr/bin/env python3
"""Script to perform end-to-end tests on the examples"""

import difflib
import gzip
import optparse
import os
import re
import subprocess
import sys

# These paths are relative to the directory in which this script is stored.
# We make sure we are in the appropriate directory in the __main__ at the
# bottom of this file.
EXECUTABLE = os.path.join("pes.timed", "timesolver-ta")

def filterTimes(lines):
    """Filter times from the output. This data is variable, so should not be
       taken into account in the comparison."""
    invalid = re.compile(r"(running|Program|start|end) (t|T)(ime)|demo|timesolver")
    return list(filter(lambda x: invalid.search(x) is None, lines))


def compare(expectedFileName, given, printDiff = False):
    """Compare the output in the file with name expectedFileName to the
    string given"""
    try:
        with gzip.open(expectedFileName, 'rt') as f:
            expectedFile = filterTimes(f.readlines())
            givenLines = filterTimes(given.splitlines(keepends=True))

            result = expectedFile == givenLines
            if(printDiff and not result):
                sys.stdout.write("[!!!] Output has changed for {0}\n".format(expectedFileName))
                sys.stdout.write("[!!!] Diff follows")
                d = difflib.Differ()
                diff = d.compare(expectedFile, givenLines)
                sys.stdout.writelines(diff)
            return result
    except:
        sys.stdout.write("[!!!] Failed to compare with existing file {0}\n".format(expectedFileName))
        return False


def runTestCase(fileName, overwrite, printdiff, debug, diff):
    """Run the tool 'demo' on the testcase dirName/fileName. If overwrite is
    True, the expected output is overwritten. If overwrite is False, the output
    is compared to the file in which the expected output is stored."""
    global EXECUTABLE
    try:
        if debug:
            cmd = [EXECUTABLE, "-d", fileName]
        else:
            cmd = [EXECUTABLE, fileName]

        print (cmd)
        ret = subprocess.run(cmd, stdout=subprocess.PIPE,
                             stderr=subprocess.PIPE,
                             universal_newlines=True, check=True)
        
        resultPath = fileName + ".expectedout.gz"

        # Check whether the file exists. If it exists, compare the result, and
        # do not overwrite if the content is the same
        if diff:
            if overwrite:
                result = None
                if os.path.exists(resultPath):
                    result = compare(resultPath, ret.stderr)

                if result:
                    print('[{0}] {1}'.format('\033[32mKEEP\033[39m',
                          resultPath))
                else:
                    with gzip.open(resultPath, 'wt') as f:
                        f.write(ret.stderr)
                        print('[{0}] {1}}'.format(
                              '\033[33mGENERATE\033[39m', resultPath))
            else:
                result = compare(resultPath, ret.stderr,
                                 printdiff)
                print('[{0}] {1}'.format('\033[32mOK\033[39m' if result
                      else '\033[31mFAILED\033[39m', fileName))
        else:
            print('[{0}] {1}'.format('\033[32mRUN\033[39m',  resultPath))
            result = True
    except subprocess.CalledProcessError as e:
        print('[{0}] {1}'.format('\033[31mFAILED\033[39m', resultPath))
        print('Standard out: {0}'.format(e.stdout))
        print('Standard error: {0}'.format(e.stderr))
        result = False

    return result


def main():
    """
    Parse the command line, and run the experiments.
    """
    parser = optparse.OptionParser(usage='usage: %prog [options]')
    parser.add_option('-o', action='store_true', dest='overwrite',
                      help='Overwrite expected outputs')
    parser.add_option('-d', action='store_true', dest='printdiff',
                      help='Print diff in case of failed test')
    parser.add_option('--nodebug', action='store_true', dest='nodebug', default=False,
                      help='Call timesolver without the debug flag')
    parser.add_option('--nodiff', action='store_true', dest='nodiff', default=False,
                      help='Do not compute the diff of the result')

    options, args = parser.parse_args()

    curdir = os.getcwd()
    script_dir = os.path.dirname(os.path.realpath(__file__))
    os.chdir(script_dir)

    global EXECUTABLE
    EXECUTABLE = args[0]
    filename = args[1]
    
    return runTestCase(filename, options.overwrite, options.printdiff, not options.nodebug, not options.nodiff)

if __name__ == "__main__":
    result = main()
    if result == 0:
        sys.exit(0)
    else:
        sys.exit(1)
