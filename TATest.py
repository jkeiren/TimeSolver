#!/usr/bin/env python3
"""Script to perform end-to-end tests on the examples"""

import difflib
import io
import gzip
import os
import re
import subprocess
import sys

# These paths are relative to the directory in which this script is stored.
# We make sure we are in the appropriate directory in the __main__ at the
# bottom of this file.
EXECUTABLE = "pes.timed/timesolver-ta"
TEST_SUITE_DIR = "examples/CorrectnessTestSuite"

def filterTimes(lines):
    """Filter times from the output. This data is variable, so should not be
       taken into account in the comparison."""
    
    invalid = re.compile(r"(running|Program|start|end) (t|T)(ime)|demo|timesolver")
    return list(filter(lambda x: invalid.search(x) == None, lines))

def compare(expectedFileName, given):
    """Compare the output in the file with name expectedFileName to the
    string given"""
    
    with gzip.open(expectedFileName, 'rt') as f:
        expectedFile = filterTimes(f.readlines())
        givenLines = filterTimes(given.splitlines(keepends = True))
        
        result = expectedFile == givenLines
        if(not result):
            sys.stdout.write("[!!!] Output has changed for {0}\n".format(expectedFileName))
            sys.stdout.write("[!!!] Diff follows")
            d = difflib.Differ()
            diff = d.compare(expectedFile, givenLines)
            sys.stdout.writelines(diff)
        return result

def runTestCase(dirName, fileName, overwrite = False):
    """Run the tool 'demo' on the testcase dirName/fileName. If overwrite is
    True, the expected output is overwritten. If overwrite is False, the output
    is compared to the file in which the expected output is stored."""
    try:
        ret = subprocess.run([EXECUTABLE, "-d", os.path.join(dirName,fileName)], stdout=subprocess.PIPE, stderr=subprocess.PIPE, universal_newlines = True, check=True)
        resultFile = fileName + ".expectedout.gz"

        if overwrite:
            with gzip.open(os.path.join(dirName,resultFile), 'wt') as f:
              f.write(ret.stdout)
            result = True
            print('[{0}] {1}/{2}'.format('\033[33mGENERATE\033[39m', dirName, resultFile))
        else:
            result = compare(os.path.join(dirName,resultFile), ret.stdout)
            print('[{0}] {1}/{2}'.format('\033[32mOK\033[39m' if result else '\033[31mFAILED\033[39m', dirName, fileName))
    except subprocess.CalledProcessError as e:
        print('[{0}] {1}/{2}'.format('\033[31mFAILED\033[39m', dirName, fileName))
        print('Standard error: {0}'.format(e.stderr))
        result = False
        
    return result
  
def traverseTestCases(rootDir, overwrite = False):
    """Run all test cases below rootDir. If overwrite is True, then we only use
    the current version of the executable to generate the expected output."""
    count = 0
    failed = 0
    for dirName, subdirList, fileList in os.walk(rootDir):
        for fname in fileList:
            # Skip expected output files
            if os.path.splitext(fname)[1] == ".gz" or fname[0] == '.':
                continue
            count += 1
            res = runTestCase(dirName, fname, overwrite)
            if(not res):
                failed += 1
    print("{0} tests were run".format(count))
    print("{0} tests failed".format(failed))
            
if __name__ == "__main__":
    curdir = os.getcwd()
    script_dir = os.path.dirname(os.path.realpath(__file__))
    os.chdir(script_dir)
    print('Running all test cases in {0}'.format(TEST_SUITE_DIR))
    traverseTestCases(TEST_SUITE_DIR, False)
    os.chdir(curdir)

