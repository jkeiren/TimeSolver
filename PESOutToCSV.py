#!/usr/bin/env python3
""" Basic Script to convert output of PES tool for multiple files to a .csv """
import sys
import re

def PESToCSV(infile, outfile):
  """ Takes the file of PES outputs on programs and converts it to a CSV for experimental data analysis.  """
  # consider with open() as : statements
  fileIn = open(infile,'r')
  fileOut = open(outfile, 'w')
  
  # Write headers to output file, separated by commas.
  writeLine = "file,output,parseTime,proofTime,totalTime\n"
  fileOut.write(writeLine)
  fileName = ''
  checkValid = False
  parseTime = ''
  proofTime = ''
  totalTime = ''
  line = fileIn.readline()
  while(line != ''):
    # Remove = and - headers for human formatting
    line = line.strip()
    line = line.strip('=')
    if(line.find("Begin Program Input") != -1):
      # Read lines specific to the program output of this PES Tool:
      # Program input file 2 lines after this (lines include blank lines)
      line = fileIn.readline()
      line = fileIn.readline()
      line = line.strip()
      fileName = line.split('/')[-1]
      # Program Result 3 lines after that
      line = fileIn.readline()
      line = fileIn.readline()
      line = fileIn.readline()
      line = line.strip()
      line = line.strip('=- ')
      line = line.strip('-=')
      if(line.find("Invalid") != -1):
        checkValid = False
      else:
        checkValid = True
      # Program Parse time 4 lines after that
      line = fileIn.readline()
      line = fileIn.readline()
      line = fileIn.readline()
      line = fileIn.readline()
      line = line.strip()
      parseTime = (re.search('(\d+.\d+)|(\d+)', line)).group(0)
      # Next line is program proof time
      line = fileIn.readline()
      line = line.strip()
      proofTime = (re.search('(\d+.\d+)|(\d+)', line)).group(0)
      # Following line is Combined running time
      line = fileIn.readline()
      line = line.strip()
      totalTime = (re.search('(\d+.\d+)|(\d+)', line)).group(0)
      # The next line has "End of Program Execution."
    elif(line.find("End of Program Execution") != -1):
      # Since the program has just ended, use this to parse lines
      # specific to the profiler, such as the "time" command
      # When done, write to file
      validStr = "invalid"
      if(checkValid):
        validStr = "valid"
      writeLine = fileName + ',' + validStr + ',' + parseTime + ',' + proofTime + ',' + totalTime + '\n'
      fileOut.write(writeLine)
    line = fileIn.readline()
    
    
  fileIn.close()
  fileOut.close()
# end of function


if (len(sys.argv) < 3):
  print("Error. Please provide an input filename and an output filename.\n")
  sys.exit(1)

PESToCSV(sys.argv[1], sys.argv[2])
sys.exit(0)