import TrainGateGen
import optparse
import subprocess
import re
import yaml

CWBRT = '../../pes.timed/demo'
RE_RESULT = 'Program Result:\s*\*\*(?P<result>\w+)\*\*'
RE_TIMES = '''Lexer and parser running time: (?P<parsing>[0-9.e-]+) seconds
Prover running time: (?P<proving>[0-9.e-]+) seconds
Combined running time: (?P<total>[0-9.e-]+) seconds
Number of locations: (?P<locations>\d+)
'''

N=6
PROPERTIES = ["canreachocc", "canreachcross1", "canreachcross2", "canreachcross1stop2", "canreachcross1stopothers", "mutex", "mutexstate", "nodeadlock", "train1apprthencross"]

RESULTS = []

def runInstance(n, prop):
    # Generate file
    outputfile = 'Train{0}.{1}.in'.format(n, prop)
    TrainGateGen.generateTrainGate(n, outputfile, prop)
    
    # Run the tool
    p = subprocess.Popen([CWBRT, outputfile], stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    out, err = p.communicate()
    out = str(out, 'utf-8')
    
    if p.returncode != 0:
        print("Executing subprocess failed")
        print(out)
        print(err)
    
    else:    
        mresult = re.search(RE_RESULT, out, re.DOTALL)
        mtimes = re.search(RE_TIMES, out, re.DOTALL)
    
        result = {'ntrains': n,
                  'property': prop,
                  'parsing': float(mtimes.group('parsing')),
                  'proving': float(mtimes.group('proving')),
                  'total': float(mtimes.group('total')),
                  'nlocations': int(mtimes.group('locations')),
                  'result': mresult.group('result')}

        print(yaml.dump(result, default_flow_style=False))
        RESULTS.append(result)
    
def runTrain(n):
    for prop in PROPERTIES:
        runInstance(n, prop)

def run(out):
    for i in range(2,N):
        runTrain(i)
    
    if out:
        outfile = open(out, 'w')    
        outfile.write(yaml.dump(RESULTS, default_flow_style=False))
        outfile.close()
    else:
        print("Complete output")
        print(yaml.dump(RESULTS, default_flow_style=False))

def runCmdLine():
    parser = optparse.OptionParser(usage='usage: %prog [options] [outfile]')
    options, args = parser.parse_args()
    if not args:
        args = (None,)
    run(args[0])

if __name__ == "__main__":
    runCmdLine()