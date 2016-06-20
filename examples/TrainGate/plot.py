import optparse
import yaml

import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt


# Example of the data
# - nlocations: 2
#   ntrains: 6
#   parsing: 0.057099
#   property: canreachocc
#   proving: 0.0001
#   result: Valid
#   total: 0.061387
# - nlocations: 978
#   ntrains: 6
#   parsing: 0.0621
#   property: canreachcross1
#   proving: 2.73974
#   result: Valid
#   total: 2.80658

def run(infile, outfile, property):
    data = yaml.load(open(infile, 'r').read())
    
    xs = []
    ystotal = []
    ysparsing = []
    ysproving = []
    for d in data:
        if d['property'] == property:
            xs.append(d['ntrains'])
            ystotal.append(d['total'])
            ysparsing.append(d['parsing'])
            ysproving.append(d['proving'])
            
    plt.plot(xs, ystotal, 'ro', label='total', ls='-')
    plt.plot(xs, ysparsing, 'bo', label='parsing', ls='-')
    plt.plot(xs, ysproving, 'go', label='proving', ls='-')
    plt.ylabel('time (s) (logarithmic)')
    plt.xlabel('# Trains')
    plt.xticks(xs)
    plt.yscale('log')
    plt.title(property)
    plt.legend(loc='upper left')
    plt.show()
    plt.savefig(outfile)
    

def runCmdLine():
    parser = optparse.OptionParser(usage='usage: %prog [options] infile outfile')
    parser.add_option('-p', action='store', type='string', dest='property', default='mutexstate',
                          help='Generate plot for given propertyt')
    options, args = parser.parse_args()
    
    if not args:
        raise Exception("Please provide an inputfile")
    
    run(args[0], args[1], options.property)
    
if __name__ == "__main__":
    runCmdLine()
