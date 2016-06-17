#!/Library/Frameworks/Python.framework/Versions/3.5/bin/python3
import itertools
import string
import logging
import optparse

LOG = logging.getLogger()

def concat(xss):
    return itertools.chain.from_iterable(xss)

def nub(xs):
    ys = []
    for x in xs:
        if x not in ys:
            ys.append(x)
    return ys

def boolToInt(b):
    return 1 if b else 0
    
def getState(states, name):
    for s in states:
        if s.name == name:
            return s
    raise Exception("State {0} not found".format(name))

class LabelStore:
    def __init__(self):
        self.__store = []
    
    def __sanitize(self, label):
        if label == None or label.find('[') == -1:
            return label
        else:
            return label[:label.find('[')]
    
    def labels(self):
        return self.__store
            
    def addLabel(self, label):
        if label != None:
            label = self.__sanitize(label)
            if label not in self.__store:
                self.__store.append(label)
    
    def getIndex(self, label):
        assert self.__sanitize(label) in self.__store
        return self.__store.index(self.__sanitize(label))
        
    def __str__(self):
        return str(self.__store)
        
LABELSTORE = LabelStore()

class State:
    def __init__(self, name, invariant=None, initial=False, committed=False):
        self.name = name
        self.invariant = invariant
        self.initial = initial
        self.committed = committed
        
    def __str__(self):
        return "{0}, {1}{2}".format(self.name, self.invariant, ", INIT" if self.initial else "")
        
    def constant(self):
        return "C{0}".format(self.name)
        
    def encoding(self, automaton, dest=False):
        stateClause = "{0} {2} {1}".format(automaton.controlName(), automaton.stateIndex(self), "=" if dest else "==")
        committedClause = "qCommitted {0} {1}".format("=" if dest else "==", boolToInt(self.committed))
        return [stateClause, committedClause]

class Transition:
    def __init__(self, source, dest, guard, label, reset, update = None):
        self.source = source
        self.dest = dest
        self.guard = guard
        self.label = label
        self.reset = reset
        self.update = update
        LABELSTORE.addLabel(label)
        
    
    # Split the guard into a part which is not about clocks, and a part which is.
    def guardIsCondition(self):
        return self.guard in [["len > 0"], ["len == 0"]]
        
    def replaceCondition(self, condition):
        ret = []
        for x in condition:
            x = x.replace("len > 0", "q0 != 0")
            x = x.replace("len == 0", "q0 == 0")
            ret.append(x)
        LOG.debug("Replacing condition {0} with {1}".format(condition, ret))
        return ret
        
    def encoding(self, automaton):
        # Reset extra clock for committed locations
        c = []
        if self.source.committed:
            c.append('x0')
        return (self.source.encoding(automaton),
                self.replaceCondition(self.guard) if self.guardIsCondition() else [],
                [] if self.guardIsCondition() else self.guard,
                self.dest.encoding(automaton,True),
                self.label,
                self.reset,
                self.update)
        
    def __str__(self):
        return "({0}, {1})--{2}-->({3}){4}".format(str(self.source), self.guard, self.label, str(self.dest), self.reset)

class TA:
    def __init__(self, name, states, transitions, clocks):
        self.name = name
        self.states = states
        self.transitions = transitions
        self.clocks = clocks
    
    def __str__(self):
        return '''{0}:
CLOCKS:
{3}
STATES:
{1}
TRANSITIONS:
{2}
'''.format(self.name, self.states, self.transitions, self.clocks)
    
    def controlName(self):
        return "p{0}".format(self.name)
    
    def stateIndex(self, state):
        return self.stateIndexByName(state.name)
        
    def stateIndexByName(self, stateName):
        for idx, val in enumerate(self.states):
            if val.name == stateName:
                return idx
        raise Exception("State not found")
            
    def invariants(self):
        for s in self.states:
            if s.committed:
                yield "{0} == {1} -> {2}".format(self.controlName(), self.stateIndex(s), "x0 <= 0")
            if s.invariant:
                yield "{0} == {1} -> {2}".format(self.controlName(), self.stateIndex(s), s.invariant)
        
    def localTransitions(self):
        for t in self.transitions:
            if not t.label:
                yield t

class Gate(TA):
  def __init__(self):
    states = [
        State("Free", None, True),
        State("Occ"),
        State("Committed", committed=True)
    ]
    transitions = [
        Transition(getState(states, "Free"), getState(states, "Occ"), ["len > 0"], "go[front()]!", []),
        Transition(getState(states, "Free"), getState(states, "Occ"), ["len == 0"], "appr[e]?", [], "enqueue(e)"),
        Transition(getState(states, "Occ"), getState(states, "Committed"), [], "appr[e]?", [], "enqueue(e)"),
        Transition(getState(states, "Occ"), getState(states, "Free"), ["e == front()"], "leave[e]?", [], "dequeue(e)"),
        Transition(getState(states, "Committed"), getState(states, "Occ"), [], "stop[tail()]!", [])
    ]
    super().__init__("Gate", states, transitions, [])
  

class Train(TA):
  def __init__(self, id):
    self.id = id
    states = [
        State("Safe", None, True),
        State("Appr", "x{0} <= 20".format(id)),
        State("Stop"),
        State("Start", "x{0} <= 15".format(id)),
        State("Cross", "x{0} <= 5".format(id))
    ]
    transitions = [
        Transition(getState(states, "Safe"), getState(states, "Appr"), [], "appr[{0}]!".format(id), ["x{0}".format(id)]),
        Transition(getState(states, "Appr"), getState(states, "Cross"), ["x{0} >= 10".format(id)], None, ["x{0}".format(id)]),
        Transition(getState(states, "Appr"), getState(states, "Stop"), ["x{0} <= 10".format(id)], "stop[{0}]?".format(id), []),
        Transition(getState(states, "Stop"), getState(states, "Start"), [], "go[{0}]?".format(id), ["x{0}".format(id)]),
        Transition(getState(states, "Start"), getState(states, "Cross"), ["x{0} >= 7".format(id)], None, ["x{0}".format(id)]),
        Transition(getState(states, "Cross"), getState(states, "Safe"), ["x{0} >= 3".format(id)], "leave[{0}]!".format(id), [])
    ]
    clocks = "x{0}".format(self.id)
    super().__init__("Train{0}".format(id), states, transitions, clocks)

def printTransitionEncoding(encoding):
    LOG.debug("Printing transition encoding {0}".format(encoding))
    (source, condition, guard, dest, label, reset, update) = encoding
    return "({0}{1})->({2}){3};\n".format(
        str.join(' && ', nub(source + condition)),
        ", {0}".format(str.join(' && ', nub(guard))) if guard != [] else "",
        str.join(', ', nub(dest)) + ', qAct = {0}'.format(LABELSTORE.getIndex(label)) if label != None else str.join(', ', nub(dest)),
        "{{{0}}}".format(str.join(", ", reset)) if reset else "")

def areCommunicatingTransitions(t1, t2):
    LOG.debug("Determining whether transitions {0} and {1} communicate ...".format(t1, t2))
    l1 = t1.label
    l2 = t2.label
    if l1 == None or l2 == None:
        return False
    
    # Both transitions have labels.
    name1 = l1[:l1.find('[')]
    name2 = l2[:l2.find('[')]
    io1 = l1[l1.find(']')+1:]
    io2 = l2[l2.find(']')+1:]
    
    ret = name1 == name2 and ((io1 == "?" and io2 == "!") or (io1 == "!" and io2 == "?"))
    LOG.debug("...{0}".format(ret))
    return ret

def encodeCondition(c):
    return list(filter(lambda x: x != None, [c]))

# The result is a pair of conditions and guards, since guards in the implementation can only handle clocks.        
def mergeGuards(aut1, aut2, g1, g2):
    LOG.debug("Merging guards {0} and {1}".format(g1, g2))
    conditions = []
    guards = []
    if g1 == ["e == front()"]:
        LOG.debug("replacing g1 {0}".format(g1))
        g1 = "q0 == {0}".format(aut2.id)
        conditions.append(g1)
    else:
        LOG.debug("g1 remains a guard {0}".format(g1))
        guards += g1
    if g2 == ["e == front()"]:
        LOG.debug("replacing g2 {0}".format(g2))
        g2 = "q0 == {0}".format(aut1.id)
        conditions.append(g2)
    else:
        LOG.debug("g2 remains a guard {0}".format(g2))
        guards += g2
    
    ret = (conditions, guards)
    LOG.debug("merged result: {0}".format(ret))
    return ret

def mergeLabels(nTrains, aut1, aut2, l1, l2):
    ret = []
    if l1.find("front()") != -1:
        ret.append("q0 == {0}".format(aut2.id))
    elif l2.find("front()") != -1:
        ret.append("q0 == {0}".format(aut1.id))
    elif l1.find("tail()") != -1:
        ret.append("q{0} == {1}".format(nTrains-1, aut2.id))
    elif l2.find("tail()") != -1:
        ret.append("q{0} == {1}".format(nTrains-1, aut1.id))
    return ret
    

def mergeCommunicatingTransitions(nTrains, aut1, aut2, t1, t2):
    LOG.debug("merging communicating transitions {0} and {1}".format(t1, t2))
    (source1, condition1, guard1, dest1, label1, reset1, update1) = t1.encoding(aut1)
    (source2, condition2, guard2, dest2, label2, reset2, update2) = t2.encoding(aut2)
    
    sources = source1 + source2 #list(filter(lambda x: x != None,[source1, source2]))
    LOG.debug("  source: {0}".format(sources))
    
    conditions = condition1 + condition2
    LOG.debug("  conditions: {0}".format(conditions))
    
    (extraConds, guards) = mergeGuards(aut1, aut2, guard1, guard2)
    conditions += extraConds
    LOG.debug("  conditions after merging guards: {0}".format(conditions))
    
    dests = dest1 + dest2 #list(filter(lambda x: x != None, [dest1, dest2]))
    LOG.debug("  target states: {0}".format(dests))
    
    # Labels are compatible, so pick 1 here
    label = label1
    LOG.debug("  label: {0}".format(label))
    
    # But also make sure we add the right check, if needed.
    conditions += mergeLabels(nTrains, aut1, aut2, label1, label2)
    
    resets = reset1 + reset2
    LOG.debug("  clocks to reset: {0}".format(resets))
    
    mergedUpdates = mergeUpdates(nTrains, aut1, aut2, update1, update2)
    LOG.debug("  merged updates: {0}".format(mergedUpdates))
    
    ret = []
    if len(mergedUpdates) > 0:
        for update in mergedUpdates:
            LOG.debug("    updating...")
            (condition, dest) = update
            LOG.debug("    sources after merging updates: {0}".format(sources + [condition]))
            LOG.debug("    target states after merging updates: {0}".format(dests + [dest]))
            ret += [(sources + condition,
                conditions,
                guards,
                dests + dest,
                label,
                resets,
                None)]
                
    else:
        ret = [(sources,
            conditions,
            guards,
            dests,
            label,
            resets,
            None)]
    return ret

def mergeUpdates(nTrains, aut1, aut2, update1, update2):
    LOG.info("Merging updates '{0}' and '{1}'".format(update1, update2))
    if update1 == "enqueue(e)":
        assert(update2 == None)
        ret = generateEnqueue(nTrains, aut2.id)
    elif update1 == "dequeue(e)":
        assert(update2 == None)
        ret = generateDequeue(nTrains, aut2.id)
    elif update2 == "enqueue(e)":
        assert(update1 == None)
        ret = generateEnqueue(nTrains, aut1.id)
    elif update2 == "dequeue(e)":
        assert(update1 == None)
        ret = generateDequeue(nTrains, aut1.id)
    else:
        assert(update1 == None and update2 == None)
        ret = []
    LOG.debug("  merged updates into: {0}".format(ret))
    return ret

# We produce additional conditions, and new updates for the queue
def generateEnqueue(nTrains, trainId):
    LOG.debug("Generating code for enqueuing train {0}".format(trainId))
    ret = []
    for i in range(nTrains):
        condition = ["q{0} != 0".format(j) for j in range(i)] + ["q{0} == 0".format(i)]
        update = ["q{0} = {1}".format(i, trainId)]
        ret += [(condition, update)]

    return ret

# Produces all sublists of xs obtained by removing a single element
def allListsOneShorter(xs):
    # invariant xs + [x] + ys = original xs
    ys = []
    while xs != []:
        x = xs.pop()
        yield xs + ys
        ys.insert(0,x)

# All queue like permutations
def queuePermutations(head, xs, tail):
    # First, permute xs
    for perm in itertools.permutations(xs):
        yield ([head] + list(perm) + tail)
    
    
    # Now, we need to remove each element, and permute the smaller list
    # remember that xs = x[:i] ++ x[i:], x[:0] == []
    for ys in allListsOneShorter(xs):
        yield from queuePermutations(head, ys, tail + [0])  
    
def generateDequeue(nTrains, trainId):
    LOG.debug("Generating code for dequeuing train {0}".format(trainId))
    ret = []
    LOG.debug("  Processing all permutations")
    
    head = trainId
    xs = list(filter(lambda x: x != head, [i+1 for i in range(nTrains)]))
    
    for perm in queuePermutations(head, xs, []):
        perm = list(perm)
        LOG.debug("  Permutation {0}".format(perm))
        condition = ["q0 == {0}".format(perm[0])]
        updates = []
        for i in range(1, nTrains):
            condition += ["q{0} == {1}".format(i, perm[i])]
            updates += ["q{0} = {1}".format(i-1, perm[i])]
        updates += ["q{0} = 0".format(nTrains-1)]
        
        LOG.debug("    condition: {0}".format(condition))
        LOG.debug("    updates: {0}".format(updates))
        
        ret += [(condition, updates)]
        LOG.debug("Dequeue codes: {0}".format(ret))    
        
    return ret

def generateProperty(property, gate, trains):
    global LABELSTORE
    if property == "eventualaccess":
        return '''EQUATIONS: {{
1: mu X = {{ pTrain1 == {0} }} || (\\forall time(\AllAct(X)) && \exists time(\ExistAct(Y)))
2: nu Y = \AllAct(Y) 
}}\n'''.format(trains[0].stateIndexByName("Cross"))
    elif property == "canreachcross":
        return '''EQUATIONS: {{
1: mu X = {{ pTrain1 == {0} }} || \exists time(\ExistAct(X))
}}\n'''.format(trains[0].stateIndexByName("Cross"))
    elif property == "canreachstop":
        return '''EQUATIONS: {{
1: mu X = {{ pTrain1 == {0} }} || \exists time(\ExistAct(X))
}}\n'''.format(trains[0].stateIndexByName("Stop"))
    elif property == "canreachstart":
        return '''EQUATIONS: {{
1: mu X = {{ pTrain1 == {0} }} || \exists time(\ExistAct(X))
}}\n'''.format(trains[0].stateIndexByName("Start"))
    elif property == "canreachcommitted":
        return '''EQUATIONS: {{
1: mu X = {{ pGate == {0} }} || \exists time(\ExistAct(X))
}}\n'''.format(gate.stateIndexByName("Committed"))
    elif property == "mutex":
         return '''EQUATIONS: {{
 1: nu X = \\forall time(\AllAct(X)) && \\forall time(\AllAct(qAct != {0} || Y))
 2: nu Y = \\forall time(\AllAct(qAct == {1} || Y)) && \\forall time(\AllAct(qAct != {0}))
 }}\n'''.format(LABELSTORE.getIndex('go'), LABELSTORE.getIndex('leave'))
    elif property == "mutexstate":
        LOG.debug(" ------ ")
        LOG.debug("Generating state-based mutex formula")
        clauses = []
        for train in trains:
            guard = "{0} != {1}".format(train.controlName(), train.stateIndexByName("Cross"))
            LOG.debug("  allowing {0} in Cross using guard {0}".format(guard))
            conjuncts = []
            for train1 in trains:
                LOG.debug("  considering {0}".format(train1.name))
                if train != train1:
                    conjunct = "{0} != {1}".format(train1.controlName(), train.stateIndexByName("Cross"))
                    LOG.debug("  disallowing this train using clause {0}".format(conjunct))
                    conjuncts += [conjunct]
                    
            clauses += ["({0} || ({1}))".format(guard, str.join(" && ", conjuncts))]                   
                    
        return '''EQUATIONS: {{
1: nu X = \\forall time(\AllAct(X)) && {0}
}}\n'''.format(str.join(" && ", clauses))
    elif property == "nodeadlock":
        return '''EQUATIONS: {
1: nu X = \\forall time(\AllAct(X)) && \\forall time(\ExistAct(TRUE))
}\n'''
    else:
        raise Exception("Unknown property {0}".format(property))
    
def generateTrainGate(nTrains, outputFile, property):
    LOG.info("Generating train/gate for {0} trains".format(nTrains))
    
    outfile = open(outputFile, 'w')
    
    gate = Gate()
    trains = [Train(id) for id in range(1,nTrains+1)]
    
    LOG.info("Generating defines for state names of the gate")
    # Defines for state names
    outfile.write("//defines for state names of the gate\n")
    for s in gate.states:
        outfile.write("#define {0} {1}\n".format(s.constant(), gate.stateIndex(s)))
        
    LOG.info("Generating defines for state names of the gate")
    outfile.write("//defines for state names of the trains\n")
    for s in trains[0].states:
        outfile.write("#define {0} {1}\n".format(s.constant(), trains[0].stateIndex(s)))
        
    LOG.info("Generating defines for the trains")
    outfile.write("//defines for trains\n")
    for val in trains:
        outfile.write("#define C{0} {1}\n".format(val.name,val.id))
        
    LOG.info("Generating defines for the actions")
    outfile.write("//defines for actions\n")
    for label in LABELSTORE.labels():
        outfile.write("#define C{0} {1}\n".format(label,LABELSTORE.getIndex(label)))
    
    LOG.info("Generating clocks")
    clocks = gate.clocks + list(map(lambda x: x.clocks, trains)) + ["x0"]
    outfile.write("CLOCKS: {{ {0} }}\n".format(str.join(", ", clocks)))
    
    LOG.info("Generating contol variables")
    names = [gate.controlName()] + list(map(lambda x: x.controlName(), trains))
    queue = ["q{0}".format(i) for i in range(nTrains)]
    act = ["qAct", "qCommitted"]
    outfile.write("CONTROL: {{ {0} }}\n".format(str.join(", ", names + queue + act)))
    
    LOG.info("Generating MES")
    outfile.write("PREDICATE: { X,Y }\n")
    
    outfile.write("START: X\n")
    
    outfile.write(generateProperty(property, gate, trains))
    
    LOG.info("Generating invariants")
    invariants = list(gate.invariants()) + list(concat(map(lambda x: x.invariants(), trains)))
    outfile.write('''INVARIANT:
  {0}\n'''.format(str.join('\n  ', invariants)))
    
    LOG.info("Generating transitions")
    outfile.write("TRANSITIONS:")
    LOG.info("Generating local transitions for the trains")
    for train in trains:
        outfile.write("// {0}\n".format(train.name))
        for t in train.localTransitions():
            print(t.encoding(train))
            outfile.write(printTransitionEncoding(t.encoding(train)))
    
    LOG.info("Generating communicating transitions")    
    # Communicating transitions
    for train in trains:
        outfile.write("// {0} and {1}\n".format(train.name, gate.name))
        for ttrain in train.transitions:
            for tgate in gate.transitions:
                if areCommunicatingTransitions(ttrain, tgate):
                    merged = mergeCommunicatingTransitions(nTrains, train, gate, ttrain, tgate) 
                    for t in merged:    
                      outfile.write(printTransitionEncoding(t))
                    

def runCmdLine():
    """
    Parse the command line, and run the experiments.
    """
    parser = optparse.OptionParser(usage='usage: %prog [options] [outfile]')
    parser.add_option('-v', action='count', dest='verbosity',
                      help='Be more verbose. Use more than once to increase verbosity even more.')
    parser.add_option('-n', action='store', type='int', dest='ntrains', default=2,
                      help='Generate system for given number of trains')
    parser.add_option('-p', action='store', type='string', dest='property', default='eventualaccess',
                      help='Generate MES for given property; choose one of eventualaccess (default), canreachcross, canreachstop, canreachstart, canreachcommitted, mutex, mutexstate, nodeadlock')
    options, args = parser.parse_args()
    if not args:
        args = (None,)

    outputFile = args[0]

    logging.basicConfig()
    
    if options.verbosity:
        if options.verbosity > 0:
            logging.getLogger().setLevel(logging.INFO)
        if options.verbosity > 1:
            logging.getLogger().setLevel(logging.DEBUG)

    generateTrainGate(options.ntrains, outputFile, options.property)

if __name__ == "__main__":
    runCmdLine()
    


     
    
    