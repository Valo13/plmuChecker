import os

# format:

# des (<initial state>, <#states>, <#transitions>)
# for each transition:
#   (<start state>, "<action>", <end state> {<probability> <end state>})

# <#states> and <#transitions> not mandatory
# a state is represented by a natural number in the interval [0, #numstates-1]
# a probability is represented by a positive rational number: nat/nat


class Transition:
    def __init__(self, startstate, action, enddist):
        self.startstate = startstate
        self.action = action
        self.enddist = enddist

    def __repr__(self):
        return '(' + str(self.startstate) + ', "' + self.action + '", ' + ' '.join(str(k) + ':' + str(v) for k, v in self.enddist.items()) + ')'


class TransitionSystem:
    def __init__(self, file, initData, transitions, isProbabilistic):
        self.file = file
        self.name = os.path.splitext(os.path.basename(file))[0]
        self.initstate = int(initData[0])
        self.isProbabilistic = isProbabilistic
        if len(initData) > 1:
            self.numstates = int(initData[1])
        else:
            states = set()
            for t in transitions:
                if t.startstate not in states:
                    states.add(t.startstate)
                for s in t.enddist:
                    if s not in states:
                        states.add(s)
            self.numstates = len(states)
        if len(initData) > 2:
            self.numtransitions = int(initData[2])
        else:
            self.numtransitions = len(transitions)

        # index the transitions on start state for easy access
        self.transitions = [[] for i in range(0, self.numstates)]
        for t in transitions:
            self.transitions[t.startstate] += [t]

    def outgoing(self, state, action):
        return [t for t in self.transitions[state] if t.action == action]

    def __repr__(self):
        return 'des (' + str(self.initstate) + ', ' + str(self.numtransitions) + ', ' + str(self.numstates) + ')\n' + '\n'.join(str(t) for s in self.transitions for t in s)


def extractDist(distData):
    prob = 1.0
    dist = {}
    for i in range(len(distData)/2):
        pValue = distData[2*i+1]
        slash = pValue.find('/')
        p = float(pValue[:slash]) / float(pValue[slash+1:])
        dist[int(distData[2*i])] = p
        prob -= p

    dist[int(distData[-1])] = prob
    return dist


def readTS(filename):
    try:
        f = open(filename)
        lines = f.read().split('\n')
        f.close()
    except IOError:
        print("File '" + filename + "' not found")
        return -1

    try:
        isProbabilistic = False
        initData = lines[0][lines[0].find('(') + 1:lines[0].rfind(')')].split(',')

        transitionsData = lines[1:]
        transitions = []
        for t in transitionsData:
            if t.startswith('('):
                tData = t[t.find('(') + 1:t.rfind(')')].split(',')
                distData = tData[2].strip().split(' ')
                if len(distData) > 1:
                    isProbabilistic = True
                transitions += [Transition(int(tData[0]), tData[1].strip()[1:-1], extractDist(distData))]

        return TransitionSystem(filename, initData, transitions, isProbabilistic)
    except (IndexError, ValueError):
        print("Supplied model is incorrectly specified. For syntax, see TSReader.py")
        return -1
