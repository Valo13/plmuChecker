# player even = player 1 (winning player)
# player odd = player 2


class ParityGameNode:
    def __init__(self, owner, rank, successors=None):
        self.nid = None
        self.owner = owner
        self.rank = rank
        if successors:
            self.successors = successors
        else:
            self.successors = []


class ParityGame:
    def __init__(self, initNode, gameNodes):
        self.initNode = initNode
        self.nodes = gameNodes
        # set node ids
        nid = 0
        for s in range(len(self.nodes)):
            for f in self.nodes[s]:
                self.nodes[s][f].nid = nid
                nid += 1

    def __str__(self):
        out = ""
        for s in range(len(self.nodes)):
            for f in self.nodes[s]:
                node = self.nodes[s][f]
                out += str(node.nid) + ":(" + str(s) + ", " + f + "):" + node.owner + ":" + node.rank + ":"\
                       + str([n.id for n in node.successors]) + (":INIT" if node is self.initNode else "") + "\n"

model = None
printInfo = False

fixpointFormulas = {}

# nodes are indexed bij state, str(formula)
nodes = []
id = 0


def nextRank(rank, becomesEven):
    if (rank % 2 == 0) == becomesEven:
        return rank
    else:
        return rank+1


def createParityGameNodes(formula, state, rank):
    fid = str(formula)
    # check if we already have this node
    if str(formula) not in nodes[state]:
        if formula.op.type == "VAL":
            if formula.op.val == 0:
                nodes[state][fid] = ParityGameNode("ODD", nextRank(rank, False))
            elif formula.op.val == 1:
                nodes[state][fid] = ParityGameNode("EVEN", nextRank(rank, True))
            nodes[state][fid].successors = [nodes[state][fid]]
        elif formula.op.type == "VAR":
            fixf = fixpointFormulas[formula.op.var]
            createParityGameNodes(fixf, state, rank)
            nodes[state][fid] = ParityGameNode("EVEN", rank, [nodes[state][str(fixf)]])
        elif formula.op.type in ["AND", "OR", "PRODUCT", "COPRODUCT", "TCOSUM", "TSUM"]:
            successors = []
            for subf in formula.subformulas:
                createParityGameNodes(subf, state, rank)
                successors += nodes[state][str(subf)]
            owner = "ODD" if formula.op.type in ["AND", "PRODUCT", "TCOSUM"] else "EVEN"
            nodes[state][fid] = ParityGameNode(owner, rank, successors)
        elif formula.op.type in ["DIAMOND", "BOX"]:
            subf = formula.subformulas[0]
            successors = []
            for s in model.outgoing(state, formula.op.action):
                createParityGameNodes(subf, s, rank)
                successors += nodes[state][str(subf)]
            owner = "EVEN" if formula.op.type == "DIAMOND" else "ODD"
            nodes[state][fid] = ParityGameNode(owner, rank, successors)
        elif formula.op.type in ["LEASTFP", "GREATESTFP"]:
            subf = formula.subformulas[0]
            nRank = nextRank(rank, formula.op.sign == "nu")
            createParityGameNodes(subf, state, nRank)
            nodes[state][fid] = ParityGameNode("EVEN", nRank, [nodes[state][str(subf)]])


def createParityGame(formula):
    createParityGameNodes(formula, model.initState, 0)
    return ParityGame(nodes[model.initState][str(formula)], nodes)


def initParityGameSolver(ts, formula, store, verbose, isProbabilistic):
    global model, printInfo, nodes, fixpointFormulas
    model = ts
    printInfo = verbose

    nodes = [{} for i in range(ts.numstates)]
    fixpointFormulas = {subf.op.var: subf for subf in formula.getSubFormulas(["LEASTFP", "GREATESTFP"])}

    if isProbabilistic:
        print("2 and a half player parity games not yet supported")
    else:
        parityGame = createParityGame(formula)
        print(str(parityGame))
    return None
