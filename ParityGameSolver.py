# player even = player 1 (winning player)
# player odd = player 2

# reduction still needs to be tested for
# - nested alternating fixpoints
# - single circle parity game


import os
from FormulaReader import *

model = None
printInfo = False


class ParityGameNode:
    def __init__(self, owner, rank, successors=None):
        self.nid = None
        self.owner = owner  # EVEN, ODD or NATURE
        self.rank = rank
        if successors:
            self.successors = successors  # if owner is EVEN or ODD this is a list of nodes, else a dict of nodes:prob
        else:
            self.successors = []
        self.reductionStarted = False
        self.reduction = self
        self.state = None
        self.formula = ""

    def __str__(self):
        if self.owner == "NATURE":
            return str(self.nid) + ":NATURE:" + str([{n.nid: p} for n, p in self.successors.items()])
        else:
            return str(self.nid) + ":" + self.owner + ":" + str(self.rank) + ":" + str([n.nid for n in self.successors]) \
                   + ":(" + str(self.state) + ", " + self.formula + ")"


class ParityGame:
    def __init__(self, initNode, nodes):
        self.initNode = initNode
        self.nodes = nodes

    def __str__(self):
        return "\n".join([str(node) for node in self.nodes])

    def toDot(self, formulaName, suffix=""):
        out = "digraph parityGame {\n"
        for node in self.nodes:
            if node.owner == "NATURE":
                out += "n" + str(node.nid) + "[shape=ellipse " + (",style=bold" if node is self.initNode else "") + "]\n"
            else:
                out += "n" + str(node.nid) + "[shape=" + ("box" if node.owner == "ODD" else "diamond") \
                       + ", label=\"" + str(node.rank) + "\\n" + str(node.state) + "\\n" + node.formula + "\"" \
                       + (",style=bold" if node is self.initNode else "") + "]\n"
        for node in self.nodes:
            if node.owner == "NATURE":
                for succ, p in node.successors.items():
                    out += "n" + str(node.nid) + " -> n" + str(succ.nid) + "[label=" + str(p) + "]\n"
            else:
                for succ in node.successors:
                    out += "n" + str(node.nid) + " -> n" + str(succ.nid) + "\n"
        out += "}"
        f = open(os.path.sep.join([os.path.split(model.file)[0], "pg_" +
                                   os.path.basename(os.path.splitext(model.file)[0])
                                   + "_" + formulaName + suffix + ".dot"]), 'w')
        f.write(out)
        f.close()


fixpointFormulas = {}

# nodes are indexed bij state, str(formula)
playerNodes = []
natureNodes = []


def nextRank(rank, becomesEven):
    if (rank % 2 == 0) == becomesEven:
        return rank
    else:
        return rank + 1


def createParityGameNodes(formula, state, rank, isProbabilistic):
    global playerNodes, natureNodes
    fid = str(formula)
    # check if we already have this node
    if fid not in playerNodes[state]:
        if formula.op.type == "VAL":
            val = formula.op.val
            if val == 0.0:
                playerNodes[state][fid] = ParityGameNode("ODD", nextRank(rank, False))
                playerNodes[state][fid].successors = [playerNodes[state][fid]]
            elif val == 1.0:
                playerNodes[state][fid] = ParityGameNode("EVEN", nextRank(rank, True))
                playerNodes[state][fid].successors = [playerNodes[state][fid]]
            else:
                nNode = ParityGameNode("NATURE", rank)
                createParityGameNodes(lambdaFormula(0.0), state, rank, isProbabilistic)
                createParityGameNodes(lambdaFormula(1.0), state, rank, isProbabilistic)
                nNode.successors = {playerNodes[state][lambdaFormula(0.0)]: 1 - val,
                                    playerNodes[state][lambdaFormula(1.0)]: val}
                natureNodes += [nNode]
        elif formula.op.type == "VAR":
            fixf = fixpointFormulas[formula.op.var]
            playerNodes[state][fid] = ParityGameNode("EVEN", rank)
            createParityGameNodes(fixf, state, rank, isProbabilistic)
            playerNodes[state][fid].successors = [playerNodes[state][str(fixf)]]
        elif formula.op.type in ["AND", "OR"]:
            successors = []
            for subf in formula.subformulas:
                createParityGameNodes(subf, state, rank, isProbabilistic)
                successors += [playerNodes[state][str(subf)]]
            owner = "ODD" if formula.op.type == "AND" else "EVEN"
            playerNodes[state][fid] = ParityGameNode(owner, rank, successors)
        elif formula.op.type in ["DIAMOND", "BOX"]:
            subf = formula.subformulas[0]
            successors = []
            nsuccessors = {}
            owner = "EVEN" if formula.op.type == "DIAMOND" else "ODD"
            transitions = model.outgoing(state, formula.op.action)
            if not transitions:
                playerNodes[state][fid] = ParityGameNode(owner, nextRank(rank, formula.op.type == "BOX"))
                playerNodes[state][fid].successors = [playerNodes[state][fid]]
            else:
                for transition in transitions:
                    for s in transition.enddist:
                        createParityGameNodes(subf, s, rank, isProbabilistic)
                        if isProbabilistic:
                            nsuccessors[playerNodes[s][str(subf)]] = transition.enddist[s]
                        else:
                            successors += playerNodes[s][str(subf)]
                    if isProbabilistic:
                        nNode = ParityGameNode("NATURE", rank, nsuccessors)

                        nsuccessors = {}
                        natureNodes += [nNode]
                        successors += [nNode]

                playerNodes[state][fid] = ParityGameNode(owner, rank, successors)
        elif formula.op.type in ["LEASTFP", "GREATESTFP"]:
            subf = formula.subformulas[0]
            nRank = nextRank(rank, formula.op.type == "GREATESTFP")
            playerNodes[state][fid] = ParityGameNode("EVEN", nRank)
            createParityGameNodes(subf, state, nRank, isProbabilistic)
            playerNodes[state][fid].successors = [playerNodes[state][str(subf)]]


def createParityGame(formula, isProbabilistic=False):
    createParityGameNodes(formula, model.initstate, 0, isProbabilistic)
    allNodes = []
    # set node ids
    nid = 0
    for s in range(len(playerNodes)):
        for f in playerNodes[s]:
            node = playerNodes[s][f]
            node.state = s
            node.formula = f
            node.nid = nid
            allNodes += [node]
            nid += 1
    for nNode in natureNodes:
        nNode.nid = nid
        allNodes += [nNode]
        nid += 1
    return ParityGame(playerNodes[model.initstate][str(formula)], allNodes)


# if node can be removed, it will mark node with the node to reduce to
# also removes successors that will never be picked
def reduceParityGameRec(node):
    if not node.reductionStarted:
        node.reductionStarted = True
        if node.owner == "NATURE":
            for succ in node.successors:
                reduceParityGameRec(succ)

            # if it only has one successor, we set this to be removed
            if len(node.successors) == 1:
                node.reduction = node.successors.keys()[0].reduction
        else:
            for succ in node.successors:
                reduceParityGameRec(succ)

            # now the actual reductions
            # remove successors that will certainly never be chosen
            newSuccessors = []
            for succ in node.successors:
                red = succ.reduction
                # search iteratively to find what the successor will reduce to
                while red is not red.reduction:
                    red = red.reduction
                # remove if current node is even and the successor reduction (red) is a livelock with odd rank
                #   (or current is odd, livelock has even rank)
                if not (red.owner != "NATURE" and len(red.successors) == 1 and red.successors[0] is red
                        and ((node.owner == "EVEN" and red.rank % 2 == 1) or (node.owner == "ODD" and red.rank % 2 == 0))):
                    newSuccessors += [succ]
            if not newSuccessors:
                newSuccessors += [node.successors[0]]
            node.successors = newSuccessors

            # if it only has one successor, we set this node to be removed
            #   change rank to minimum of both if successor is not a livelock
            if len(newSuccessors) == 1:
                newNode = newSuccessors[0]
                newRed = newNode.reduction
                if not (newRed.owner != "NATURE" and len(newRed.successors) == 1 and newRed.successors[0] is newRed):
                    newRed.rank = min(node.rank, newRed.rank)
                node.reduction = newRed


reachedNodes = []


# gathers all nodes that are reachable after reduction
def reachabilitySet(node):
    global reachedNodes
    reducedNode = node.reduction
    # continue searching when it can be further reduced
    if reducedNode.reduction is not reducedNode:
        return reachabilitySet(reducedNode.reduction)
    else:
        if reducedNode not in reachedNodes:
            reachedNodes += [reducedNode]
            if reducedNode.owner == "NATURE":
                newSuccessors = {}
                for succ, p in reducedNode.successors.items():
                    newSuccessors[reachabilitySet(succ)] = p
                reducedNode.successors = newSuccessors
            else:
                for i in range(len(reducedNode.successors)):
                    reducedNode.successors[i] = reachabilitySet(reducedNode.successors[i])
        return reducedNode


def reduceParityGame(parityGame):
    reduceParityGameRec(parityGame.initNode)
    newInit = parityGame.initNode.reduction
    reachabilitySet(newInit)
    return ParityGame(newInit, reachedNodes)


def initParityGameSolver(ts, formula, store, verbose, isProbabilistic):
    global model, printInfo, playerNodes, fixpointFormulas
    model = ts
    printInfo = verbose

    playerNodes = [{} for i in range(ts.numstates)]
    fixpointFormulas = {subf.op.var: subf for subf in formula.getSubFormulas(["LEASTFP", "GREATESTFP"])}

    parityGame = None
    if formula.getSubFormulas(["PRODUCT", "COPRODUCT", "TCOSUM", "TSUM"]):
        print("The operators (co)product and truncated (co)sum are not supported")
    elif isProbabilistic:
        parityGame = createParityGame(formula, True)
    else:
        parityGame = createParityGame(formula)
    if parityGame is not None:
        parityGame.toDot(formula.name)
        reduceParityGame(parityGame).toDot(formula.name, "_red")
    return None
