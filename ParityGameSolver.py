# player even = player 1 (winning player)
# player odd = player 2

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
                out += "n" + str(node.nid) + "[shape=ellipse]\n"
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


def reduceParityGameRec(node):
    if node.reductionStarted:
        return node
    else:
        node.reductionStarted = True
    if node.owner == "NATURE":
        newSuccessors = {}
        for succ, p in node.successors.items():
            newSucc = reduceParityGameRec(succ)
            newSuccessors[newSucc] = p
        node.successors = newSuccessors

        # if it only has one successor, simply return the successor instead
        if len(node.successors) == 1:
            return node.successors.keys()[0]
        else:
            return node
    else:
        for i in range(len(node.successors)):
            node.successors[i] = reduceParityGameRec(node.successors[i])

        # now the actual reductions
        # remove successors that will certainly never be chosen (odd prio loop when even and dual)
        newSuccessors = []
        for succ in node.successors:
            if not (succ.owner != "NATURE" and len(succ.successors) == 1 and succ.successors[0] is succ
                    and ((node.owner == "EVEN" and succ.rank % 2 == 1) or (node.owner == "ODD" and succ.rank % 2 == 0))):
                newSuccessors += [succ]
        if not newSuccessors:
            newSuccessors += [node.successors[0]]

        # if it only has one successor, return that successor instead
        #   change rank to minimum of both if successor is not a livelock
        if len(newSuccessors) == 1:
            newNode = newSuccessors[0]
            if not (newNode.owner != "NATURE" and len(newNode.successors) == 1 and newNode.successors[0] is newNode):
                newNode.rank = min(node.rank, newNode.rank)
            return newNode
        else:
            node.successors = newSuccessors
            return node


def reachabilitySet(node, reachedNodes):
    reachedNodes += [node]
    for succ in node.successors:
        if succ not in reachedNodes:
            reachedNodes = reachabilitySet(succ, reachedNodes)
    return reachedNodes


def reduceParityGame(parityGame):
    return ParityGame(parityGame.initNode, reachabilitySet(reduceParityGameRec(parityGame.initNode), []))


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
        print(str(parityGame))
        parityGame.toDot(formula.name)
        reduceParityGame(parityGame).toDot(formula.name, "_red")
    return None
