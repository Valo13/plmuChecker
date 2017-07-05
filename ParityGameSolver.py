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


class ParityGame:
    def __init__(self, initNode, pNodes, nNodes):
        self.initNode = initNode
        self.playerNodes = pNodes
        self.natureNodes = nNodes
        # set node ids
        nid = 0
        for s in range(len(self.playerNodes)):
            for f in self.playerNodes[s]:
                self.playerNodes[s][f].nid = nid
                nid += 1
        for nNode in natureNodes:
            nNode.nid = nid
            nid += 1

    def __str__(self):
        out = ""
        for s in range(len(self.playerNodes)):
            for f in self.playerNodes[s]:
                node = self.playerNodes[s][f]
                out += str(node.nid) + ":" + node.owner + ":" + str(node.rank) + ":" + str([n.nid for n in node.successors])\
                       + ":(" + str(s) + ", " + f + ")" + (":INIT" if node is self.initNode else "") + "\n"
        for nNode in self.natureNodes:
            out += str(nNode.nid) + ":NATURE:" + str([{n.nid: p} for n, p in nNode.successors.items()]) + "\n"
        return out

    def toDot(self, formulaName):
        out = "digraph parityGame {\n"
        for s in range(len(self.playerNodes)):
            for f in self.playerNodes[s]:
                node = self.playerNodes[s][f]
                out += "n" + str(node.nid) + "[shape=" + ("box" if node.owner == "ODD" else "diamond") \
                    + ", label=\"" + str(node.rank) + "\\n" + str(s) + "\\n" + f + "\"" + (",style=bold" if node is self.initNode else "") + "]\n"
        for node in self.natureNodes:
            out += "n" + str(node.nid) + "[shape=ellipse]\n"
        for s in range(len(self.playerNodes)):
            for f in self.playerNodes[s]:
                node = self.playerNodes[s][f]
                for succ in node.successors:
                    out += "n" + str(node.nid) + " -> n" + str(succ.nid) + "\n"
        for node in self.natureNodes:
            for succ, p in node.successors.items():
                out += "n" + str(node.nid) + " -> n" + str(succ.nid) + "[label=" + str(p) + "]\n"
        out += "}"
        f = open(os.path.sep.join([os.path.split(model.file)[0],
                        "pg_" + os.path.basename(os.path.splitext(model.file)[0]) + "_" + formulaName + ".dot"]), 'w')
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
        return rank+1


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
                nNode.successors = {playerNodes[state][lambdaFormula(0.0)]: 1-val, playerNodes[state][lambdaFormula(1.0)]: val}
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
                            nsuccessors.update({playerNodes[s][str(subf)]: transition.enddist[s]})
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
    return ParityGame(playerNodes[model.initstate][str(formula)], playerNodes, natureNodes)


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
    return None
