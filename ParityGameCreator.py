# player even = player 1 (winning player)
# player odd = player 2

# reduction still needs to be tested for
# - nested alternating fixpoints
# - single circle parity game


import os
from FormulaReader import *
from RealFormula import *
from RESSolver import toDisConjunctiveForm, createRES

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
        self.state = None  # in case created from res, this contains the variable
        self.formula = ""

    def __str__(self):
        return str(self.nid) + ":" + self.owner + (":" + str(self.rank) if self.owner != "NATURE" else "") + ":"\
               + (str([{n.nid: p} for n, p in self.successors.items()]) if self.owner == "NATURE" else str([n.nid for n in self.successors])) \
               + ":(" + str(self.state) + ", " + self.formula + ")"


class ParityGame:
    def __init__(self, initNode, nodes, giveIds=True):
        self.initNode = initNode
        self.nodes = nodes

        # add ids
        if giveIds:
            nid = 0
            for node in nodes:
                node.nid = nid
                nid += 1

    def __str__(self):
        return "INIT:" + str(self.initNode.nid) + "\n" + "\n".join([str(node) for node in self.nodes])

    def toDot(self, formulaName, suffix="", addNodeLabel=True):
        out = "digraph parityGame {\n"
        for node in self.nodes:
            if node.owner == "NATURE":
                out += "n" + str(node.nid) + "[shape=ellipse " + (",style=bold" if node is self.initNode else "") + "]\n"
            else:
                out += "n" + str(node.nid) + "[shape=" + ("box" if node.owner == "ODD" else "diamond") \
                       + ", label=\"" + str(node.rank) + ("\\n" + str(node.state) + "\\n" + node.formula if addNodeLabel else "") + "\"" \
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


def nextRank(rank, becomesEven):
    if (rank % 2 == 0) == becomesEven:
        return rank
    else:
        return rank + 1


# player nodes are indexed bij state, str(formula)
playerNodes = {}
natureNodes = []
fixpointFormulas = {}


def createParityGameNodes(state, formula, rank, isProbabilistic):
    global playerNodes, natureNodes
    fid = str(formula)
    # check if we already have this node
    if fid not in playerNodes[state]:
        if formula.op.type == "VAL":
            val = formula.op.val
            # 0.0 nodes are for ODD, 1.0 nodes for EVEN (not that it matters, but it is a node they will certainly win)
            if val == 0.0:
                playerNodes[state][fid] = ParityGameNode("ODD", nextRank(rank, False))
                playerNodes[state][fid].successors = [playerNodes[state][fid]]
            elif val == 1.0:
                playerNodes[state][fid] = ParityGameNode("EVEN", nextRank(rank, True))
                playerNodes[state][fid].successors = [playerNodes[state][fid]]
            else:
                nNode = ParityGameNode("NATURE", rank)
                succ1 = createParityGameNodes(state, lambdaFormula(0.0), rank, isProbabilistic)
                succ2 = createParityGameNodes(state, lambdaFormula(1.0), rank, isProbabilistic)
                nNode.successors = {succ1: 1 - val, succ2: val}
                natureNodes += [nNode]
        elif formula.op.type == "VAR":
            fixf = fixpointFormulas[formula.op.var]
            playerNodes[state][fid] = ParityGameNode("EVEN", rank, [createParityGameNodes(state, fixf, rank, isProbabilistic)])
        elif formula.op.type in ["AND", "OR"]:
            successors = []
            for subf in formula.subformulas:
                successors += [createParityGameNodes(state, subf, rank, isProbabilistic)]
            owner = "ODD" if formula.op.type == "AND" else "EVEN"
            playerNodes[state][fid] = ParityGameNode(owner, rank, successors)
        elif formula.op.type in ["DIAMOND", "BOX"]:
            subf = formula.subformulas[0]
            successors = []
            nsuccessors = {}
            transitions = model.outgoing(state, formula.op.action)
            if not transitions:
                # owner inversed for consistency with 0.0 nodes and 1.0 nodes
                owner = "EVEN" if formula.op.type == "BOX" else "ODD"
                playerNodes[state][fid] = ParityGameNode(owner, nextRank(rank, formula.op.type == "BOX"))
                playerNodes[state][fid].successors = [playerNodes[state][fid]]
            else:
                owner = "EVEN" if formula.op.type == "DIAMOND" else "ODD"
                for transition in transitions:
                    for s in transition.enddist:
                        succ = createParityGameNodes(s, subf, rank, isProbabilistic)
                        if isProbabilistic:
                            nsuccessors[succ] = transition.enddist[s]
                        else:
                            successors += [succ]

                    if isProbabilistic:
                        nNode = ParityGameNode("NATURE", rank, nsuccessors)
                        nsuccessors = {}
                        natureNodes += [nNode]
                        successors += [nNode]

                playerNodes[state][fid] = ParityGameNode(owner, rank, successors)
        elif formula.op.type in ["LEASTFP", "GREATESTFP"]:
            subf = formula.subformulas[0]
            nRank = nextRank(rank, formula.op.type == "GREATESTFP")
            # store node first to avoid infinite recursion
            playerNodes[state][fid] = ParityGameNode("EVEN", nRank)
            playerNodes[state][fid].successors = [createParityGameNodes(state, subf, nRank, isProbabilistic)]
    return playerNodes[state][fid]


def createParityGameFromPLmu(formula, isProbabilistic=False):
    global playerNodes, fixpointFormulas
    playerNodes = [{} for i in range(model.numstates)]
    fixpointFormulas = {subf.op.var: subf for subf in formula.getSubFormulas(["LEASTFP", "GREATESTFP"])}

    initNode = createParityGameNodes(model.initstate, formula, 0, isProbabilistic)
    pNodes = []
    # set node data
    for s in range(len(playerNodes)):
        for f in playerNodes[s]:
            node = playerNodes[s][f]
            node.state = s
            node.formula = f
            pNodes += [node]
    return ParityGame(initNode, pNodes + natureNodes)


# nodes are indexed by variable, (real) formula
equations = {}
nodesFRF = {}


# returns the node it has created
def createParityGameNodesFromRealFormula(var, formula, rank):
    global nodesFRF
    fid = str(formula)
    # check if we already have this node
    if var not in nodesFRF:
        nodesFRF[var] = {}
    if fid not in nodesFRF[var]:
        if formula.op.type == "VAL":
            val = formula.op.val
            # 0.0 nodes are for ODD, 1.0 nodes for EVEN (not that it matters, but it is a node they will certainly win)
            if val == 0.0:
                node = ParityGameNode("ODD", nextRank(rank, False))
                node.successors = [node]
            elif val == 1.0:
                node = ParityGameNode("EVEN", nextRank(rank, True))
                node.successors = [node]
            else:
                node = ParityGameNode("NATURE", rank)
                succ1 = createParityGameNodesFromRealFormula(var, valueFormula(0.0), rank)
                succ2 = createParityGameNodesFromRealFormula(var, valueFormula(1.0), rank)
                node.successors = {succ1: 1 - val, succ2: val}
            nodesFRF[var][fid] = node
        elif formula.op.type == "VAR":
            newVar = formula.op.var
            nodesFRF[var][fid] = ParityGameNode("EVEN", rank)
            nodesFRF[var][fid].successors = [createParityGameNodesFromRealFormula(newVar, equations[newVar].rhs,
                                                                                  nextRank(rank, equations[newVar].sign == "nu"))]
        elif formula.op.type == "MULTIPLY":
            nodesFRF[var][fid] = ParityGameNode("NATURE", rank)
            multVar = [term.op.var for term in formula.operands if term.op.type == "VAR"][0].op.var
            multVal = [term.op.val for term in formula.operands if term.op.type == "VAL"][0].op.val
            nodesFRF[var][fid].successors = {createParityGameNodesFromRealFormula(var, valueFormula(0.0), rank): multVal,
                                             createParityGameNodesFromRealFormula(var, multVar, rank): 1-multVal}
        elif formula.op.type == "ADD":
            prob = 1
            successors = {}
            nodesFRF[var][fid] = ParityGameNode("NATURE", rank)
            for operand in formula.operands:
                if operand.op.type == "VAL":
                    successors[createParityGameNodesFromRealFormula(var, valueFormula(1.0), rank)] = operand.op.val
                    prob -= operand.op.val
                elif operand.op.type == "MULTIPLY":
                    multVarOperand = [term for term in operand.operands if term.op.type == "VAR"][0]
                    multVal = [term.op.val for term in operand.operands if term.op.type == "VAL"][0]
                    successors[createParityGameNodesFromRealFormula(var, multVarOperand, rank)] = multVal
                    prob -= multVal
            if prob > 0.0:  # since we do not allow TCOSUM and TSUM, prob cannot get below 0.0
                successors[createParityGameNodesFromRealFormula(var, valueFormula(0.0), rank)] = prob
            nodesFRF[var][fid].successors = successors
        elif formula.op.type in ["MAXIMUM", "MINIMUM"]:
            nodesFRF[var][fid] = ParityGameNode("EVEN" if formula.op.type == "MAXIMUM" else "ODD", rank)
            nodesFRF[var][fid].successors = [createParityGameNodesFromRealFormula(var, operand, rank) for operand in formula.operands]
        nodesFRF[var][fid].state = var
        nodesFRF[var][fid].formula = fid
    return nodesFRF[var][fid]


# create a parity game form a RES
# equations that are not needed for the solution are not converted (would be unreachable anyway)
def createParityGameFromRES(formula):
    res = createRES(formula, model)
    res = toDisConjunctiveForm(res)
    global equations
    for equation in res.equations:
        equations[equation.lhs] = equation

    initEq = res.equations[model.initstate]
    initNode = createParityGameNodesFromRealFormula(initEq.lhs, initEq.rhs, nextRank(0, initEq.sign == "nu"))
    return ParityGame(initNode, [nodesFRF[v][f] for v in nodesFRF for f in nodesFRF[v]])


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
    global reachedNodes
    reachedNodes = []
    reduceParityGameRec(parityGame.initNode)
    newInit = parityGame.initNode.reduction
    reachabilitySet(newInit)
    return ParityGame(newInit, reachedNodes, False)


def initParityGameCreator(ts, formula, fromRES, store, verbose, isProbabilistic):
    global model, printInfo
    model = ts
    printInfo = verbose

    parityGame = None
    if formula.getSubFormulas(["PRODUCT", "COPRODUCT", "TCOSUM", "TSUM"]):
        print("The operators (co)product and truncated (co)sum are not supported")
    elif fromRES:
        parityGame = reduceParityGame(createParityGameFromRES(formula))
    else:
        parityGame = reduceParityGame(createParityGameFromPLmu(formula, isProbabilistic))
    if store and parityGame is not None:
            parityGame.toDot(formula.name, "_RES" if fromRES else "", False)
    return None
