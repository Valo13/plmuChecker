import os
import time
from RealFormula import *
from FormulaReader import *
from tarjan import tarjan

# maximum number of iterations for the solver by fixpoint
MAX_ITER = 5


class RealEquation:
    def __init__(self, sign, lhs, rhs):
        self.sign = sign
        self.lhs = lhs
        self.rhs = rhs
        self.processed = False

    def __str__(self):
        return self.sign + ' ' + self.lhs + ' = ' + str(self.rhs)

    def __repr__(self):
        return self.sign + ' ' + self.lhs + ' = ' + repr(self.rhs)


class RealEquationSystem:
    def __init__(self, equations, initVar):
        self.equations = equations
        # we also index the equations on the variable in the left hand side for easy access
        self.indexedEquations = {}
        for eq in equations:
            self.indexedEquations[eq.lhs] = eq

        self.initVar = initVar

    def __str__(self):
        return '\n'.join(str(e) for e in self.equations)

    def __repr__(self):
        return '\n'.join(repr(e) for e in self.equations)


# given a RES, create an equivalent res where every equation does not contain both max and min
# assumes that the res is simplified and in normal form
def toDisConjunctiveForm(res):
    newEquations = []
    for equation in res.equations:
        f = equation.rhs
        if f.op.type == "MAXIMUM" and any([subf.op.type == "MINIMUM" for subf in f.operands]):
            nr = 0
            extraEquations = []
            for i in range(len(f.operands)):
                subf = f.operands[i]
                if subf.op.type == "MINIMUM":
                    newVar = equation.lhs + "-" + str(nr)
                    nr += 1
                    extraEquations += [RealEquation(equation.sign, newVar, subf)]
                    f.operands[i] = newVar
            newEquations += [equation] + extraEquations
        else:
            newEquations += [equation]

    return RealEquationSystem(newEquations, res.initVar)


model = None
printInfo = False


# creates the right-hand side of a boolean equation
def RHS(state, formula):
    # in case operator is VAL, we just return itself
    if formula.op.type == "VAL":
        return valueFormula(formula.op.val)

    # in case variable or fixpoint, its just a variable
    elif formula.op.type in ["VAR", "LEASTFP", "GREATESTFP"]:
        newVar = formula.op.var + str(state)
        return RealFormulaNode(RealOperatorNode("VAR", newVar))

    # in case of label operator, return the label
    elif formula.op.type == "LABEL":
        return valueFormula(model.labels[state])

    # in case binary (OR, AND, PRODUCT, COPRODUCT, TCOSUM, TSUM, LAMBDA), apply semantics
    elif formula.op.type == "OR":
        operands = [RHS(state, formula.subformulas[i]) for i in [0, 1]]
        return RealFormulaNode(RealOperatorNode("MAXIMUM"), operands)
    elif formula.op.type == "AND":
        operands = [RHS(state, formula.subformulas[i]) for i in [0, 1]]
        return RealFormulaNode(RealOperatorNode("MINIMUM"), operands)
    elif formula.op.type == "PRODUCT":  # NOT SUPPORTED
        operands = [RHS(state, formula.subformulas[i]) for i in [0, 1]]
        return RealFormulaNode(RealOperatorNode("MULTIPLY"), operands)
    elif formula.op.type == "COPRODUCT":  # NOT SUPPORTED
        operands = [RHS(state, formula.subformulas[i]) for i in [0, 1]]
        addition = RealFormulaNode(RealOperatorNode("ADD"), operands)
        multiplication = RealFormulaNode(RealOperatorNode("MULTIPLY"), operands)
        return RealFormulaNode(RealOperatorNode("SUBTRACT"), [addition, multiplication])
    elif formula.op.type == "TCOSUM":
        operands = [RHS(state, formula.subformulas[i]) for i in [0, 1]]
        addition = RealFormulaNode(RealOperatorNode("ADD"), operands)
        subtraction = RealFormulaNode(RealOperatorNode("ADD"), [addition, valueFormula(-1.0)])
        importantZero = valueFormula(0.0)
        importantZero.makeImportant()
        return RealFormulaNode(RealOperatorNode("MAXIMUM"), [importantZero, subtraction])
    elif formula.op.type == "TSUM":
        operands = [RHS(state, formula.subformulas[i]) for i in [0, 1]]
        addition = RealFormulaNode(RealOperatorNode("ADD"), operands)
        importantOne = valueFormula(1.0)
        importantOne.makeImportant()
        return RealFormulaNode(RealOperatorNode("MINIMUM"), [importantOne, addition])
    elif formula.op.type == "LAMBDA":
        operands = [RHS(state, formula.subformulas[i]) for i in [0, 1]]
        multiplication1 = RealFormulaNode(RealOperatorNode("MULTIPLY"), [valueFormula(formula.op.val), operands[0]])
        multiplication2 = RealFormulaNode(RealOperatorNode("MULTIPLY"), [valueFormula(1 - formula.op.val), operands[1]])
        return RealFormulaNode(RealOperatorNode("ADD"), [multiplication1, multiplication2])

    # in case diamond or box, create formula with subformula for each outgoing transition with given action
    elif formula.op.type in ["DIAMOND", "BOX"]:
        products = [[RealFormulaNode(RealOperatorNode("MULTIPLY"), [
            valueFormula(t.enddist[endstate]), RHS(endstate, formula.subformulas[0])
        ]) for endstate in t.enddist.keys()
                     ] for t in model.outgoing(state, formula.op.action)]

        # in case no transitions, return 0 if diamond, else 1
        if not products:
            return valueFormula(0.0) if formula.op.type == "DIAMOND" else valueFormula(1.0)

        # in case one transition
        elif len(products) == 1:
            if len(products[0]) == 1:
                return products[0][0]
            else:
                return RealFormulaNode(RealOperatorNode("ADD"), products[0])

        # in case more than one transition, create maximum if diamond, else minimum
        else:
            op = "MAXIMUM" if formula.op.type == "DIAMOND" else "MINIMUM"
            sums = []
            for transProducts in products:
                if len(transProducts) == 1:
                    sums += [transProducts[0]]
                else:
                    sums += [RealFormulaNode(RealOperatorNode("ADD"), transProducts)]
            return RealFormulaNode(RealOperatorNode(op), sums)


# the dependence graph
depChildren = {}  # X:list means X depends on all variables in list
depParents = {}  # X:list means all variables in list depend on X


def createRES(formula, ts, makeDepGraph):
    global model
    model = ts
    # alter the formula so that it starts with a fixpoint operator
    if formula.op.type not in ["LEASTFP", "GREATESTFP"]:
        formula = FormulaNode([[OperatorNode([OperatorNode(["Q"], "VAR")], "LEASTFP"), formula]])
    fixpoints = formula.getSubFormulas(["LEASTFP", "GREATESTFP"])
    equations = []
    for fixf in fixpoints:
        sign = "mu" if fixf.op.type == "LEASTFP" else "nu"
        for state in range(0, model.numstates):
            var = fixf.op.var + str(state)
            rhs = RHS(state, fixf.subformulas[0])
            equation = RealEquation(sign, var, simplify(toNormalForm(simplify(rhs)), True))
            equations += [equation]

            if makeDepGraph:
                depChildren[var] = set()
                if var not in depParents:
                    depParents[var] = set()

                # create edges in the dependency graph
                for varFormula in equation.rhs.getSubFormulas(["VAR"]):
                    depVar = varFormula.op.var

                    depChildren[var].add(depVar)
                    if depVar not in depParents:
                        depParents[depVar] = {var}
                    else:
                        depParents[depVar].add(var)

    return RealEquationSystem(equations, formula.op.var + str(ts.initstate))


def createLocalRES(formula, ts, SCC, makeDepGraph):
    global model, depChildren, depParents
    model = ts
    depChildren = {}
    depParents = {}

    # alter the formula so that it starts with a fixpoint operator
    if formula.op.type not in ["LEASTFP", "GREATESTFP"]:
        formula = FormulaNode([[OperatorNode([OperatorNode(["Q"], "VAR")], "LEASTFP"), formula]])
    fixpoints = formula.getSubFormulas(["LEASTFP", "GREATESTFP"])
    indexedFixpoints = {fix.op.var: fix for fix in fixpoints}
    signs = {fix.op.var: ('mu' if fix.op.type == "LEASTFP" else 'nu') for fix in fixpoints}

    # initialize blocks
    varRank = {}
    blockRank = 0
    if SCC:
        blockSign = signs[fixpoints[0].op.var]
        for fixf in fixpoints:
            if signs[fixf.op.var] != blockSign:
                blockRank += 1
                blockSign = signs[fixf.op.var]
            varRank[fixf.op.var] = blockRank
    blocks = [[] for rank in range(blockRank + 1)]

    equations = []
    initVar = fixpoints[0].op.var + str(ts.initstate)
    varQueue = [initVar]
    varQueuePointer = 0
    while varQueuePointer < len(varQueue):
        var = varQueue[varQueuePointer]
        rhs = RHS(int(var[1:]), indexedFixpoints[var[0]].subformulas[0])
        eq = RealEquation(signs[var[0]], var, simplify(toNormalForm(simplify(rhs)), True))
        equations += [eq]

        if SCC:
            blocks[varRank[var[0]]] += [eq]

        if makeDepGraph:
            depChildren[var] = set()
            if var not in depParents:
                depParents[var] = set()

        # add all variables that eq depends on to the queue (if not there already)
        for varFormula in eq.rhs.getSubFormulas(["VAR"]):
            newVar = varFormula.op.var
            if newVar not in varQueue:
                varQueue += [newVar]

            if makeDepGraph:
                # create edges in the dependency graph
                depChildren[var].add(newVar)
                if newVar not in depParents:
                    depParents[newVar] = {var}
                else:
                    depParents[newVar].add(var)

        varQueuePointer += 1

    res = RealEquationSystem(equations, initVar)
    createEnd = time.clock()

    # sort so that we can compare the solving time it to non-local version
    if not SCC:
        fixpointVars = [fix.op.var for fix in fixpoints]
        toSort = [(var[0], var[1:]) for var in res.indexedEquations.keys()]
        toSort.sort(key=lambda x: (fixpointVars.index(x[0]), int(x[1])))
        res = RealEquationSystem([res.indexedEquations[v + s] for (v, s) in toSort], res.initVar)
    else:
        res.blocks = blocks
        res.varRank = varRank

    return res, createEnd


# uses fixpoint approximation to solve equation
def solveEquationApprox(equation):
    var = equation.lhs
    oldrhs = None
    newrhs = valueFormula(0.0 if equation.sign == "mu" else 1.0)
    iter = 0
    while oldrhs != newrhs and iter < MAX_ITER:
        oldrhs = copy.deepcopy(newrhs)
        newrhs = simplify(toNormalForm(substituteVar(copy.deepcopy(equation.rhs), var, oldrhs)), True)
        iter += 1
        # print("iteration " + str(iter) + ": " + var + " = " + str(newrhs))
    equation.rhs = newrhs
    return equation


# solve equation var = formula for var
# assumes that formula to be in normal form without max or min and that var is in formula
# note that due to TCOSUM and TSUM the result may be outside [0,1]
#   however, this is not an issue since there is another term somewhere that will be chosen above this one in that case
def solveForVar(formula, var, sign):

    if not formula.containsVar(var):
        return formula
    else:
        # solve (linear)
        if formula.op.type == "VAR":
            return valueFormula(0.0 if sign == "mu" else 1.0)
        elif formula.op.type == "MULTIPLY":
            return valueFormula(0.0)
        else:
            operandWithVar = [operand for operand in formula.operands if operand.containsVar(var)][0]
            if operandWithVar.op.type == "VAR":
                # print("found formula of form X = X + f, which may not have a solution")
                raise ZeroDivisionError
            else:
                val = [term.op.val for term in operandWithVar.operands if term.op.type == "VAL"][0]
                operandsWithoutVar = [operand for operand in formula.operands if not operand.containsVar(var)]
                scalar = 1.0 / (1.0 - val)
                if len(operandsWithoutVar) == 1:
                    scaledrhs = RealFormulaNode(RealOperatorNode("MULTIPLY"),
                                                [valueFormula(scalar), operandsWithoutVar[0]])
                else:
                    scaledrhs = RealFormulaNode(RealOperatorNode("MULTIPLY"),
                                                [valueFormula(scalar), RealFormulaNode(
                                                                     RealOperatorNode("ADD"), operandsWithoutVar)
                                                 ])
                return simplify(toNormalForm(scaledrhs), True)


# uses math to solve equation
# requires normal form and variable in lhs also in rhs
def solveEquation(equation):
    # print("solving " + str(equation.rhs) + " for " + equation.lhs)
    if equation.rhs.op.type in ["MAXIMUM", "MINIMUM"]:
        for i in range(len(equation.rhs.operands)):
            operand = equation.rhs.operands[i]
            if operand.op.type == "MINIMUM":
                for j in range(len(operand.operands)):
                    operand.operands[j] = solveForVar(operand.operands[j], equation.lhs, equation.sign)
            else:
                equation.rhs.operands[i] = solveForVar(operand, equation.lhs, equation.sign)
    else:
        equation.rhs = solveForVar(equation.rhs, equation.lhs, equation.sign)
    if printInfo:
        print("result: " + str(equation))
    return equation


# for parent 'parent' set its children to 'children'
def depSet(parent, children):
    # the old and new children are usually very similar, so we check what has changed and work with that
    toRemove = depChildren[parent].difference(children)
    toAdd = children.difference(depChildren[parent])
    depChildren[parent] = children
    for var in toRemove:
        depParents[var].remove(parent)
    for var in toAdd:
        depParents[var].add(parent)


def solveRES(res, useDepGraph):
    if printInfo:
        print("##### SOLVING RES #####")
    for i in reversed(range(0, len(res.equations))):
        equation = res.equations[i]
        var = equation.lhs
        if printInfo:
            print("##### handling " + var)
        # solve own equation if necessary
        if equation.rhs.containsVar(var):
            if printInfo:
                print("##### solving...")
            equation.rhs = simplify(solveEquation(equation).rhs, True)
            if useDepGraph:
                depSet(var, set(v.op.var for v in equation.rhs.getSubFormulas(["VAR"])))

        # substitute above
        if printInfo:
            print("##### substituting...")
        if useDepGraph:
            for parentVar in copy.copy(depParents[var]):
                eq = res.indexedEquations[parentVar]
                if not eq.processed:
                    eq.rhs = simplify(toNormalForm(simplify(substituteVar(eq.rhs, var, equation.rhs))), True)
                    depSet(parentVar, set(v.op.var for v in eq.rhs.getSubFormulas(["VAR"])))
        else:
            for j in reversed(range(0, i)):
                eq = res.equations[j]
                eq.rhs = simplify(toNormalForm(simplify(substituteVar(eq.rhs, var, equation.rhs))), True)

        equation.processed = True
        if printInfo:
            print(str(res) + '\n')

    i = 0
    nextEquation = res.equations[i]
    while nextEquation.lhs != res.initVar:
        for j in range(i+1, len(res.equations)):
            res.equations[j].rhs = simplify(substituteVar(res.equations[j].rhs, res.equations[i].lhs, res.equations[i].rhs))
        i += 1
        nextEquation = res.equations[i]
    return float(res.equations[i].rhs.op.val)


# returns the reversed order of breadth first search
# assumes that all vertices in "vertices" can be reached from a vertex in "start"
def reversedOrderBFS(vertices, start, blockDepChildren):
    visited = {v: (True if v in start else False) for v in vertices}
    orderedVertices = start
    index = 0
    while index < len(orderedVertices):
        for child in blockDepChildren[orderedVertices[index]]:
            if child in vertices and not visited[child]:
                orderedVertices += [child]
                visited[child] = True
        index += 1

    return reversed(orderedVertices)


# solve the RES with a more efficient order by using SCC's
def solveRESSCC(res):
    numBlocks = len(res.blocks)

    if printInfo:
        print("##### SOLVING RES #####")
    # from the last block to the first
    for rank in reversed(range(numBlocks)):
        # create the dependency graph for this block
        #  note that this dependency graph is only used to determine the ordering of solving the equations,
        #  it is not altered during solving
        if numBlocks == 1:
            blockDepChildren = depChildren
        else:
            blockDepChildren = {}
            for eq in res.blocks[rank]:
                blockDepChildren[eq.lhs] = set([child for child in depChildren[eq.lhs] if res.varRank[child[0]] == rank])

        # apply tarjan's algorithm to get all SCC's
        SCCs = tarjan(blockDepChildren)

        # note that tarjan's algorithm returns all SCC's in the reverse topological order,
        #  which is exactly the order we want for solving
        for i in range(len(SCCs)):
            SCC = SCCs[i]
            if len(SCC) > 1:
                # order the vertices in the SCC in reversed order of BFS
                if rank == 0 and i == len(SCCs) - 1:
                    # if we are at the very last SCC, we let the initial variable have depth 0
                    SCC = reversedOrderBFS(SCC, [res.initVar], blockDepChildren)
                else:
                    # else we let all vertices that have an incoming dependency from outside this SCC have depth 0
                    startingVertices = []
                    for var in SCC:
                        for parentVar in depParents[var]:
                            if parentVar not in SCC:
                                startingVertices += [var]
                    if len(SCC) > len(startingVertices):
                        SCC = reversedOrderBFS(SCC, startingVertices, blockDepChildren)
            for var in SCC:
                if printInfo:
                    print("##### handling " + var)
                equation = res.indexedEquations[var]

                # solve own equation if necessary
                if var in depChildren[var]:
                    if printInfo:
                        print("##### solving...")
                    equation.rhs = simplify(solveEquation(equation).rhs, True)
                    depSet(var, set(v.op.var for v in equation.rhs.getSubFormulas(["VAR"])))

                # substitute to parents
                if printInfo:
                    print("##### substituting...")
                for parentVar in copy.copy(depParents[var]):
                    eq = res.indexedEquations[parentVar]
                    if not eq.processed:
                        eq.rhs = simplify(toNormalForm(simplify(substituteVar(eq.rhs, var, equation.rhs))), True)
                        depSet(parentVar, set(v.op.var for v in eq.rhs.getSubFormulas(["VAR"])))

                equation.processed = True

                if printInfo:
                    print(str(res) + '\n')

    return float(res.indexedEquations[res.initVar].rhs.op.val)


def initRESSolver(ts, formula, store, verbose, local, depGraph, SCC):
    global printInfo
    printInfo = verbose

    # for now, we do not allow formulas with the operators PRODUCT and COPRODUCT
    if formula.getSubFormulas(["PRODUCT", "COPRODUCT"]):
        print("Operators product (*) and coproduct (#) are not supported")
        return None, 0, 0

    createStart = time.clock()
    if depGraph:
        global depChildren, depParents
        depChildren = {}
        depParents = {}
    if local or SCC:
        result = createLocalRES(formula, ts, SCC, depGraph)
        res = result[0]
        createEnd = result[1]
    else:
        res = createRES(formula, ts, depGraph)
        createEnd = time.clock()

    if store:
        f = open(os.path.sep.join([os.path.split(model.file)[0],
                                   ts.name + "_" + formula.name + "_RES" + ("_local" if local else "") + ".res"]), 'w')
        f.write(str(res))
        f.close()

    print("RES created")

    solveStart = time.clock()
    try:
        if SCC:
            value = solveRESSCC(res)
        else:
            value = solveRES(res, depGraph)
    except ZeroDivisionError:
        value = None
    solveEnd = time.clock()

    return value, createEnd - createStart, solveEnd - solveStart
