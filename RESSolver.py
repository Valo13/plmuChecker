import os
from RealFormula import *
from FormulaReader import *

# maximum number of iterations for the solver by fixpoint
MAX_ITER = 5


class RealEquation:
    def __init__(self, sign, lhs, rhs):
        self.sign = sign
        self.lhs = lhs
        self.rhs = rhs

    def __str__(self):
        return self.sign + ' ' + self.lhs + ' = ' + str(self.rhs)

    def __repr__(self):
        return self.sign + ' ' + self.lhs + ' = ' + repr(self.rhs)


class RealEquationSystem:
    def __init__(self, equations):
        self.equations = equations

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

    return RealEquationSystem(newEquations)


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


def createRES(formula, ts):
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
            rhs = RHS(state, fixf.subformulas[0])
            equations += [RealEquation(sign, fixf.op.var + str(state), simplify(toNormalForm(simplify(rhs)), True))]

    return RealEquationSystem(equations)


# creates a RES with only equations that matter for the solution
def createLocalRES(formula, ts):
    global model
    model = ts
    # alter the formula so that it starts with a fixpoint operator
    if formula.op.type not in ["LEASTFP", "GREATESTFP"]:
        formula = FormulaNode([[OperatorNode([OperatorNode(["Q"], "VAR")], "LEASTFP"), formula]])
    fixpoints = formula.getSubFormulas(["LEASTFP", "GREATESTFP"])
    equations = []
    varQueue = [formula.op.var + str(model.initstate)]
    varQueuePointer = 0
    while len(varQueue) > varQueuePointer:
        var = varQueue[varQueuePointer]
        fixVar = var[0]
        state = int(var[1:])
        fixf = [fixf for fixf in fixpoints if fixf.op.var == fixVar][0]
        sign = "mu" if fixf.op.type == "LEASTFP" else "nu"
        rhs = RHS(state, fixf.subformulas[0])
        # add variables to the queue to make equations for
        for varFormula in rhs.getSubFormulas(["VAR"]):
            newVar = varFormula.op.var
            if newVar not in varQueue:
                varQueue += [newVar]
        equations += [RealEquation(sign, var, simplify(toNormalForm(simplify(rhs)), True))]
        varQueuePointer += 1

    return RealEquationSystem(equations)


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


def solveRES(res, local):
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

        # substitute above
        if printInfo:
            print("##### substituting...")
        for j in reversed(range(0, i)):
            res.equations[j].rhs = simplify(toNormalForm(simplify(substituteVar(res.equations[j].rhs, var, equation.rhs))), True)
        if printInfo:
            print(str(res) + '\n')

    if local:
        print(res)
        return float(res.equations[0].rhs.op.val)
    else:
        # get the value for the initial state by substituting the resulting value downward
        for i in range(1, model.initstate + 1):
            for j in range(i):
                res.equations[i].rhs = substituteVar(res.equations[i].rhs, res.equations[j].lhs, res.equations[j].rhs)
            res.equations[i].rhs = simplify(res.equations[i].rhs)

        return float(res.equations[model.initstate].rhs.op.val)


def initRESSolver(ts, formula, store, verbose, local):
    global printInfo
    printInfo = verbose

    # for now, we do not allow formulas with the operators PRODUCT and COPRODUCT
    if formula.getSubFormulas(["PRODUCT", "COPRODUCT"]):
        print("Operators product (*) and coproduct (#) are not supported")
        return None

    if local:
        res = createLocalRES(formula, ts)
    else:
        res = createRES(formula, ts)

    if store:
        f = open(os.path.sep.join([os.path.split(model.file)[0], ts.name + "_" + formula.name + "_RES.res"]), 'w')
        f.write(str(res))
        f.close()

    try:
        return solveRES(res, local)
    except ZeroDivisionError:
        return None
