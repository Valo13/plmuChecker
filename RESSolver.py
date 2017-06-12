import os
from RationalFormula import *

# maximum number of iterations for the solver by fixpoint
MAX_ITER = 5


class RationalEquation:
    def __init__(self, sign, lhs, rhs):
        self.sign = sign
        self.lhs = lhs
        self.rhs = rhs  # simplify(rhs)

    def __str__(self):
        return self.sign + ' ' + self.lhs + ' = ' + str(self.rhs)

    def __repr__(self):
        return self.sign + ' ' + self.lhs + ' = ' + repr(self.rhs)


class RationalEquationSystem:
    def __init__(self, equations):
        self.equations = equations

    def __str__(self):
        return '\n'.join(str(e) for e in self.equations)


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
        return RationalFormulaNode(RationalOperatorNode("VAR", newVar))

    # in case binary (OR, AND, PRODUCT, COPRODUCT, TCOSUM, TSUM, LAMBDA), apply semantics
    elif formula.op.type == "OR":
        operands = [RHS(state, formula.subformulas[i]) for i in [0, 1]]
        return RationalFormulaNode(RationalOperatorNode("MAXIMUM"), operands)
    elif formula.op.type == "AND":
        operands = [RHS(state, formula.subformulas[i]) for i in [0, 1]]
        return RationalFormulaNode(RationalOperatorNode("MINIMUM"), operands)
    elif formula.op.type == "PRODUCT":
        operands = [RHS(state, formula.subformulas[i]) for i in [0, 1]]
        return RationalFormulaNode(RationalOperatorNode("MULTIPLY"), operands)
    elif formula.op.type == "COPRODUCT":
        operands = [RHS(state, formula.subformulas[i]) for i in [0, 1]]
        addition = RationalFormulaNode(RationalOperatorNode("ADD"), operands)
        multiplication = RationalFormulaNode(RationalOperatorNode("MULTIPLY"), operands)
        return RationalFormulaNode(RationalOperatorNode("SUBTRACT"), [addition, multiplication])
    elif formula.op.type == "TCOSUM":
        operands = [RHS(state, formula.subformulas[i]) for i in [0, 1]]
        addition = RationalFormulaNode(RationalOperatorNode("ADD"), operands)
        subtraction = RationalFormulaNode(RationalOperatorNode("MAXIMUM"), [addition, valueFormula(1.0)])
        return RationalFormulaNode(RationalOperatorNode("MAXIMUM"), [valueFormula(0.0), subtraction])
    elif formula.op.type == "TSUM":
        operands = [RHS(state, formula.subformulas[i]) for i in [0, 1]]
        addition = RationalFormulaNode(RationalOperatorNode("ADD"), operands)
        return RationalFormulaNode(RationalOperatorNode("MINIMUM"), [valueFormula(1.0), addition])
    elif formula.op.type == "LAMBDA":
        operands = [RHS(state, formula.subformulas[i]) for i in [0, 1]]
        multiplication1 = RationalFormulaNode(RationalOperatorNode("MULTIPLY"),
                                              [valueFormula(formula.op.val), operands[0]])
        subtraction = RationalFormulaNode(RationalOperatorNode("SUBTRACT"),
                                          [valueFormula(1.0), valueFormula(formula.op.val)])
        multiplication2 = RationalFormulaNode(RationalOperatorNode("MULTIPLY"), [subtraction, operands[1]])
        return RationalFormulaNode(RationalOperatorNode("ADD"), [multiplication1, multiplication2])

    # in case diamond or box, create formula with subformula for each outgoing transition with given action
    elif formula.op.type in ["DIAMOND", "BOX"]:
        products = [[RationalFormulaNode(RationalOperatorNode("MULTIPLY"), [
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
                return RationalFormulaNode(RationalOperatorNode("ADD"), products[0])

        # in case more than one transition, create maximum if diamond, else minimum
        else:
            op = "MAXIMUM" if formula.op.type == "DIAMOND" else "MINIMUM"
            sums = []
            for transProducts in products:
                if len(transProducts) == 1:
                    sums += transProducts[0]
                else:
                    sums += [RationalFormulaNode(RationalOperatorNode("ADD"), transProducts)]
            return RationalFormulaNode(RationalOperatorNode(op), sums)


def createRES(formula):
    fixpoints = formula.getSubFormulas(["LEASTFP", "GREATESTFP"])
    equations = []
    for fixf in fixpoints:
        sign = "mu" if fixf.op.type == "LEASTFP" else "nu"
        for state in range(0, model.numstates):
            rhs = RHS(state, fixf.subformulas[0])
            equations += [RationalEquation(sign, fixf.op.var + str(state), simplify(toNormalForm(simplify(rhs)), True))]

    return RationalEquationSystem(equations)


# uses fixpoint approximation to solve equation
def solveEquationApprox(equation):
    # fixpoint approximation
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
# assumes normal form without max or min
def solveForVar(formula, var, sign):

    if not formula.containsVar(var):
        return formula
    else:
        # solve (for now linear)
        if formula.op.type == "VAR":
            return valueFormula(0.0 if sign == "mu" else 1.0)
        elif formula.op.type == "MULTIPLY":
            return valueFormula(0.0)
        else:
            operandWithVar = [operand for operand in formula.operands if operand.containsVar(var)][0]
            if operandWithVar.op.type == "VAR":
                return valueFormula(0.0 if sign == "mu" else 1.0)
            else:
                val = [term.op.val for term in operandWithVar.operands if term.op.type == "VAL"][0]
                operandsWithoutVar = [operand for operand in formula.operands if not operand.containsVar(var)]
                scalar = 1.0 / (1.0 - val)
                if len(operandsWithoutVar) == 1:
                    scaledrhs = RationalFormulaNode(RationalOperatorNode("MULTIPLY"),
                                                    [valueFormula(scalar), operandsWithoutVar[0]])
                else:
                    scaledrhs = RationalFormulaNode(RationalOperatorNode("MULTIPLY"),
                                                    [valueFormula(scalar), RationalFormulaNode(
                                                                     RationalOperatorNode("ADD"), operandsWithoutVar)
                                                     ])
                return simplify(toNormalForm(scaledrhs), True)


# uses math to solve equation
# requires normal form and variable in lhs also in rhs
def solveEquation(equation):
    print("solving " + str(equation.rhs) + " for " + equation.lhs)
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
    print("result: " + repr(equation))
    return equation


def solveRES(res):
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

    # get the value for the initial state by substituting the resulting value downward
    for i in range(1, model.initstate + 1):
        for j in range(i):
            res.equations[i].rhs = substituteVar(res.equations[i].rhs, res.equations[j].lhs, res.equations[j].rhs)
        res.equations[i].rhs = simplify(res.equations[i].rhs)

    return float(res.equations[model.initstate].rhs.op.val)


def initRESSolver(ts, formula, store, verbose):
    global model, printInfo
    model = ts
    printInfo = verbose

    # for now, we do not allow formulas with the operators PRODUCT, COPRODUCT, TCOSUM and TSUM
    if formula.getSubFormulas(["PRODUCT", "COPRODUCT", "TCOSUM", "TSUM"]):
        return None

    res = createRES(formula)

    if store:
        f = open(os.path.sep.join([os.path.split(model.file)[0], model.name + "_" + formula.name + "_RES.res"]), 'w')
        f.write(str(res))
        f.close()

    return solveRES(res)
