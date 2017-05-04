import os
import copy
from RationalFormula import *


#maximum number of iterations for the solver by fixpoint
maxiter = 50

class RationalEquation:

    def __init__(self, sign, lhs, rhs):
        self.sign = sign
        self.lhs = lhs
        self.rhs = rhs  # simplify(rhs)

    def __repr__(self):
        return self.sign + ' ' + self.lhs + ' = ' + str(self.rhs) + ' = ' + str(simplify(self.rhs))


class RationalEquationSystem:

    def __init__(self, equations):
        self.equations = equations

    def __repr__(self):
        return '\n'.join(str(e) for e in self.equations)


model = None


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
        multiplication1 = RationalFormulaNode(RationalOperatorNode("MULTIPLY"), [valueFormula(formula.op.val), operands[0]])
        subtraction = RationalFormulaNode(RationalOperatorNode("SUBTRACT"), [valueFormula(1.0), valueFormula(formula.op.val)])
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
            equations += [RationalEquation(sign, fixf.op.var + str(state), RHS(state, fixf.subformulas[0]))]

    return RationalEquationSystem(equations)


def solveEquation(equation):
    # fixpoint approximation
    var = equation.lhs
    oldrhs = valueFormula(0.0 if equation.sign == "mu" else 1.0)
    newrhs = equation.rhs
    iter = 0
    while oldrhs != newrhs and iter < maxiter:
        oldrhs = copy.deepcopy(newrhs)
        newrhs = simplify(toNormalForm(substituteVar(equation.rhs, var, oldrhs)))
        iter += 1
    equation.rhs = newrhs
    return equation


def solveRES(res):
    for i in reversed(range(0, len(res.equations))):
        equation = res.equations[i]
        var = equation.lhs
        equation.rhs = simplify(toNormalForm(simplify(equation.rhs)), False)
        # solve own equation if necessary
        if equation.rhs.containsVar(var):
            solveEquation(equation)

        # substitute above
        for j in reversed(range(0, i)):
            res.equations[j].rhs = substituteVar(res.equations[j].rhs, var, equation.rhs)
        print(str(res) + '\n')

    return float(res.equations[0].rhs.op.val)


def initRESSolver(ts, formula, store):
    global model
    model = ts

    res = createRES(formula)

    if store:
        f = open(os.path.sep.join([os.path.split(model.file)[0], model.name + "_" + formula.name + "_RES.res"]), 'w')
        f.write(str(res))
        f.close()

    return None  # solveRES(pes)
