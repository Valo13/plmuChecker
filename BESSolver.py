import copy
import os

from FormulaReader import FormulaNode, OperatorNode


class BooleanEquation:

    def __init__(self, sign, lhs, rhs):
        self.sign = sign
        self.lhs = lhs
        self.rhs = simplify(rhs)

    def __repr__(self):
        return self.sign + ' ' + self.lhs + ' = ' + str(self.rhs)


class BooleanEquationSystem:

    def __init__(self, equations):
        self.equations = equations

    def __repr__(self):
        return '\n'.join(str(e) for e in self.equations)


model = None


# creates the right-hand side of a boolean equation
def RHS(state, formula):

    # in case operator is VAL, we just return itself
    newFormula = formula

    # in case variable or fixpoint, its just a variable
    if formula.op.type in ["VAR", "LEASTFP", "GREATESTFP"]:
        newVar = [formula.op.var + str(state)]
        newFormula = FormulaNode([OperatorNode(newVar, "VAR")])

    # in case binary (OR, AND, PRODUCT, COPRODUCT, TCOSUM, TSUM) use corresponding boolean operator (OR, AND)
    elif formula.type == "BINARY":
        op = "OR" if formula.op.type in ["OR", "COPRODUCT", "TSUM"] else "AND"
        subformulas = [RHS(state, formula.subformulas[i]) for i in [0, 1]]
        newFormula = FormulaNode([[subformulas[0], OperatorNode([], op), subformulas[1]]])

    # in case diamond or box, create formula with subformula for each outgoing transition with given action
    elif formula.op.type in ["DIAMOND", "BOX"]:
        subformulas = [RHS(t.enddist.keys()[0], formula.subformulas[0]) for t in model.outgoing(state, formula.op.action)]

        # in case no transitions, return 0 if diamond, else 1
        if not subformulas:
            return FormulaNode([OperatorNode(["0"] if formula.op.type == "DIAMOND" else ["1"], "VAL")])

        # in case one transition, return that RHS
        elif len(subformulas) == 1:
            return subformulas[0]

        # in case more than one transition, create disjunction if diamond, else conjunction (from left to right)
        else:
            op = "OR" if formula.op.type == "DIAMOND" else "AND"
            newFormula = subformulas[0]
            for i in range(1, len(subformulas)):
                newFormula = FormulaNode([[newFormula, OperatorNode([], op), subformulas[i]]])

    return newFormula


def createBES(formula):
    fixpoints = formula.getSubFormulas(["LEASTFP", "GREATESTFP"])
    equations = []
    for fixf in fixpoints:
        sign = "mu" if fixf.op.type == "LEASTFP" else "nu"
        for state in range(0, model.numstates):
            equations += [BooleanEquation(sign, fixf.op.var + str(state), RHS(state, fixf.subformulas[0]))]

    return BooleanEquationSystem(equations)


# applies boolean simplifications
def simplify(formula):
    for i in range(0, len(formula.subformulas)):
        formula.subformulas[i] = simplify(formula.subformulas[i])

    if formula.type is "BINARY":

        subfVars = [subf.op.var for subf in formula.subformulas if subf.op.type == "VAR"]
        subfIsFalse = [subf.op.type == "VAL" and subf.op.val == 0 for subf in formula.subformulas]
        subfIsTrue = [subf.op.type == "VAL" and subf.op.val == 1 for subf in formula.subformulas]

        # idempotence
        if len(subfVars) == 2 and subfVars[0] == subfVars[1]:
            return formula.subformulas[0]

        # zero and unit element for AND
        if formula.op.type in ["AND", "PRODUCT", "TCOSUM"]:
            if any(subfIsFalse):
                return FormulaNode([OperatorNode(["0"], "VAL")])
            elif any(subfIsTrue):
                return formula.subformulas[0] if subfIsTrue[1] else formula.subformulas[1]
        # zero and unit element for OR
        else:
            if any(subfIsTrue):
                return FormulaNode([OperatorNode(["1"], "VAL")])
            elif any(subfIsFalse):
                return formula.subformulas[0] if subfIsFalse[1] else formula.subformulas[1]

    return formula


# substitutes a formula 'new' for a variable 'var'
def substituteVar(formula, var, new):
    # print("substituting " + str(var) + " for " + str(new) + " in " + str(formula))
    if formula.op.type == "VAR" and formula.op.var == var:
        # not using copy is not wrong, but it is ugly
        # without it this will also substitute in equations below sometimes due to same reference
        return copy.deepcopy(new)
    else:
        for i in range(0, len(formula.subformulas)):
            formula.subformulas[i] = substituteVar(formula.subformulas[i], var, new)
    return formula


# solves BES using Gauss elimination
def solveBES(bes):
    for i in reversed(range(0, len(bes.equations))):
        equation = bes.equations[i]
        var = equation.lhs
        equation.rhs = substituteVar(equation.rhs, var, FormulaNode([OperatorNode(["0"] if equation.sign == "mu" else ["1"], "VAL")]))
        equation.rhs = simplify(equation.rhs)
        for j in reversed(range(0, i)):
            bes.equations[j].rhs = substituteVar(bes.equations[j].rhs, var, equation.rhs)
        print(str(bes) + '\n')

    return bool(bes.equations[0].rhs.op.val)


def initBESSolver(ts, formula, store):
    global model
    model = ts

    bes = createBES(formula)

    if store:
        f = open(os.path.sep.join([os.path.split(model.file)[0], model.name + "_" + formula.name + "_BES.txt"]), 'w')
        f.write(str(bes))
        f.close()

    return solveBES(bes)
