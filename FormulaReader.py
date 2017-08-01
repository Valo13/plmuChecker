from pyparsing import *
import os


class FormulaNode:
    def __init__(self, tokens):
        if isinstance(tokens[0], OperatorNode):
            self.type = "NULLARY"
            self.op = tokens[0]
            self.subformulas = []
            self.vars = []
            self.closedVars = []
        else:
            tokens = tokens[0]  # for some reason pyparsing creates list of list of tokens in case not nullary
            if len(tokens) == 2:
                self.type = "UNARY"
                self.op = tokens[0]
                self.subformulas = [tokens[1]]
            else:
                self.type = "BINARY"
                self.op = tokens[-2]
                if len(tokens) > 3:
                    self.subformulas = [FormulaNode([tokens[:-2]]), tokens[-1]]
                else:
                    self.subformulas = [tokens[0], tokens[-1]]

    # returns whether this formula is closed
    def isClosed(self):
        return len(self.vars) == len(self.closedVars)

    # gets all subformulas with operator type in 'optypes'
    def getSubFormulas(self, optypes):
        subf = []
        if self.op.type in optypes:
            subf += [self]
        for f in self.subformulas:
            subf += f.getSubFormulas(optypes)
        return subf

    def toObjectString(self):
        if self.type == "NULLARY":
            return 'Formula(' + self.op.toObjectString() + ')'
        elif self.type == "UNARY":
            return 'Formula(' + self.op.toObjectString() + ', ' + self.subformulas[0].toObjectString() + ')'
        elif self.type == "BINARY":
            return 'Formula(' + self.subformulas[0].toObjectString() + ', ' + self.op.toObjectString() + ', ' + self.subformulas[1].toObjectString() + ')'

    def __repr__(self):
        if self.type == "NULLARY":
            return str(self.op)
        elif self.type == "UNARY":
            return str(self.op) + str(self.subformulas[0])
        elif self.type == "BINARY":
            return '(' + str(self.subformulas[0]) + ' ' + str(self.op) + ' ' + str(self.subformulas[1]) + ')'


class OperatorNode:
    def __init__(self, tokens, type):
        self.type = type
        if type in ["VAL", "LAMBDA"]:
            self.val = float(tokens[0])
        elif type in ["DIAMOND", "BOX"]:
            self.action = tokens[0]
        elif type == "VAR":
            self.var = tokens[0]
        elif type in ["LEASTFP", "GREATESTFP"]:
            self.var = tokens[0].var

    def __repr__(self):
        if self.type == "VAL":
            return str(self.val)
        elif self.type == "VAR":
            return self.var
        elif self.type == "LABEL":
            return "l"
        elif self.type == "AND":
            return "&&"
        elif self.type == "OR":
            return "||"
        elif self.type == "PRODUCT":
            return "*"
        elif self.type == "COPRODUCT":
            return "#"
        elif self.type == "TCOSUM":
            return "--"
        elif self.type == "TSUM":
            return "++"
        elif self.type == "LAMBDA":
            return "+{" + str(self.val) + "}"
        elif self.type == "DIAMOND":
            return "<" + self.action + ">"
        elif self.type == "BOX":
            return "[" + self.action + "]"
        elif self.type == "LEASTFP":
            return "mu " + self.var + "."
        elif self.type == "GREATESTFP":
            return "nu " + self.var + "."

    def toObjectString(self):
        return self.type


def lambdaFormula(val):
    return FormulaNode([OperatorNode([val], "VAL")])


def grammar():
    LCURLY = Literal("{").suppress()
    RCURLY = Literal("}").suppress()
    LPOINTY = Literal("<").suppress()
    RPOINTY = Literal(">").suppress()
    LFLAT = Literal("[").suppress()
    RFLAT = Literal("]").suppress()
    DOT = Literal(".").suppress()
    ACTION = Regex("[a-zA-Z_][a-zA-Z0-9_\(\)]*")
    MU = Keyword("mu").suppress()
    NU = Keyword("nu").suppress()
    PROB = Regex("1|0(\.[0-9]*)?")

    VAL = PROB.setParseAction(lambda tokens: OperatorNode(tokens, "VAL"))
    VAR = Regex("[A-Z]").setParseAction(lambda tokens: OperatorNode(tokens, "VAR"))
    LABEL = Literal("l").setParseAction(lambda tokens: OperatorNode(tokens, "LABEL"))
    AND = Literal("&&").suppress().setParseAction(lambda tokens: OperatorNode(tokens, "AND"))
    OR = Literal("||").suppress().setParseAction(lambda tokens: OperatorNode(tokens, "OR"))
    PRODUCT = Literal("*").suppress().setParseAction(lambda tokens: OperatorNode(tokens, "PRODUCT"))
    COPRODUCT = Literal("#").suppress().setParseAction(lambda tokens: OperatorNode(tokens, "COPRODUCT"))
    TCOSUM = Literal("--").suppress().setParseAction(lambda tokens: OperatorNode(tokens, "TCOSUM"))
    TSUM = Literal("++").suppress().setParseAction(lambda tokens: OperatorNode(tokens, "TSUM"))
    LAMBDA = (Literal("+").suppress() + LCURLY + PROB + RCURLY).setParseAction(lambda tokens: OperatorNode(tokens, "LAMBDA"))
    DIAMOND = (LPOINTY + ACTION + RPOINTY).setParseAction(lambda tokens: OperatorNode(tokens, "DIAMOND"))
    BOX = (LFLAT + ACTION + RFLAT).setParseAction(lambda tokens: OperatorNode(tokens, "BOX"))
    LEASTFP = (MU + VAR + DOT).setParseAction(lambda tokens: OperatorNode(tokens, "LEASTFP"))
    GREATESTFP = (NU + VAR + DOT).setParseAction(lambda tokens: OperatorNode(tokens, "GREATESTFP"))

    OP1L = DIAMOND ^ BOX ^ LEASTFP ^ GREATESTFP
    OP2 = AND ^ OR ^ PRODUCT ^ COPRODUCT ^ TCOSUM ^ TSUM ^ LAMBDA

    FORMULAATOM = (VAL ^ VAR ^ LABEL).setParseAction(FormulaNode)

    FORMULA = operatorPrecedence(FORMULAATOM, [(OP1L, 1, opAssoc.RIGHT, FormulaNode), (OP2, 2, opAssoc.LEFT, FormulaNode)])

    return FORMULA


# adds information to a formula about what variables appear (closed and free)
#  and whether the formula can only be interpreted as probabilistic
def addInfo(formula):
    vars = []
    closedVars = []
    isOnlyProbabilistic = False
    if formula.op.type == "VAR":
        vars += [formula.op.var]
    elif (formula.op.type == "VAL" and formula.op.val not in [0.0, 1.0]) or formula.op.type == "LABEL":
            isOnlyProbabilistic = True
    elif formula.type != "NULLARY":
        for subformula in formula.subformulas:
            addInfo(subformula)
            vars += subformula.vars
            closedVars += subformula.closedVars
            isOnlyProbabilistic |= subformula.isOnlyProbabilistic

        if formula.op.type in ["LEASTFP", "GREATESTFP"]:
            closedVars += [formula.op.var]

        if formula.op.type == "LAMBDA":
            isOnlyProbabilistic = True

    formula.vars = set(vars)
    formula.closedVars = set(closedVars)
    formula.isOnlyProbabilistic = isOnlyProbabilistic

    return vars


def getAST(code):

    try:
        # parse the formula
        formula = grammar().parseString(code)[0]

    except ParseException, err:
        print err.line
        print " " * (err.column - 1) + "^"
        print err
        return -1

    # add variable and probabilistic information
    vars = addInfo(formula)
    # we disallow duplicate variables and open
    if len(vars) != len(formula.vars):
        print("No duplicate variables allowed.")
        return -1
    if not formula.isClosed():
        print("No open formulas allowed.")
        return -1

    print("Parsed formula " + str(formula))
    return formula


def readFormula(filename):

    try:
        f = open(filename)
        lines = f.read().split('\n')
        f.close()
    except IOError:
        print("File '" + filename + "' not found")
        return [-1]

    formulas = []

    for i in range(0, len(lines)):
        line = lines[i]
        if len(line) > 0 and not line.startswith('%'):
            formula = getAST(line)
            formula.name = os.path.splitext(os.path.basename(filename))[0] + str(i+1)
            formulas += [formula]

    return formulas
