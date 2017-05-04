import copy


# defines a rational formula and operators on it
# for now we do not allow formulas generated using plmu operators PRODUCT, COPRODUCT, TCOSUM and TSUM
#   so the operators + (ADD), * (MULTIPLY), min (MINIMUM) and max (MAXIMUM) are allowed
#   all these operators are defined as multiary operators
# rather: f = p | X | max(f,f) | min(f,f) | sum{p*f}

class RationalFormulaNode:

    def __init__(self, operator, operands=None):
        self.op = operator
        if operands is None:
            operands = []
        self.operands = operands
        if len(operands) == 0:  # in case of VAL, VAR
            self.type = "NULLARY"
        elif operator.type == "SUBTRACT":
            self.type = "BINARY"
        else:  # possible in case of ADD, MULTIPLY, MAXIMUM and MINIMUM (2 or more operands)
            self.type = "MULTIARY"

    def containsVar(self, var):
        if self.type == "NULLARY":
            if self.op.type == "VAR" and self.op.var == var:
                return True
            else:
                return False
        else:
            for subop in self.operands:
                return any(subop.containsVar(var))

    def __eq__(self, other):
        if isinstance(other, self.__class__):
            selfoperands = sorted(self.operands)
            otheroperands = sorted(other.operands)
            return self.op == other.op \
                   and len(selfoperands) == len(otheroperands) \
                   and all([selfoperands[i] == otheroperands[i] for i in range(len(selfoperands))])
        return NotImplemented

    def __ne__(self, other):
        if isinstance(other, self.__class__):
            return not self == other
        return NotImplemented

    def __repr__(self):
        if self.op.type == "VAL":
            return '[' + str(self.op.val) + ']'
        elif self.op.type == "VAR":
            return self.op.var
        elif self.op.type == "ADD":
            return "(" + " + ".join(str(operand) for operand in self.operands) + ")"
        elif self.op.type == "SUBTRACT":
            return "(" + str(self.operands[0]) + " - " + str(self.operands[1]) + ")"
        elif self.op.type == "MULTIPLY":
            return "(" + " * ".join(str(operand) for operand in self.operands) + ")"
        elif self.op.type == "MINIMUM":
            return "min(" + ", ".join(str(operand) for operand in self.operands) + ")"
        elif self.op.type == "MAXIMUM":
            return "max(" + ", ".join(str(operand) for operand in self.operands) + ")"


class RationalOperatorNode:

    def __init__(self, type, varorval=None):
        self.type = type
        if type == "VAR":
            self.var = varorval
        else:
            self.val = varorval

    def __eq__(self, other):
        if isinstance(other, self.__class__):
            return self.type == other.type \
                   and (self.var == other.var if self.type == "VAR" else True)\
                   and (self.val == other.val if self.type == "VAL" else True)
        return NotImplemented

    def __ne__(self, other):
        if isinstance(other, self.__class__):
            return not self == other
        return NotImplemented


def valueFormula(value):
    return RationalFormulaNode(RationalOperatorNode("VAL", value))


# substitutes a formula 'new' for a variable 'var'
def substituteVar(formula, var, new):
    if formula.op.type == "VAR" and formula.op.var == var:
        # not using copy is not wrong, but it is ugly
        # without it this will also substitute in equations below sometimes due to same reference
        return copy.deepcopy(new)
    else:
        for i in range(0, len(formula.subformulas)):
            formula.subformulas[i] = substituteVar(formula.subformulas[i], var, new)
    return formula


def applyOperator(opType, values):
    if opType == "ADD":
        return sum(values)
    elif opType == "SUBTRACT":
        return values[0] - values[1]
    elif opType == "MULTIPLY":
        prod = 1
        for value in values:
            prod *= value
        return prod
    elif opType == "MINIMUM":
        return min(values)
    elif opType == "MAXIMUM":
        return max(values)


def simplify(formula, doFlattening=True):
    for i in range(0, len(formula.operands)):
        formula.operands[i] = simplify(formula.operands[i], doFlattening)

    if formula.type != "NULLARY":
        opType = formula.op.type
        newOperands = []

        if doFlattening:
            # flatten operators
            if opType in ["ADD", "MULTIPLY", "MINIMUM", "MAXIMUM"]:
                for operand in formula.operands:
                    if operand.type != "NULLARY" and operand.op.type == opType:
                        newOperands += operand.operands
                    else:
                        newOperands += [operand]
            else:
                newOperands = formula.operands

        # apply operator to values
        values = [operand.op.val for operand in formula.operands if operand.op.type == "VAL"]
        nonValues = [operand for operand in formula.operands if operand.op.type != "VAL"]

        # before: resolve zero-values
        if 0.0 in values and opType in ["MULTIPLY", "MINIMUM"]:
            return valueFormula(0.0)
        elif 1.0 in values and opType == "MAXIMUM":
            return valueFormula(1.0)
        else:
            value = values[0] if values else None
            # apply operator
            if len(values) > 1:
                value = applyOperator(opType, values)
                valueOperand = valueFormula(value)
                if len(nonValues) == 0:
                    return valueOperand
                else:
                    newOperands = nonValues + [valueOperand]

            # after: resolve unit elements
            if (value == 0.0 and opType in ["ADD", "MAXIMUM"]) \
                    or (value == 1.0 and opType in ["MULTIPLY", "MINIMUM"]) \
                    or (opType == "SUBTRACT" and newOperands[1].op.type == "VAL" and newOperands[1].op.val == 0.0):
                if len(nonValues) == 1:
                    return nonValues[0]
                else:
                    newOperands = nonValues

        formula.operands = newOperands

    return formula


# applies distribution in formula over subOpType
# for instance, formula = a*(b+c), subOpType = ADD, then result is a*b + a*c
# also works for multiary cases
# for instance formula = a*(b+c)*(d+e), subOpType = ADD then result is a*b*d + a*c*d + a*b*e + a*c*e
def distribute(formula, subOpType):
    topop = formula.op
    distop = RationalOperatorNode(subOpType)
    toDistribute = [subf for subf in formula.subformulas if subf.op.type == subOpType]
    # if there is nothing to distribute over, we are immediately done
    if not toDistribute:
        return formula
    otherOperands = [subf for subf in formula.subformulas if subf.op.type != subOpType]
    distoperands = []

    # collect all operands of the subformulas with subOpType
    for i in range(len(toDistribute)):
        distoperands[i] = toDistribute[i].operands

    def makeCombinations(i):
        if i < len(distoperands) - 1:
            combis = makeCombinations(i + 1)
            newCombis = []
            for combi in combis:
                for operand in distoperands[i]:
                    newCombis += [[operand] + combi]
            return newCombis
        else:
            return []

    # create all combinations of these operands such that they have one operand per subOpType subformula
    combinations = makeCombinations(0)

    # create the new formula
    newOperands = [RationalFormulaNode(topop, otherOperands + combi) for combi in combinations]
    return RationalFormulaNode(distop, newOperands)


# changes a rational formula to normal form: max{min{sum{p*X} + c*c'}}
# requirement: operators have been flattened (formula is simplified
def toNormalForm(formula):
    for i in range(0, len(formula.operands)):
        formula.operands[i] = toNormalForm(formula.operands[i])

    if formula.type is "NULLARY":
        return formula

    # distribute over ADD
    if formula.op.type == "MULTIPLY":
        formula = distribute(formula, "ADD")
    # distribute over MINIMUM
    if formula.op.type in ["ADD", "MULTIPLY"]:
        formula = distribute(formula, "MINIMUM")
    # distribute over MAXIMUM
    if formula.op.type in ["MINIMUM", "ADD", "MULTIPLY"]:
        formula = distribute(formula, "MAXIMUM")

    return formula