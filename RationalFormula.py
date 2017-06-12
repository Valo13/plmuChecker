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
            return any([subop.containsVar(var) for subop in self.operands])

    # get (value, {variable: its scalar})
    # for instance 0.5 + 0.2*X + Y + 0.6*Z returns (0.5, {X: 0.2, Y: 1, Z: 0.6})
    # assumes normal form and additions of scalar*var combined for same var
    def getVariableScalar(self):
        if self.op.type == "VAL":
            return self.op.val, {}
        elif self.op.type == "VAR":
            return 0.0, {self.op.var: 1}
        elif self.op.type == "MULTIPLY":
            var = [term.op.var for term in self.operands if term.op.type == "VAR"][0]
            val = [term.op.val for term in self.operands if term.op.type == "VAL"][0]
            return 0.0, {var: val}
        elif self.op.type == "ADD":
            value = 0.0
            scalars = {}
            for operand in self.operands:
                val, scalar = operand.getVariableScalar()
                if val > 0:
                    value = val
                scalars.update(scalar)
            return value, scalars

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

    def __str__(self):
        if self.op.type == "VAL":
            return str(self.op.val)
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

    def __repr__(self):
        if self.op.type == "VAL":
            return "VAL(" + str(self.op.val) + ')'
        elif self.op.type == "VAR":
            return "VAR(" + self.op.var + ")"
        else:
            return self.op.type + "(" + ", ".join(repr(operand) for operand in self.operands) + ")"


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


def variableFormula(var):
    return RationalFormulaNode(RationalOperatorNode("VAR", var))


# substitutes a formula 'new' for a variable 'var'
def substituteVar(formula, var, new):
    if formula.op.type == "VAR" and formula.op.var == var:
        return copy.deepcopy(new)
    else:
        for i in range(len(formula.operands)):
            formula.operands[i] = substituteVar(formula.operands[i], var, new)
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


# returns whether operand1 is definitely worse than operand2 when put together in opType
def isWorseOperand(operand1, operand2, opType):
    val1, scalar1 = operand1.getVariableScalar()
    val2, scalar2 = operand2.getVariableScalar()
    if opType == "MAXIMUM":
        if val1 > val2:
            return False
        for var in scalar1:
            if var not in scalar2:
                return False
        for var in scalar2:
            if var in scalar1 and scalar1[var] > scalar2[var]:
                return False
    else:
        if val2 > val1:
            return False
        for var in scalar2:
            if var not in scalar1:
                return False
        for var in scalar1:
            if var in scalar2 and scalar2[var] > scalar1[var]:
                return False
    return True


def simplify(formula, afterNormalForm=False):
    for i in range(len(formula.operands)):
        formula.operands[i] = simplify(formula.operands[i], afterNormalForm)

    # print("simplifying " + str(formula))

    if formula.type != "NULLARY":
        opType = formula.op.type
        newOperands = []

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
        values = [operand.op.val for operand in newOperands if operand.op.type == "VAL"]
        nonValues = [operand for operand in newOperands if operand.op.type != "VAL"]

        # before: resolve zero-values
        if 0.0 in values and opType in ["MULTIPLY", "MINIMUM"]:
            # print("found zero value: " + str(valueFormula(0.0)))
            return valueFormula(0.0)
        elif 1.0 in values and opType == "MAXIMUM":
            # print("found zero value: " + str(valueFormula(1.0)))
            return valueFormula(1.0)
        else:
            value = values[0] if values else None
            # apply operator
            if len(values) > 1:
                value = applyOperator(opType, values)
                valueOperand = valueFormula(value)
                if len(nonValues) == 0:
                    # print("found only values: " + str(valueOperand))
                    return valueOperand
                else:
                    newOperands = [valueOperand] + nonValues

            # after: resolve unit elements
            if (value == 0.0 and opType == "ADD") or (value == 1.0 and opType == "MULTIPLY") \
                    or (opType == "SUBTRACT" and newOperands[1].op.type == "VAL" and newOperands[1].op.val == 0.0):
                if len(nonValues) == 1:
                    # print("found unit value with single nonvalue: " + str(nonValues[0]))
                    return nonValues[0]
                else:
                    newOperands = nonValues

            # some simplifications assuming normal form
            if afterNormalForm:
                # combine additions of variables (assumes normal form)
                if opType == "ADD":
                    multOperands = [operand for operand in newOperands if operand.op.type == "MULTIPLY"]
                    nonMultOperands = [operand for operand in newOperands if operand.op.type != "MULTIPLY"]
                    if len(multOperands) > 1:
                        varScalars = {}
                        for mult in multOperands:
                            var = [term.op.var for term in mult.operands if term.op.type == "VAR"][0]
                            val = [term.op.val for term in mult.operands if term.op.type == "VAL"][0]
                            if var in varScalars:
                                varScalars[var] += val
                            else:
                                varScalars[var] = val

                        newOperands = nonMultOperands \
                                      + [RationalFormulaNode(RationalOperatorNode("MULTIPLY"),
                                                             [valueFormula(varScalars[var]), variableFormula(var)]) for var in varScalars]

                # remove duplicate and worse operands in minimum and maximum
                if opType in ["MINIMUM", "MAXIMUM"]:
                    # remove duplicates
                    trimmedOperands = []
                    for operand in newOperands:
                        alreadyFound = False
                        for trimmedOperand in trimmedOperands:
                            if operand == trimmedOperand:
                                alreadyFound = True
                        if not alreadyFound:
                            trimmedOperands += [operand]
                    newOperands = trimmedOperands
                    # if we are not dealing with MAXIMUM with MINIMUM terms, remove terms that are certainly worse
                    # ALTER THIS WHEN USING TCOSUM AND TSUM
                    if not any([operand.op.type == "MINIMUM" for operand in newOperands]):
                        worseOperands = []
                        for operand1 in newOperands:
                            for operand2 in newOperands:
                                if operand1 != operand2 and operand1 not in worseOperands and operand2 not in worseOperands:
                                    if isWorseOperand(operand1, operand2, opType):
                                        worseOperands += [operand1]
                                    elif isWorseOperand(operand2, operand1, opType):
                                        worseOperands += [operand2]
                        newOperands = [operand for operand in newOperands if operand not in worseOperands]
                        if len(newOperands) == 1:
                            return newOperands[0]

        formula.operands = newOperands

    # print("result: " + str(formula))
    return formula


# applies distribution in formula over subOpType
# for instance, formula = a*(b+c), subOpType = ADD, then result is a*b + a*c
# also works for multiary cases
# for instance formula = a*(b+c)*(d+e), subOpType = ADD then result is a*b*d + a*c*d + a*b*e + a*c*e
# returns None if no distribution necessary
def distribute(formula, subOpType):
    topop = formula.op
    distop = RationalOperatorNode(subOpType)
    toDistribute = [subf for subf in formula.operands if subf.op.type == subOpType]
    # if there is nothing to distribute over, we are immediately done
    if not toDistribute:
        return None
    otherOperands = [subf for subf in formula.operands if subf.op.type != subOpType]
    distoperands = [[] for i in range(len(toDistribute))]

    # collect all operands of the operands with subOpType
    for i in range(len(toDistribute)):
        distoperands[i] = toDistribute[i].operands

    def makeCombinations(i):
        if i < len(distoperands):
            combis = makeCombinations(i + 1)
            newCombis = []
            for combi in combis:
                for operand in distoperands[i]:
                    newCombis += [[operand] + combi]
            return newCombis
        else:
            return [[]]

    # create all combinations of these operands such that they have one operand per subOpType subformula
    combinations = makeCombinations(0)

    # create the new formula
    newOperands = [RationalFormulaNode(topop, otherOperands + combi) for combi in combinations]
    return RationalFormulaNode(distop, newOperands)


# changes a rational formula to normal form: max{min{sum{p*X} + c*c'}}
# requirement: operators have been flattened (formula is simplified
def toNormalForm(formula):
    for i in range(len(formula.operands)):
        formula.operands[i] = toNormalForm(formula.operands[i])

    # print("bringing " + str(formula) + " to normal form")

    if formula.type is "NULLARY":
        # print("is NULLARY")
        return formula

    # distribute over ADD
    if formula.op.type == "MULTIPLY":
        result = distribute(formula, "ADD")
        if result:
            formula = result
            for i in range(len(formula.operands)):
                formula.operands[i] = toNormalForm(formula.operands[i])
    # distribute over MINIMUM
    if formula.op.type in ["ADD", "MULTIPLY"]:
        result = distribute(formula, "MINIMUM")
        if result:
            formula = result
            for i in range(len(formula.operands)):
                formula.operands[i] = toNormalForm(formula.operands[i])
    # distribute over MAXIMUM
    if formula.op.type in ["MINIMUM", "ADD", "MULTIPLY"]:
        result = distribute(formula, "MAXIMUM")
        if result:
            formula = result
            for i in range(len(formula.operands)):
                formula.operands[i] = toNormalForm(formula.operands[i])

    # print("result: " + str(formula))

    return formula
