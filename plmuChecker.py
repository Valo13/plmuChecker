import copy


MAXITER = 100
variables = {}
model = None


# naive method, approximates fixpoints
def checkNaive(formula, state):
    global variables

    if formula.type == "NULLARY":
        if formula.op.type == "VAL":
            return formula.op.val
        elif formula.op.type == "VAR":
            return variables[formula.op.var][state]
    elif formula.type == "UNARY":
        if formula.op.type == "DIAMOND":
            val = 0.0
            for t in model.outgoing(state, formula.op.action):
                sum = 0.0
                for s in t.enddist:
                    sum += t.enddist[s] * checkNaive(formula.subformulas[0], s)
                if sum > val:
                    val = sum
            return val
        elif formula.op.type == "BOX":
            val = 1.0
            for t in model.outgoing(state, formula.op.action):
                sum = 0.0
                for s in t.enddist:
                    sum += t.enddist[s] * checkNaive(formula.subformulas[0], s)
                if sum < val:
                    val = sum
            return val
        elif formula.op.type in ["LEASTFP", "GREATESTFP"]:
            i = 0
            var = formula.op.var
            newVars = ([0.0] if formula.op.type == "LEASTFP" else [1.0]) * model.numstates
            while variables[var] != newVars and i < MAXITER:
                variables[var] = copy.copy(newVars)
                for s in range(0, model.numstates):
                    newVars[s] = checkNaive(formula.subformulas[0], s)
                print("Iteration " + str(i) + ": " + str(variables))
                i += 1
            return variables[var][state]
    elif formula.type == "BINARY":
        val1 = checkNaive(formula.subformulas[0], state)
        val2 = checkNaive(formula.subformulas[1], state)
        if formula.op.type == "AND":
            return min(val1, val2)
        if formula.op.type == "OR":
            return max(val1, val2)
        if formula.op.type == "PRODUCT":
            return val1 * val2
        if formula.op.type == "COPRODUCT":
            return val1 + val2 - val1 * val2
        if formula.op.type == "TCOSUM":
            return max(0.0, val1 + val2 - 1.0)
        if formula.op.type == "TSUM":
            return min(1.0, val1 + val2)
        if formula.op.type == "LAMBDA":
            return formula.op.val * val1 + (1.0 - formula.op.val) * val2


def checkNaiveInit(ts, formula):
    global model, variables
    model = ts
    variables = {var: [] for var in formula.vars}
    return checkNaive(formula, model.initstate)
