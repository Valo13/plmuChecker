import argparse
from TSReader import *
from FormulaReader import *
import plmuChecker
import BESSolver
import RESSolver


def main():
    parser = argparse.ArgumentParser(description='check a plmu formula on a PLTS')
    parser.add_argument("-e", "--equations", help="solve via BES or RES", action="store_true")
    parser.add_argument("-s", "--store", help="store intermediate results such as a BES", action="store_true")
    parser.add_argument('model', help='the model to check a formula on (path to file)')
    parser.add_argument('formulas', help='the formula(s) to check on a model (path to file)')
    args = parser.parse_args()

    model = readTS(args.model)
    formulas = readFormula(args.formulas)

    for formula in formulas:
        if model != -1 and formula != -1:
            isOnlyProbabilistic = model.isProbabilistic or formula.isOnlyProbabilistic

            # do the checking
            result = None
            if args.equations:
                if isOnlyProbabilistic:
                    result = RESSolver.initRESSolver(model, formula, args.store)
                else:
                    result = BESSolver.initBESSolver(model, formula, args.store)
            else:
                result = plmuChecker.checkNaiveInit(model, formula)

            if result is not None:
                print("The result of " + str(formula) + " is: " + str(result))
            else:
                print("Could not compute result for formula " + str(formula))

main()
