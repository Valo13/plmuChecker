import argparse
import time
from TSReader import *
from FormulaReader import *
import plmuChecker
import BESSolver
import RESSolver
import ParityGameCreator


def main():
    parser = argparse.ArgumentParser(description='check a plmu formula on a PLTS')
    parser.add_argument("-e", "--equations", help="solve via BES or RES", action="store_true")
    parser.add_argument("-l", "--local", help="create local RES", action="store_true")
    parser.add_argument("-p", "--paritygame", help="solve via paritygame", action="store_true")
    parser.add_argument("-s", "--store", help="store intermediate results such as a BES", action="store_true")
    parser.add_argument("-v", "--verbose", help="display info", action="store_true")
    parser.add_argument('model', help='the model to check a formula on (path to file)')
    parser.add_argument('formulas', help='the formula(s) to check on a model (path to file)')
    args = parser.parse_args()

    model = readTS(args.model)
    formulas = readFormula(args.formulas)
    elapsedTime = time.clock()
    for formula in formulas:
        if model != -1 and formula != -1:
            hasLabelOperator = bool(formula.getSubFormulas(["LABEL"]))
            if hasLabelOperator and formula.getSubFormulas(["PRODUCT", "COPRODUCT", "TCOSUM", "TSUM"]):
                print("The operators (co)product and truncated (co)sum are not supported when using the label operator")
            else:
                isOnlyProbabilistic = model.isProbabilistic or formula.isOnlyProbabilistic
                if args.paritygame:
                    print("Creating parity game for formula " + str(formula))
                    ParityGameCreator.initParityGameCreator(model, formula, args.equations, args.store, args.verbose, isOnlyProbabilistic)
                else:
                    # do the model checking
                    print("Computing result for formula " + str(formula))
                    if args.equations:
                        if isOnlyProbabilistic:
                            result = RESSolver.initRESSolver(model, formula, args.store, args.verbose, args.local)
                        else:
                            result = BESSolver.initBESSolver(model, formula, args.store, args.verbose)
                    else:
                        result = plmuChecker.checkNaiveInit(model, formula, args.verbose)

                    if hasLabelOperator:
                        result = result * model.labelFactor

                    elapsedTime = time.clock() - elapsedTime
                    if result is not None:
                        print("The result of " + str(formula) + " is: " + str(result))
                        print("Time elapsed: " + str(elapsedTime) + ' seconds\n')
                    else:
                        print("Could not compute result for formula " + str(formula) + '\n')

main()
