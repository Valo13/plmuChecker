import argparse
from TSReader import *
from FormulaReader import *
import plmuChecker
import BESSolver
import RESSolver
import ParityGameCreator


def main():
    parser = argparse.ArgumentParser(description='check a plmu formula on a PLTS')
    parser.add_argument("-e", "--equations", help="solve via RES", action="store_true")
    parser.add_argument("-l", "--local", help="create local RES", action="store_true")
    parser.add_argument("-d", "--depGraph", help="create and use dependency graph for substitution", action="store_true")
    parser.add_argument("-o", "--order", help="solve a RES in an efficient order using SSC's, includes -l and -d", action="store_true")
    parser.add_argument("-p", "--paritygame", help="create a paritygame (if also -e, create via RES)", action="store_true")
    parser.add_argument("-s", "--store", help="store intermediate results such as a BES", action="store_true")
    parser.add_argument("-v", "--verbose", help="display info", action="store_true")
    parser.add_argument('-r', "--runs", default=[1], action='store', nargs=1, type=int, help='run the same problem multiple times and give the average running time')
    parser.add_argument('model', help='the model to check a formula on (path to file)')
    parser.add_argument('formulas', help='the formula(s) to check on a model (path to file)')
    args = parser.parse_args()

    model = readTS(args.model)
    formulas = readFormula(args.formulas)
    # initiate clock
    numberOfRuns = args.runs[0]

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
                    creationTimes = []
                    solveTimes = []
                    value = None
                    for i in range(numberOfRuns):
                        # do the model checking
                        print("Computing result for formula " + str(formula))
                        if args.equations:
                            result = RESSolver.initRESSolver(model, formula, args.store, args.verbose, args.local or args.order, args.depGraph or args.order, args.order)
                            value = result[0]
                            creationTimes += [result[1]]
                            solveTimes += [result[2]]
                        else:
                            result = plmuChecker.checkNaiveInit(model, formula, args.verbose)
                            value = result[0]
                            solveTimes += [result[1]]

                        if result is None:
                            print("Could not compute result for formula " + str(formula) + '\n')
                            break

                        if hasLabelOperator:
                            value = value * model.labelFactor

                    print("The result of " + str(formula) + " is: " + str(value))
                    if args.equations:
                        print("Creation time: " + str(sum(creationTimes) / numberOfRuns) + ' seconds')
                    print("Running time: " + str(sum(solveTimes)/numberOfRuns) + ' seconds')
                    if numberOfRuns > 1:
                        print("Individual timings: " + str(solveTimes))
                    print('\n')


main()
