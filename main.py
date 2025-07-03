#!/usr/bin/env python3
import sys

from qsfo.parser import Parser

if __name__ == "__main__":
    parser = Parser()
    formula = parser.parse(sys.argv[1])
    print("--- Parsed formula ---")
    print(formula)
    print("------")
    print("Free variables: ", set(map(str, formula.free_variables())))
    print("Bound variables: ", set(map(str, formula.bound_variables())))
