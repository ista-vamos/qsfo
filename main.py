#!/usr/bin/env python3
import sys

from qsfo.parser import Parser

if __name__ == "__main__":
    parser = Parser()
    formula = parser.parse(sys.argv[1])
    print(formula.pretty())
