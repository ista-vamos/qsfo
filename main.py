#!/usr/bin/env python3
import sys

from qsfo.monitoring.trace import SignalsTrace
from qsfo.parser import Parser
from qsfo.monitoring.boolean import Formula2Polyhedra

if __name__ == "__main__":
    parser = Parser()
    formula = parser.parse(sys.argv[1])
    trace = SignalsTrace.from_signal_file(sys.argv[2])
    print("--- Parsed formula ---")
    print(formula)
    print("------")
    print("Free variables: ", set(map(str, formula.free_variables())))
    print("Bound variables: ", set(map(str, formula.bound_variables())))
    print("--- Trace ---")
    print(trace)
    print("--- Piecewise signals ---")
    tv = trace.timevar()
    for v in trace.header():
        if v == tv:
            continue

        print(f"For {v}:")
        print([str(p) for p in trace.piecewise_linear_signal(v)])
    print("--- ---")

    f2ph = Formula2Polyhedra()
    f2ph.translate(formula)
