#!/usr/bin/env python3
import sys

from qsfo.monitoring.trace import SignalsTrace
from qsfo.parser import Parser
from qsfo.polyhedron import simplify_constraints

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

    if sys.argv[0].startswith("bool"):
        from qsfo.monitoring.boolean import Formula2Polyhedra

        f2ph = Formula2Polyhedra()
        mon_signal = f2ph.translate(formula, trace)
        print("Monitoring signal:")
        for sig in mon_signal:
            print(sig)
    else:
        from qsfo.monitoring.quantitative import OfflineMonitor

        mon = OfflineMonitor(formula, trace)
        mon_signal = mon.signal()
        print("Monitoring signal:")
        for sigvar, sig in mon_signal:
            print("Robustness:")
            for s in sig:
                print(f'  {sigvar} ==> {s}')
