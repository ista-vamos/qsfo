#!/usr/bin/env python3
import sys

from qsfo.monitoring.trace import SignalsTrace
from qsfo.parser import Parser
from qsfo.polyhedron import solve_for_variable, FRACTIONS_PREC, Polyhedron

from sympy import Eq, solve


if __name__ == "__main__":
    parser = Parser()
    formula = parser.parse(sys.argv[1])
    trace_file = sys.argv[2]
    # FIXME: use argparse...
    if len(sys.argv) > 3:
        sampling = float(sys.argv[3])
    else:
        sampling = None

    print("--- Parsed formula ---")
    print(formula)
    print("------")
    print("Free variables: ", set(map(str, formula.free_variables())))
    print("Bound variables: ", set(map(str, formula.bound_variables())))
    print("Signals: ", set(map(lambda s: s.name(), formula.signals())))

    if trace_file.endswith('.csv'):
        trace = SignalsTrace.from_csv_file(trace_file, sampling, signals=[s.name() for s in formula.signals()])
    else:
        trace = SignalsTrace.from_signal_file(trace_file)
   #print("--- Trace ---")
   #print(trace)
   #print("--- Piecewise signals ---")
   #tv = trace.timevar()
   #for v in trace.header():
   #    if v == tv:
   #        continue
   #
   #    print(f"For {v}:")
   #    print([str(p) for p in trace.piecewise_linear_signal(v)])
   #print("--- ---")

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
        for sig in mon_signal:
            print("Robustness:")
            for s in sig:
                #C = [f'{(c.lhs/FRACTIONS_PREC).evalf()} {c.rel_op} {(c.rhs/FRACTIONS_PREC).evalf()}' for c in s.constraints()]
                #print(f'  {sig.var()} ==> {C}')

                # get the defining equality for the robustness value
                var = sig.var()
                eq = [c for c in s.constraints() if isinstance(c, Eq) and c.has(var)]
                if len(eq) == 1:
                    S = solve(eq, var)
                    assert isinstance(S, dict), (eq, S)
                    C  = Polyhedron([c.subs(var, S[var]) for c in s.constraints() if not isinstance(c, Eq)] ).reduce().simplify_constraints()
                    C = C.intersection(Polyhedron([Eq(var, S[var])]))
                    print(f'  {var} ==> {C}')
                    continue
                else:
                    print(f'  {var} ==> {s.simplify_constraints()}')
