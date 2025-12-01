#!/usr/bin/env python3
import sys
import argparse

from qsfo.monitoring.trace import SignalsTrace
from qsfo.parser import Parser
from qsfo.polyhedron import solve_for_variable, FRACTIONS_PREC, Polyhedron

from sympy import Eq, solve


def parse_cmd():
    parser = argparse.ArgumentParser(description="Monitoring qsfo.")

    # Required positional arguments
    parser.add_argument("formula", type=str, help="qsfo formula (required)")
    parser.add_argument("input", type=str, help="Path to the input file")

    # Optional arguments
    parser.add_argument(
        "--samp", type=float, default=None, help="Optional sampling interval (float)"
    )
    parser.add_argument(
        "--horizon", type=float, default=None, help="Optional horizon value (float)"
    )

    return parser.parse_args()


if __name__ == "__main__":
    args = parse_cmd()
    parser = Parser()
    formula = parser.parse(args.formula)

    print("--- Parsed formula ---")
    print(formula)
    print("------")
    print("Free variables: ", set(map(str, formula.free_variables())))
    print("Bound variables: ", set(map(str, formula.bound_variables())))
    print("Signals: ", set(map(lambda s: s.name(), formula.signals())))

    trace_file = args.input
    if trace_file.endswith(".csv"):
        trace = SignalsTrace.from_csv_file(
            trace_file, args.samp, signals=[s.name() for s in formula.signals()]
        )
    else:
        trace = SignalsTrace.from_signal_file(trace_file)
    # print("--- Trace ---")
    # print(trace)
    # print("--- Piecewise signals ---")
    # tv = trace.timevar()
    # for v in trace.header():
    #    if v == tv:
    #        continue
    #
    #    print(f"For {v}:")
    #    print([str(p) for p in trace.piecewise_linear_signal(v)])
    # print("--- ---")

    if sys.argv[0].startswith("bool"):
        raise NotImplementedError("Boolean monitoring is broken atm")
        from qsfo.monitoring.boolean import Formula2Polyhedra

        f2ph = Formula2Polyhedra()
        mon_signal = f2ph.translate(formula, trace)
        print("Monitoring signal:")
        for sig in mon_signal:
            print(sig)
    else:
        from qsfo.monitoring.quantitative import OfflineMonitor

        mon = OfflineMonitor(formula, trace, args.horizon)
        mon_signal = mon.signal()
        print("Monitoring signal:")
        for sig in mon_signal:
            print("Robustness:")
            for s in sig:
                # C = [f'{(c.lhs/FRACTIONS_PREC).evalf()} {c.rel_op} {(c.rhs/FRACTIONS_PREC).evalf()}' for c in s.constraints()]
                # print(f'  {sig.var()} ==> {C}')

                # get the defining equality for the robustness value
                print(f"  {s[0]} @ {s[1]}")
