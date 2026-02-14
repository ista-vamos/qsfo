#!/usr/bin/env python3
import sys
import argparse

from qsfo.monitoring.trace import SignalsTrace
from qsfo.parser import Parser
from qsfo.polyhedron import Interval
from csv import writer as csv_writer

from sympy import Eq, solve, Symbol, FiniteSet, And as AND


def parse_cmd():
    parser = argparse.ArgumentParser(description="Monitoring qsfo.")

    # Required positional arguments
    parser.add_argument("formula", type=str, help="qsfo formula (required)")
    parser.add_argument("input", type=str, help="Path to the input file")

    # Optional arguments
    parser.add_argument(
        "--samp",
        type=float,
        default=None,
        help="Optional sampling interval (float) for inputs that do not contain the time variable `t` explicitely",
    )
    parser.add_argument(
        "--horizon", type=float, default=None, help="Optional horizon value (float)"
    )

    parser.add_argument(
        "--csv", type=str, default=None, help="Write output to the csv file"
    )

    parser.add_argument(
        "--csv-with-robustness",
        action="store_true",
        default=False,
        help="Write robustness signal into CSV (makes sense only if the len of the signal is always 1)",
    )

    parser.add_argument(
        "--csv-no-buffering",
        action="store_true",
        default=True,
        help="Write output to CSV immediately, without buffering.",
    )

    parser.add_argument(
        "--no-stdout",
        action="store_true",
        default=False,
        help="Write not output to stdout",
    )

    return parser.parse_args()


def poly_as_intv(poly):
    intv = AND(*poly.constraints()).as_set()
    if isinstance(intv, FiniteSet):
        t_start = t_end = next(iter(intv))
        l_open, r_open = False, False
    else:
        t_start, t_end = intv.start, intv.end
        l_open, r_open = intv.left_open, intv.right_open

    return Interval(t_start, t_end, l_open, r_open)


if __name__ == "__main__":
    args = parse_cmd()
    parser = Parser()
    formula = parser.parse(args.formula)

    if not args.no_stdout:
        print("--- Parsed formula ---")
        print(formula)
        print("------")
        print("Free variables: ", set(map(str, formula.free_variables())) or "∅")
        print("Bound variables: ", set(map(str, formula.bound_variables())) or "∅")
        print("Signals: ", set(map(lambda s: str(s.name()), formula.signals())))

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
    if args.csv is None:
        csv = None
    else:
        csvfile = open(args.csv, "w")
        csv = csv_writer(csvfile)
        if args.csv_with_robustness:
            csv.writerow(
                ["intv_start", "intv_end", "expr", "r_start", "r_end", "t_r", "t_m"]
            )
        else:
            csv.writerow(["intv_start", "intv_end", "t_r", "t_m"])

    if sys.argv[0].startswith("bool"):
        raise NotImplementedError("Boolean monitoring is broken atm")
    # from qsfo.monitoring.boolean import Formula2Polyhedra
    #
    # f2ph = Formula2Polyhedra()
    # mon_signal = f2ph.translate(formula, trace)
    # print("Monitoring signal:")
    # for sig in mon_signal:
    #     print(sig)
    else:
        from qsfo.monitoring.quantitative import OfflineMonitor

        mon = OfflineMonitor(formula, trace, args.horizon)
        mon_signal = mon.signal_with_stats()
        if not args.no_stdout:
            print("Monitoring signal:")
        for (sig, t_r, t_m), intv in mon_signal:
            intv = poly_as_intv(intv)
            if not args.no_stdout:
                print(f"####  t ∈ {intv} (computed in {t_r + t_m} sec)")

            if csv and not args.csv_with_robustness:
                csv.writerow(
                    [
                        intv.start,
                        intv.end,
                        t_r,
                        t_m,
                    ]
                )
                if args.csv_no_buffering:
                    csvfile.flush()

            if args.no_stdout and not (csv and args.csv_with_robustness):
                # nothing to do
                continue

            for expr, sub_intv in sig:
                # get the defining equality for the robustness value
                if not args.no_stdout:
                    print(f"  {expr} @ {sub_intv}")

                if csv and args.csv_with_robustness:
                    if isinstance(sub_intv, FiniteSet):
                        t_start = t_end = next(iter(sub_intv))
                    else:
                        t_start, t_end = sub_intv.start, sub_intv.end

                    t = t_start
                    r_start = expr if isinstance(expr, float) else eval(str(expr))
                    t = t_end
                    r_end = expr if isinstance(expr, float) else eval(str(expr))
                    csv.writerow(
                        [
                            t_start,
                            t_end,
                            f"'{expr}'",
                            r_start,
                            r_end,
                            t_r,
                            t_m,
                        ]
                    )

                    if args.csv_no_buffering:
                        csvfile.flush()

            if not args.no_stdout:
                print("")
