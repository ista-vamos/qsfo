from os.path import dirname, join as pathjoin
from sys import path as syspath

syspath.append(pathjoin(dirname(__file__), ".."))

from qsfo.parser import Parser
from qsfo.monitoring.trace import SignalsTrace
from qsfo.monitoring.boolean import Formula2Polyhedra
from qsfo.polyhedron import simplify_constraints

if __name__ == "__main__":
    formula = Parser().parse(r"forall c: f(c) \le g(t)")

    signal = SignalsTrace.from_list(
        [
            ["t", "f", "g"],
            [0, 3, 6],
            [1, 4, 7],
            [2, 5, 8],
            # [ 3,   4,   8],
            # [ 4,   3,   8],
            # [ 3,   5,   1],
        ]
    )
    print(formula)
    print("Signal f:")
    for seg in signal.piecewise_linear_signal("f"):
        print("  ", seg.time_bounds(), " ==> ", seg)
    print("Signal g:")
    for seg in signal.piecewise_linear_signal("g"):
        print("  ", seg.time_bounds(), " ==> ", seg)

    mon_signal = Formula2Polyhedra().translate(formula, signal)
    print("Mon signal len: ", len(mon_signal))
    print("Result:")
    for sig in mon_signal:
        print(sig)
