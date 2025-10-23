from os.path import dirname, join as pathjoin
from sys import path as syspath

syspath.append(pathjoin(dirname(__file__), "../.."))

from qsfo.parser import Parser
from qsfo.monitoring.trace import SignalsTrace
from qsfo.monitoring.boolean import Formula2Polyhedra

if __name__ == "__main__":
    formula = Parser().parse(r"f(t) \le g(t)")

    signal = SignalsTrace.from_list(
        [
            ["t", "f", "g"],
            [0, 2, 2],
            [1, 3, 4],
        ]
    )
    print(formula)
    mon_signal = Formula2Polyhedra().translate(formula, signal)
    for sig in mon_signal:
        print(sig)
