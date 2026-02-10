from os.path import dirname, join as pathjoin
from sys import path as syspath

syspath.append(pathjoin(dirname(__file__), "../.."))

from qsfo.parser import Parser
from qsfo.monitoring.trace import SignalsTrace
from qsfo.monitoring.quantitative import OfflineMonitor

if __name__ == "__main__":
    # formula = Parser().parse(r"f(t) \le g(t + 1)")
    formula = Parser().parse(r"exists c \in [0,2]: 0 < f(t - c)")

    signal = SignalsTrace.from_list(
        [
            ["t", "f"],
            [0, 0],
            [1, -3],
            [2, -1],
            [3, 1],
        ]
    )
    print(formula)
    mon_signal = OfflineMonitor(formula, signal).signal()
    for sig in mon_signal:
        v, P = sig
        print(P)
