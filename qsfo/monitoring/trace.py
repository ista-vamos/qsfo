from ..polyhedron import TimedPolyhedron, Var
from sympy import Rational


class PiecewiseTrace(list):
    def __init__(self, timevar, sigvar, iterable):
        super().__init__(iterable)

        self._timevar = timevar
        self._sigvar = sigvar

    def timevar(self):
        return self._timevar

    def sigvar(self):
        return self._sigvar


class SignalsTrace(list):

    def __init__(self, header, iterable):
        """
        `header` is a list of strings, first one is the time variable,
        the rest is the signal.
        """
        super().__init__(iterable)
        self._header = header

    def timevar(self):
        return self._header[0]

    def header(self):
        return self._header

    def from_signal_file(path):
        """
        Create trace from a file containing sampled signals.
        We assume that the file has a header with names.
        The first name is the time variable, the rest of the names are names of the signals.
        For example `t f g`. Then, every other line gives the values `t f(t) g(t)`.
        """
        with open(path, "r") as f:
            header = f.readline().split()
            tr = SignalsTrace(header, [])
            N = len(header)
            for n, line in enumerate(f):
                vals = line.split()
                if len(vals) != N:
                    raise RuntimeError(f"Missing values on line {n+2}")

                tr.append({header[i]: float(vals[i]) for i in range(N)})

            return tr

    def from_list(lst: list):
        """
        Create trace from a file containing sampled signals.
        We assume that the first element of the list is a header.
        The first name is the time variable, the rest of the names are names of the signals.
        For example `t f g`. Then, every other line gives the values `t f(t) g(t)`.
        """
        header = lst[0]
        tr = SignalsTrace(header, [])
        N = len(header)
        for n, row in enumerate(lst[1:]):
            if len(row) != N:
                raise RuntimeError(f"Missing values on line {n+2}")

            tr.append({header[i]: float(row[i]) for i in range(N)})

        return tr


    def piecewise_linear_signal(self, varname) -> list:
        """
        Get the piecewise linear signal for a particular variable
        represented as a sequence of timed polyhedra.
        """
        t = self._header[0]
        timevar = Var(t)
        resvar = Var(varname)
        N = len(self)

        sig = PiecewiseTrace(timevar, resvar, [])
        last = self[0]
        for i in range(1, N):
            cur = self[i]
            a = Rational(cur[varname] - last[varname]) / Rational(cur[t] - last[t])
            b = Rational(last[varname]) - a * Rational(last[t])
            line = a * timevar + b
            sig.append(
                TimedPolyhedron(
                    timevar,
                    (last[t], cur[t]),
                    constraints=[line - resvar <= 0, 0 <= line - resvar],
                )
            )
        return sig
