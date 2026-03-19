from lark import Token
from ..polyhedron import Polyhedron, Var, NO_BOUNDS, Interval, frac
from sympy import Eq
import csv

# from fractions import Fraction


class TraceSegment(Polyhedron):
    """
    Polyhedron with explicit time variable that we use to represent
    a segment of a piece-wise linear trace.
    """

    def __init__(
        self,
        timevar: Var,
        constraints: list,
        variables=None,
        bounds: Interval = NO_BOUNDS,
    ):
        super().__init__(constraints, variables, bounds)
        assert isinstance(bounds, Interval), bounds
        self._timevar = timevar
        self._time_bounds = bounds

    def bounds(self):
        return self._time_bounds

    def connstraint_by_time_bounds(self) -> "TraceSegment":
        bounds = self._time_bounds
        timevar = self._timevar
        if not bounds.is_left_unbounded:
            self._constraints.add(
                timevar > bounds.start if bounds.left_open else timevar >= bounds.start
            )
        if not bounds.is_right_unbounded:
            self._constraints.add(
                timevar < bounds.end if bounds.right_open else timevar <= bounds.end
            )
        if bounds != NO_BOUNDS:
            self._vars.add(timevar)

        return self

    def timevar(self) -> Var:
        return self._timevar

    def time_bounds_as_ph(self) -> Polyhedron:
        C = []
        bounds = self._time_bounds
        timevar = self._timevar
        if not bounds.is_left_unbounded:
            C.append(
                timevar > bounds.start if bounds.left_open else timevar >= bounds.start
            )
        if not bounds.is_right_unbounded:
            C.append(
                timevar < bounds.end if bounds.right_open else timevar <= bounds.end
            )

        return Polyhedron(C, set((self.timevar(),)), self._time_bounds)

    def substitute(
        self, S: dict, new_timevar: None | str = None, variables: None | set = None
    ) -> "TraceSegment":
        n = TraceSegment(
            new_timevar or self._timevar,
            self.substitute_constraints(S),
            variables,
            # self.time_bounds(),
        )
        return n


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
    def __init__(self, header: list[str], iterable):
        """
        `header` is a list of strings, first one is the time variable,
        the rest is the signal.
        """
        super().__init__(iterable)
        self._header = header

    def timevar(self) -> str:
        return self._header[0]

    def header(self) -> list[str]:
        return self._header

    def from_signal_file(path: str) -> "SignalsTrace":
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
                    raise RuntimeError(f"Missing values on line {n + 2}")

                tr.append({header[i]: float(vals[i]) for i in range(N)})

            return tr

    def from_csv_file(
        path: str,
        sampling: None | int | float = None,
        timevar: str = "t",
        signals: None | list[Token] = None,
        max_samples: None | int = None,
    ) -> "SignalsTrace":
        """
        If samling is not None, we assume that it is a floating point number describing
        the sampling frequency of the data in the CSV file. In that case,
        we also assume that the time values are not present in the CSV file and we add.

        If `signals` is non-empty, consider only signals in `signals`.
        """
        with open(path, "r") as f:
            reader = csv.reader(f)
            header_row = next(reader)
            if signals:
                _signals = set((s.value.strip() for s in signals))
                _signals.add(timevar)
                header: list[str] = [nm.strip() for nm in header_row if nm in _signals]
            else:
                header: list[str] = [nm.strip() for nm in header_row]

            if sampling is not None:
                header: list[str] = [str(timevar)] + header
            tr = SignalsTrace(header, [])
            N = len(header_row)
            for n, row in enumerate(reader):
                if max_samples is not None and n >= max_samples:
                    break
                if len(row) != N:
                    raise RuntimeError(
                        f"Missing values on line {n + 2}. Expected {N} values, got {len(row)}"
                    )

                if sampling is not None:
                    row = [n * sampling] + row

                # filter to given signals only
                if _signals:
                    vals = {s: float(v) for s, v in zip(header, row) if s in _signals}
                else:
                    vals = {s: float(v) for s, v in zip(header, row)}

                tr.append(vals)

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
                raise RuntimeError(f"Missing values on line {n + 2}")

            tr.append({header[i]: float(row[i]) for i in range(N)})

        return tr

    def piecewise_linear_signal(self, varname: str) -> list[TraceSegment]:
        """
        Get the piecewise linear signal for a particular variable
        represented as a sequence of timed polyhedra.
        """
        t: str = self._header[0]
        timevar = Var(f"t_{varname}")
        resvar = Var(f"v_{varname}")
        N = len(self)

        sig = PiecewiseTrace(timevar, resvar, [])
        last = self[0]
        for i in range(1, N):
            cur = self[i]
            a = frac(cur[varname] - last[varname]) / frac(cur[t] - last[t])
            b = frac(last[varname]) - a * frac(last[t])
            # a = (cur[varname] - last[varname]) / (cur[t] - last[t])
            # b = (last[varname]) - a * (last[t])
            line = a * timevar + b
            sig.append(
                TraceSegment(
                    timevar,
                    constraints=[Eq(line - resvar, 0)],
                    # bounds=Interval(last[t], cur[t], ropen=True),
                    bounds=Interval(frac(last[t]), frac(cur[t]), ropen=True),
                ).connstraint_by_time_bounds()
            )
            last = cur
        return sig
