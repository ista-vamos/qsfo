from ..polyhedron import Polyhedron, Var, NO_BOUNDS, Interval
from sympy import Rational, Eq


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

    def timevar(self):
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

    def substitute(self, S: dict, new_timevar=None, variables=None):
        n = TraceSegment(
            new_timevar or self._timevar,
            self.substitute_constraints(S),
            variables,
            #self.time_bounds(),
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

    def from_csv_file(path: str, sampling=None, timevar='t', signals: list[str] = None):
        """
        If samling is not None, we assume that it is a floating point number describing
        the sampling frequency of the data in the CSV file. In that case,
        we also assume that the time values are not present in the CSV file and we add.

        If `signals` is non-empty, consider only signals in `signals`.
        """
        # TODO: use `csv` package
        with open(path, "r") as f:
            if signals:
                header = [nm.strip() for nm in f.readline().split(',') if nm in signals]
            else:
                header = [nm.strip() for nm in f.readline().split(',')]

            if sampling is not None:
                header = [str(timevar)] + header
            tr = SignalsTrace(header, [])
            N = len(header)
            for n, line in enumerate(f):
                vals = line.split(',')
                if signals:
                    vals = {header[i].strip(): float(vals[i]) for i in range(N) if header[i] in signals}
                else:
                    vals = {header[i].strip(): float(vals[i]) for i in range(N)}

                if sampling is not None:
                    vals[timevar] = n*sampling

                if len(vals) != N:
                    raise RuntimeError(f"Missing values on line {n+2}. Expected {N} values, got {len(vals)}")

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
                raise RuntimeError(f"Missing values on line {n+2}")

            tr.append({header[i]: float(row[i]) for i in range(N)})

        return tr

    def piecewise_linear_signal(self, varname) -> list:
        """
        Get the piecewise linear signal for a particular variable
        represented as a sequence of timed polyhedra.
        """
        t = self._header[0]
        timevar = Var(f"t_{varname}")
        resvar = Var(f"v_{varname}")
        N = len(self)

        sig = PiecewiseTrace(timevar, resvar, [])
        last = self[0]
        for i in range(1, N):
            cur = self[i]
            #a = Rational(cur[varname] - last[varname]) / Rational(cur[t] - last[t])
            #b = Rational(last[varname]) - a * Rational(last[t])
            a = (cur[varname] - last[varname]) / (cur[t] - last[t])
            b = (last[varname]) - a * (last[t])
            line = a * timevar + b
            print(line)
            sig.append(
                TraceSegment(
                    timevar,
                    constraints=[Eq(line - resvar, 0)],
                    bounds=Interval(last[t], cur[t], ropen=True),
                    #bounds=Interval(Rational(last[t]), Rational(cur[t]), ropen=True),
                ).connstraint_by_time_bounds()
            )
            last = cur
        return sig
