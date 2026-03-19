import time

from qsfo.formula import *
from qsfo.monitoring.trace import TraceSegment
from qsfo.monitoring.polyhedralist import PolyhedraList
from qsfo.polyhedron import (
    Var,
    Polyhedron,
    INFTY,
    NEG_INFTY,
    NO_BOUNDS,
    Interval,
    constraints_time_set_fast,
    frac,
)

# import And as AND, to avoid conflict with qsfo.formula.And
from sympy import And as AND, Eq
from sympy.logic.boolalg import BooleanFalse, BooleanTrue

# from qsfo.dbg import trace_calls, add_to_trace

def _tri_bool(expr) -> bool | None:
    """Return True/False if `expr` is a concrete boolean, else None.

    SymPy comparisons sometimes evaluate eagerly to BooleanTrue/BooleanFalse.
    We must not pass those booleans into the Polyhedron backend.
    """

    if expr is True or expr is False:
        return expr
    if isinstance(expr, (BooleanTrue, BooleanFalse)):
        return bool(expr)
    return None


def _filter_trivial_constraints(constraints):
    """Drop trivially-true constraints; detect trivially-false constraints.

    Returns:
      - list of non-trivial constraints, if satisfiable
      - None, if any constraint is (concretely) False
    """

    filtered = []
    for c in constraints:
        tb = _tri_bool(c)
        if tb is True:
            continue
        if tb is False:
            return None
        filtered.append(c)
    return filtered


def _poly_from_guards(guards, variables) -> Polyhedron | None:
    """Build a Polyhedron from guard constraints, handling booleans.

    Returns None if guards are unsatisfiable (contain concrete False).
    """

    guards = _filter_trivial_constraints(guards)
    if guards is None:
        return None
    return Polyhedron(guards, variables=variables)


def _intersect_guard(poly: Polyhedron, guard, *, variables=None) -> Polyhedron | None:
    """Intersect `poly` with a guard that may simplify to True/False.

    If `guard` is:
      - True: returns `poly`
      - False: returns None
      - relational: returns reduced intersection
    """

    tb = _tri_bool(guard)
    if tb is True:
        return poly
    if tb is False:
        return None
    if variables is None:
        variables = poly.vars()
    return poly.intersection(Polyhedron([guard], variables=variables)).reduce()


def _numeric_sign(expr) -> int | None:
    """If `expr` is provably numeric, return its sign (+1/0/-1)."""

    # Python numbers
    if isinstance(expr, (int, float)):
        if expr > 0:
            return 1
        if expr < 0:
            return -1
        return 0

    # SymPy numbers (Rational, Integer, etc.)
    try:
        if getattr(expr, "is_number", False):
            if expr > 0:
                return 1
            if expr < 0:
                return -1
            return 0
    except TypeError:
        # Non-comparable symbolic expression
        return None

    return None


class RobustnessPolyhedron:
    """
    A polyhedron with assigned robustness value.

    NOTE: this class does not inherit from `Polyhedron` on purpose,
    to make operations with the robustness expression explicit.
    """

    def __init__(self, r_expr, poly: Polyhedron) -> None:
        assert r_expr is not None, poly
        assert isinstance(poly, Polyhedron), (type(poly), poly)
        assert not poly.is_empty(), poly
        assert not poly.reduce().is_empty(), poly
        self._robustness_expr = r_expr
        self._poly = poly

    def poly(self) -> Polyhedron:
        return self._poly

    def robustness(self):
        return self._robustness_expr

    def reduce(self):
        self._poly.reduce()
        return self

    def is_empty(self):
        return self._poly.is_empty()

    def to_list(self):
        return RobustnessPolyhedraList((self,))

    def substitute(self, S):
        expr = self._robustness_expr
        if hasattr(expr, "subs"):
            expr = expr.subs(list(S.items()))
        return RobustnessPolyhedron(expr, self._poly.substitute(S))

    def __str__(self) -> str:
        return f"{self._robustness_expr} with {self._poly}"


class RobustnessPolyhedraList(list):
    """
    A list of RobustnessPolyhedra
    """

    def __init__(self, iterable):
        super().__init__(iterable)

        assert all(isinstance(x, RobustnessPolyhedron) for x in self), self

    def __str__(self) -> str:
        return " ; ".join(map(str, self))


class RobustnessTraceSegment(RobustnessPolyhedron):
    def __init__(
        self, r_expr, poly: Polyhedron, timevar: Var, bounds: Interval = NO_BOUNDS
    ) -> None:
        self._robustness_expr = r_expr
        self._poly = poly
        self._timevar = timevar
        self._bounds = bounds

    def bounds(self) -> Interval:
        return self._bounds

    def timevar(self) -> Var:
        return self._timevar


def segment_to_rph(var: str, segment: TraceSegment) -> RobustnessTraceSegment:
    # TODO: we assume that the value of the segment is named `v_{var}`
    var = Var(f"v_{var}")
    defeq = [c for c in segment.constraints() if isinstance(c, Eq) and c.has(var)]
    rest = [c for c in segment.constraints() if not (isinstance(c, Eq) and c.has(var))]
    assert len(defeq) == 1, defeq

    expr = defeq[0]
    expr = (expr.lhs - expr.rhs).collect(var)
    coef = expr.coeff(var)
    robustness = (expr - coef * var) / (-1 * coef)

    return RobustnessTraceSegment(
        robustness, Polyhedron(rest), segment.timevar(), bounds=segment.bounds()
    )


def robustness_poly_op(op, lhs, rhs):
    if op == "+":
        expr = lhs.robustness() + rhs.robustness()
    elif op == "-":
        expr = lhs.robustness() - rhs.robustness()
    elif op == "*":
        expr = lhs.robustness() * rhs.robustness()
    else:
        raise NotImplementedError(f"Operation not implemented: {op}")

    return expr


class OnlineMonitor:
    def __init__(self, formula: Formula, horizon: float | int | None = None):
        self._formula: Formula = formula
        # the signal history up to the horizon (P_f)
        self._signal: list[dict[str, RobustnessTraceSegment]] = []
        # at this moment, we hardcode that our free time variable is 't'
        self.timevar = Var("t")
        self._horizon = horizon

        # gather constraints from the formula and other known constraints that are valid universally
        self._P_dom: Polyhedron | None = Polyhedron([self.timevar >= 0])

        self._vars: dict[str, Var] = {}
        # numbering for unnamed variables
        self.__annon_vars_idx: int = 0

        self._last_time_measure = None

    def _get_var(self, name: str) -> Var:
        """Return a stable `Var` object for a given name.

        Ensures that the monitor's free time variable is represented by the
        same `Var` instance everywhere.
        """

        # Make sure we never create a second Var('t') besides `self.timevar`.
        if name == str(self.timevar):
            return self.timevar

        v = self._vars.get(name)
        if v is None:
            v = Var(name)
            self._vars[name] = v
        return v
    def _fresh_variable(self, name: str = None) -> Var:
        """Return a fresh anonymous variable, or a stable named variable."""

        if name is not None:
            return self._get_var(name)

        self.__annon_vars_idx += 1
        idx = self.__annon_vars_idx
        return Var(f"v_{idx}")

    def negate(self, P: Polyhedron, v: Var) -> Polyhedron:
        """
        Negate the value of polyhedron `P`, where the value is given
        in the variable `v`. The output polyhedron will still have
        the value in `v`.
        """
        raise NotImplementedError("Needs fix")
        new_v = self._fresh_variable()
        P.substitute({v: new_v})
        return P.intersection(Polyhedron([Eq(v, -new_v)]))

    def update_signal(self, segment) -> None:
        # transform the signal into a robustness polyhedron
        segment = {sig: segment_to_rph(sig, seg) for sig, seg in segment.items()}
        self._signal.append(segment)

    def _trim_signal_history(self, limit) -> None:
        """Drop stored signal segments that end strictly before `limit`."""

        keep_from = -1
        for j in range(len(self._signal)):
            B = next(iter(self._signal[j].values())).bounds()
            if B.end >= limit:
                keep_from = j
                break

        if keep_from > 0:
            self._signal = self._signal[keep_from:]

    def update(
        self, segment: dict, time_interval: Polyhedron, stats: bool = False
    ) -> RobustnessPolyhedraList:
        """
        :param: segment - new segment (w_i in the paper), it is a dict that maps
                          signals names to polyhdera. These polyhedra already contain
                          the time constraints, that we might want to change in the future.
        """
        # add this new segment to the signal history (update P_f, Alg 1. line 5)
        self.update_signal(segment)

        # compute current contstraints on variables
        P_seg = self._P_dom.intersection(time_interval)

        # compute the monitoring signal
        start_time = time.process_time()
        R = self.formula_robust(self._formula, P_seg)
        end_time = time.process_time()

        # `R == []` means "undefined everywhere" (Remark 2.3 in the draft),
        # *not* NEG_INFTY.

        # optional post-processing: union regions that share identical robustness
        start_time_2 = time.process_time()
        M = self.simplify_maxima(R)
        end_time_2 = time.process_time()

        r_time = end_time - start_time
        m_time = end_time_2 - start_time_2

        # Trim signal history for the next step (Alg. 1, line 9 in the draft).
        horizon = self._horizon
        if horizon is not None and self._signal:
            cur_bounds = next(iter(self._signal[-1].values())).bounds()
            self._trim_signal_history(cur_bounds.end - horizon)

        if stats:
            return M, r_time, m_time
        return M

    def _split_max_on_intersection(
        self, I: Polyhedron, r_l, r_r
    ) -> list[RobustnessPolyhedron]:
        """Return polyhedral pieces for max(r_l, r_r) restricted to I."""

        # Explicitly handle infinities to avoid passing them into the Polyhedron backend.
        if r_l == INFTY or r_r == INFTY:
            return [RobustnessPolyhedron(INFTY, I)]
        if r_l == NEG_INFTY:
            return [RobustnessPolyhedron(r_r, I)]
        if r_r == NEG_INFTY:
            return [RobustnessPolyhedron(r_l, I)]

        # Finite case: split along r_l >= r_r.
        pieces: list[RobustnessPolyhedron] = []
        P1 = _intersect_guard(I, r_l >= r_r, variables=I.vars())
        if P1 is not None and not P1.is_empty():
            pieces.append(RobustnessPolyhedron(r_l, P1))
        P2 = _intersect_guard(I, r_l < r_r, variables=I.vars())
        if P2 is not None and not P2.is_empty():
            pieces.append(RobustnessPolyhedron(r_r, P2))
        return pieces

    def _split_min_on_intersection(
        self, I: Polyhedron, r_l, r_r
    ) -> list[RobustnessPolyhedron]:
        """Return polyhedral pieces for min(r_l, r_r) restricted to I."""

        # Explicitly handle infinities.
        if r_l == NEG_INFTY or r_r == NEG_INFTY:
            return [RobustnessPolyhedron(NEG_INFTY, I)]
        if r_l == INFTY:
            return [RobustnessPolyhedron(r_r, I)]
        if r_r == INFTY:
            return [RobustnessPolyhedron(r_l, I)]

        pieces: list[RobustnessPolyhedron] = []
        P1 = _intersect_guard(I, r_l <= r_r, variables=I.vars())
        if P1 is not None and not P1.is_empty():
            pieces.append(RobustnessPolyhedron(r_l, P1))
        P2 = _intersect_guard(I, r_l > r_r, variables=I.vars())
        if P2 is not None and not P2.is_empty():
            pieces.append(RobustnessPolyhedron(r_r, P2))
        return pieces

    def compute_maxima(self, R: RobustnessPolyhedraList) -> RobustnessPolyhedraList:
        """Compute a pointwise maximum over possibly-overlapping polyhedral pieces.

        This is used to implement the "remove dominated points" step in
        EliminateBySup (Alg. 1), i.e. keep only maximum robustness for each
        valuation of the remaining variables.
        """

        if not R:
            return RobustnessPolyhedraList([])

        # Maintain an invariant that elements of `M` are pairwise disjoint.
        M: list[RobustnessPolyhedron] = [R[0]]
        wbg: list[RobustnessPolyhedron] = list(R[1:])

        while wbg:
            P = wbg.pop()
            newM: list[RobustnessPolyhedron] = []
            intersected = False

            for n, X in enumerate(M):
                r_P, r_X = P.robustness(), X.robustness()
                P_I = X.poly().intersection(P.poly()).reduce()
                if P_I.is_empty():
                    newM.append(X)
                    continue

                intersected = True

                # Part on the intersection uses max(r_P, r_X)
                newM.extend(self._split_max_on_intersection(P_I, r_P, r_X))

                # Split the parts of P and X outside the intersection.
                for c in PolyhedraList(*P_I.complement()):
                    cn = c.intersection(P.poly()).reduce()
                    if not cn.is_empty():
                        wbg.append(RobustnessPolyhedron(r_P, cn))

                    cx = c.intersection(X.poly()).reduce()
                    if not cx.is_empty():
                        newM.append(RobustnessPolyhedron(r_X, cx))

                # We modified the workbag; restart with the updated M.
                newM.extend(M[n + 1 :])
                break

            if not intersected:
                newM.append(P)

            M = newM

        # Final cleanup
        res: list[RobustnessPolyhedron] = []
        for m in M:
            m.reduce()
            if not m.is_empty():
                res.append(m)

        return RobustnessPolyhedraList(res)

    def simplify_maxima(self, M):
        merged_by_rob = {}
        interval_cache = {}

        for R in M:
            constraints = R.poly().constraints()
            key = frozenset(constraints)
            if key in interval_cache:
                interval = interval_cache[key]
            else:
                interval = constraints_time_set_fast(constraints, self.timevar)
                if interval is None:
                    interval = AND(*constraints).as_set()
                interval_cache[key] = interval

            rob = R.robustness()
            cur = merged_by_rob.get(rob)
            if cur is None:
                merged_by_rob[rob] = interval
            else:
                merged_by_rob[rob] = cur | interval

        return [(r, C) for r, C in merged_by_rob.items()]

    def formula_robust(self, formula, P_seg) -> RobustnessPolyhedraList:
        """Compute the robustness of `formula` over the domain polyhedron `P_seg`."""

        chld = formula.children()

        if isinstance(formula, Exists):
            q = formula.quantifier()
            r: Var = q.var().expr()
            r_bounds = q.bounds()

            P: RobustnessPolyhedraList = self.formula_robust(
                chld[0],
                P_seg.intersection(Polyhedron([r_bounds[0] <= r, r <= r_bounds[1]])),
            )
            return self.eliminate_by_sup(P, r, r_bounds)

        elif isinstance(formula, Not):
            assert len(chld) == 1, "Negation must have only one sub-formula"
            newP = self.formula_robust(chld[0], P_seg)
            res = []
            for r in newP:
                rob = r.robustness()
                if rob == INFTY:
                    new_rob = NEG_INFTY
                elif rob == NEG_INFTY:
                    new_rob = INFTY
                else:
                    new_rob = -rob
                res.append(RobustnessPolyhedron(new_rob, r.poly()))
            return RobustnessPolyhedraList(res)
        elif isinstance(formula, (LessThan, LessOrEqual)):
            lhs = self.term(chld[0], P_seg)
            rhs = self.term(chld[1], P_seg)

            res = []
            for l, r in ((l, r) for l in lhs for r in rhs):
                poly = l.poly().intersection(r.poly()).intersection(P_seg).reduce()
                if poly.is_empty():
                    continue
                res.append(RobustnessPolyhedron(r.robustness() - l.robustness(), poly))

            return RobustnessPolyhedraList(res)

        elif isinstance(formula, And):
            R1 = self.formula_robust(chld[0], P_seg)
            R2 = self.formula_robust(chld[1], P_seg)
            res = []
            for lhs in R1:
                for rhs in R2:
                    I = lhs.poly().intersection(rhs.poly()).reduce()
                    if I.is_empty():
                        continue
                    res.extend(
                        self._split_min_on_intersection(
                            I, lhs.robustness(), rhs.robustness()
                        )
                    )
            return RobustnessPolyhedraList(res)

        elif isinstance(formula, Or):
            R1 = self.formula_robust(chld[0], P_seg)
            R2 = self.formula_robust(chld[1], P_seg)
            res = []
            for lhs in R1:
                for rhs in R2:
                    I = lhs.poly().intersection(rhs.poly()).reduce()
                    if I.is_empty():
                        continue
                    res.extend(
                        self._split_max_on_intersection(
                            I, lhs.robustness(), rhs.robustness()
                        )
                    )
            return RobustnessPolyhedraList(res)

        else:
            raise NotImplementedError(
                f"Unhandled formula type '{type(formula)}': {formula}"
            )

    def term(self, formula: Formula, P_seg: Polyhedron) -> RobustnessPolyhedraList:
        """Compute robustness value (and constraints) for a term."""

        if isinstance(formula, (TimeVar, ValueVar)):
            v = self._get_var(formula.name())
            poly = Polyhedron([], variables=set((v, self.timevar))).intersection(P_seg)
            poly = poly.reduce()
            if poly.is_empty():
                return RobustnessPolyhedraList([])
            return RobustnessPolyhedron(v, poly).to_list()

        if isinstance(formula, Constant):
            poly = Polyhedron([], variables=set((self.timevar,))).intersection(P_seg)
            poly = poly.reduce()
            if poly.is_empty():
                return RobustnessPolyhedraList([])
            return RobustnessPolyhedron(frac(formula.value()), poly).to_list()

        if isinstance(formula, (TimeOp, ValueOp)):
            op: str = formula.op()

            if op in ("+", "-"):
                assert len(formula.children()) == 2, formula

                # simplify adding/substracting 0
                children = formula.children()
                if isinstance(children[0], Constant) and children[0].value() == 0:
                    if op == "+":
                        return self.term(children[1], P_seg)
                    else:
                        lhs: RobustnessPolyhedraList = self.term(children[1], P_seg)
                        return RobustnessPolyhedraList(
                            (RobustnessPolyhedron(-ph.robustness(), ph.poly()) for ph in lhs)
                        )

                elif isinstance(children[1], Constant) and children[1].value() == 0:
                    return self.term(children[0], P_seg)

                rpl_0: RobustnessPolyhedraList = self.term(children[0], P_seg)
                rpl_1: RobustnessPolyhedraList = self.term(children[1], P_seg)

                res = []
                for lhs, rhs in ((lhs, rhs) for lhs in rpl_0 for rhs in rpl_1):
                    poly = lhs.poly().intersection(rhs.poly()).reduce()
                    if poly.is_empty():
                        continue
                    res.append(RobustnessPolyhedron(robustness_poly_op(op, lhs, rhs), poly))

                return RobustnessPolyhedraList(res)

            if op == "abs":
                assert len(formula.children()) == 1, formula

                rpl: RobustnessPolyhedraList = self.term(formula.children()[0], P_seg)
                res = []
                for R in rpl:
                    r_expr = R.robustness()

                    # Handle infinities explicitly.
                    if r_expr == INFTY:
                        res.append(RobustnessPolyhedron(INFTY, R.poly()))
                        continue
                    if r_expr == NEG_INFTY:
                        res.append(RobustnessPolyhedron(INFTY, R.poly()))
                        continue

                    poly = R.poly()
                    I_pos = _intersect_guard(poly, r_expr >= 0, variables=poly.vars())
                    if I_pos is not None and not I_pos.is_empty():
                        res.append(RobustnessPolyhedron(r_expr, I_pos))

                    I_neg = _intersect_guard(poly, r_expr < 0, variables=poly.vars())
                    if I_neg is not None and not I_neg.is_empty():
                        res.append(RobustnessPolyhedron(-r_expr, I_neg))

                return RobustnessPolyhedraList(res)

            if op == "*":
                assert len(formula.children()) == 2, formula
                children = formula.children()

                assert isinstance(children[0], Constant) or isinstance(children[1], Constant)

                # We must still evaluate the non-constant side to preserve well-definedness
                # (signal accesses in the term still have to be defined), but we can
                # simplify the algebra where safe.
                if isinstance(children[0], Constant):
                    c = children[0].value()
                    rhs_terms = self.term(children[1], P_seg)
                    if c == 1:
                        return rhs_terms
                    if c == -1:
                        return RobustnessPolyhedraList(
                            (RobustnessPolyhedron(-ph.robustness(), ph.poly()) for ph in rhs_terms)
                        )
                    if c == 0:
                        return RobustnessPolyhedraList(
                            (RobustnessPolyhedron(frac(0), ph.poly()) for ph in rhs_terms)
                        )

                if isinstance(children[1], Constant):
                    c = children[1].value()
                    lhs_terms = self.term(children[0], P_seg)
                    if c == 1:
                        return lhs_terms
                    if c == -1:
                        return RobustnessPolyhedraList(
                            (RobustnessPolyhedron(-ph.robustness(), ph.poly()) for ph in lhs_terms)
                        )
                    if c == 0:
                        return RobustnessPolyhedraList(
                            (RobustnessPolyhedron(frac(0), ph.poly()) for ph in lhs_terms)
                        )

                rpl_0: RobustnessPolyhedraList = self.term(children[0], P_seg)
                rpl_1: RobustnessPolyhedraList = self.term(children[1], P_seg)

                res = []
                for lhs, rhs in ((lhs, rhs) for lhs in rpl_0 for rhs in rpl_1):
                    poly = lhs.poly().intersection(rhs.poly()).reduce()
                    if poly.is_empty():
                        continue
                    res.append(RobustnessPolyhedron(robustness_poly_op(op, lhs, rhs), poly))
                return RobustnessPolyhedraList(res)

            raise NotImplementedError(f"Operation not implemented: {formula}")

        if isinstance(formula, Signal):
            sig: str = formula.name()
            time_term: Term = formula.arg()
            segments = (elem[sig] for elem in self._signal)
            res = []
            for seg in segments:
                seg = seg.substitute({seg.timevar(): time_term.expr()})
                poly = seg.poly().intersection(P_seg).reduce()
                if poly.is_empty():
                    continue
                res.append(RobustnessPolyhedron(seg.robustness(), poly))
            return RobustnessPolyhedraList(res)

        raise NotImplementedError(f"Translation of term not implemented: {formula}")

    def eliminate_by_sup(
        self, P_in: RobustnessPolyhedraList, x: Var, x_bounds: tuple
    ) -> RobustnessPolyhedraList:
        """Eliminate a quantified variable by taking a supremum.

        This corresponds to Alg. 1's EliminateBySup, including the final
        dominated-point removal step.
        """

        P_res: list[RobustnessPolyhedron] = []
        for ph in P_in:
            P_I = (
                ph.poly()
                .intersection(Polyhedron([x_bounds[0] <= x, x <= x_bounds[1]]))
                .reduce()
            )
            if P_I.is_empty():
                continue
            Q = self.plp_maximize(P_I, ph.robustness(), x)
            P_res.extend(Q)

        # Remove dominated points: keep only pointwise maxima over the same Y.
        return self.compute_maxima(RobustnessPolyhedraList(P_res))

    def plp_maximize(
        self, P: Polyhedron, robustness_expr, x: Var
    ) -> RobustnessPolyhedraList:
        """Parametric linear maximization (Alg. 2 in the draft)."""

        assert isinstance(P, Polyhedron), (P, type(P))

        # Project out the quantified variable to obtain the parameter space.
        P_Y = P.eliminate(x)
        if P_Y.is_empty():
            return RobustnessPolyhedraList([])

        # Collect bounds on `x` and the x-free part of P.
        L, U, P_0 = isolate_bounds(P, x)

        # Restrict to feasible parameter valuations.
        P0Y = P_0.intersection(P_Y).reduce()
        if P0Y.is_empty():
            return RobustnessPolyhedraList([])

        # Constant robustness across x.
        if robustness_expr in (INFTY, NEG_INFTY):
            return RobustnessPolyhedraList([RobustnessPolyhedron(robustness_expr, P0Y)])

        if not hasattr(robustness_expr, "has") or not robustness_expr.has(x):
            alpha, beta = 0, robustness_expr
        else:
            alpha, beta = split_coeff(robustness_expr, x)

        vars_Y = P0Y.vars()
        Q: list[RobustnessPolyhedron] = []

        alpha_sign = _numeric_sign(alpha)

        # Case: alpha is provably constant
        if alpha_sign == 0:
            Q.append(RobustnessPolyhedron(beta, P0Y))
            return RobustnessPolyhedraList(Q)

        if alpha_sign == 1:
            G_pos, G_neg, G_zero = P0Y, None, None
        elif alpha_sign == -1:
            G_pos, G_neg, G_zero = None, P0Y, None
        else:
            # Symbolic sign: split the parameter space.
            G_pos = _intersect_guard(P0Y, alpha > 0, variables=vars_Y)
            G_neg = _intersect_guard(P0Y, alpha < 0, variables=vars_Y)
            G_zero = _intersect_guard(P0Y, Eq(alpha, 0), variables=vars_Y)

        if G_pos is not None and not G_pos.is_empty():
            if not U:
                # Unbounded above
                Q.append(RobustnessPolyhedron(INFTY, G_pos))
            else:
                for u in U:
                    A_u = _poly_from_guards([(u <= un) for un in U], variables=vars_Y)
                    if A_u is None:
                        continue
                    F_u = _poly_from_guards([(l <= u) for l in L], variables=vars_Y)
                    if F_u is None:
                        continue
                    q = G_pos.intersection(A_u).intersection(F_u).reduce()
                    if not q.is_empty():
                        Q.append(RobustnessPolyhedron(alpha * u + beta, q))

        if G_neg is not None and not G_neg.is_empty():
            if not L:
                # Unbounded below
                Q.append(RobustnessPolyhedron(INFTY, G_neg))
            else:
                for l in L:
                    A_l = _poly_from_guards([(l >= ln) for ln in L], variables=vars_Y)
                    if A_l is None:
                        continue
                    F_l = _poly_from_guards([(l <= u) for u in U], variables=vars_Y)
                    if F_l is None:
                        continue
                    q = G_neg.intersection(A_l).intersection(F_l).reduce()
                    if not q.is_empty():
                        Q.append(RobustnessPolyhedron(alpha * l + beta, q))

        if G_zero is not None and not G_zero.is_empty():
            Q.append(RobustnessPolyhedron(beta, G_zero))

        return RobustnessPolyhedraList(Q)


def split_coeff(expr, x):
    """Rewrite expression `expr` into the form `alpha * x + beta`."""

    expr = expr.collect(x)
    alpha = expr.coeff(x)
    beta = expr - alpha * x
    return alpha, beta


def isolate_bounds(P, x) -> tuple[list, list, Polyhedron]:
    """Extract symbolic lower/upper bounds on `x` from polyhedron constraints.

    Returns:
      - L: list of candidate lower bound expressions (x >= l)
      - U: list of candidate upper bound expressions (x <= u)
      - P_0: the sub-polyhedron containing constraints that do not mention x
    """

    L, U, P_0 = [], [], []
    for expr in P.constraints():
        if not expr.has(x):
            P_0.append(expr)
            continue

        op = expr.rel_op
        assert op in ("<", "<=", ">", ">=", "=="), expr
        expr = (expr.lhs - expr.rhs).collect(x)  # expr op 0
        coeff = expr.coeff(x)
        rest = expr - coeff * x
        bound = -rest / coeff  # x op' bound (where op' depends on coeff and op)

        if op == "==":
            L.append(bound)
            U.append(bound)
        elif op in ("<", "<="):
            if coeff > 0:
                U.append(bound)  # x {<,<=} bound
            else:
                L.append(bound)  # x {>,>=} bound
        else:  # ">" or ">="
            if coeff > 0:
                L.append(bound)  # x {>,>=} bound
            else:
                U.append(bound)  # x {<,<=} bound

    # IMPORTANT: P_0 must live in the parameter space (vars without x), otherwise
    # later intersections can accidentally re-introduce x as an unconstrained variable.
    vars_wo_x = set(P.vars())
    if x in vars_wo_x:
        vars_wo_x.remove(x)

    return L, U, Polyhedron(P_0, variables=vars_wo_x)


class OfflineMonitor:
    def __init__(self, formula, trace, horizon=None):
        self._formula = formula
        self._trace = trace
        self._horizon = horizon

    def signal(self):
        mon = OnlineMonitor(self._formula, self._horizon)
        signal_names: list[str] = self._trace.header()[1:]
        piecewise_signals: dict[str, list[TraceSegment]] = {
            name: self._trace.piecewise_linear_signal(name) for name in signal_names
        }

        for n in range(len(self._trace) - 1):
            segment: dict[str, TraceSegment] = {
                name: piecewise_signals[name][n] for name in signal_names
            }
            time_interval: TraceSegment = piecewise_signals[signal_names[0]][n]
            time_interval: Polyhedron = time_interval.time_bounds_as_ph().substitute(
                {time_interval.timevar(): mon.timevar}
            )

            yield mon.update(segment, time_interval)

    def signal_with_stats(self):
        """Generator for the robustness signal and computation statistics."""

        mon = OnlineMonitor(self._formula, self._horizon)
        signal_names = self._trace.header()[1:]
        piecewise_signals: dict[str, list[TraceSegment]] = {
            name: self._trace.piecewise_linear_signal(name) for name in signal_names
        }

        for n in range(len(self._trace) - 1):
            segment: dict[str, TraceSegment] = {
                name: piecewise_signals[name][n] for name in signal_names
            }
            time_interval: TraceSegment = piecewise_signals[signal_names[0]][n]
            time_interval: Polyhedron = time_interval.time_bounds_as_ph().substitute(
                {time_interval.timevar(): mon.timevar}
            )

            yield mon.update(segment, time_interval, stats=True), time_interval
