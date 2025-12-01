import time

from qsfo.formula import *
from qsfo.monitoring.trace import TraceSegment
from qsfo.monitoring.polyhedralist import FormulaPolyhedraList, PolyhedraList
from qsfo.polyhedron import (
    Var,
    Polyhedron,
    INFTY,
    NEG_INFTY,
    solve_for_variable,
    NO_BOUNDS,
    Interval,
)
from sympy import And, Eq, S, Or
from qsfo.dbg import trace_calls, add_to_trace


class RobustnessPolyhedron:
    """
    A polyhedron with assigned robustness value.

    NOTE: this class does not inherit from `Polyhedron` on purpose,
    to make operations with the robustness expression explicit.
    """

    def __init__(self, r_expr, poly: Polyhedron) -> None:
        assert isinstance(poly, Polyhedron), (type(poly), poly)
        assert not poly.is_empty(), poly
        assert not poly.reduce().is_empty(), poly
        self._robustness_expr = r_expr
        self._poly = poly

    def poly(self) -> PolyhedraList:
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
        return RobustnessPolyhedron(
            self._robustness_expr.subs(list(S.items())), self._poly.substitute(S)
        )

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
    else:
        raise NotImplementedError(f"Operation not implemented: {op}")


class OnlineMonitor:
    def __init__(self, formula: Formula, horizon: float = None):
        self._formula: Formula = formula
        # the signal history up to the horizon (P_f)
        self._signal: list[dict[str, TraceSegment]] = []
        # at this moment, we hardcode that our free time variable is 't'
        self.timevar = Var("t")
        self._horizon = horizon

        # TODO: gather constraints from the formula
        self._P_dom: Polyhedron | None = Polyhedron([self.timevar >= 0])

        # we need to create new fresh variables while computing signals,
        # we cache them here
        # XXX: if the cache becomes too big, it might be better not
        # to cache the variables, but just create them and let garbage collection
        # get rid of them once we do not need them
        self._vars = {}
        # numbering for unnamed variables
        self.__annon_vars_idx: int = 0

        self._last_time_measure = None

    def _fresh_variable(self, name: str = None) -> Var:
        if name:
            return self._vars.get(name, Var(name))

        self.__annon_vars_idx += 1
        idx = self.__annon_vars_idx
        return Var(f"v_{idx}")

    def _get_var(self, name: str) -> Var:
        return self._vars.get(name, self._fresh_variable(name))

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
        #print(
        #    "NEW SEGMENT:\n",
        #    "".join(f"{sig}: {seg} @ {seg.bounds()}\n" for sig, seg in segment.items()),
        #)
        self._signal.append(segment)

        # trim segments that are out of horizon
        horizon = self._horizon
        if horizon is None:
            return

        cur_time = next(iter(segment.values())).bounds()
        limit = cur_time.start - horizon

        keep_from = -1
        for i in range(len(self._signal)):
            B = next(iter(self._signal[i].values())).bounds()
            if B.end >= limit:
                keep_from = i
                break;

        if keep_from > 0:
            self._signal = self._signal[keep_from:]


    # @trace_calls
    def update(
        self, segment: dict, time_interval: Polyhedron
    ) -> RobustnessPolyhedraList:
        """
        :param: segment - new segment (w_i in the paper), it is a dict that maps
                          signals names to polyhdera. These polyhedra already contain
                          the time constraints, that we might want to change in the future.
        """
        # add this new segment to the signal history (update P_f, Alg 1. line 5)
        self.update_signal(segment)

        # compute current contstraints on variables
        # P = self._P_dom.intersection(time_interval)
        P_seg = self._P_dom.intersection(time_interval)  # .simplify()

        # compute the monitoring signal and update the list of
        # known polyhedra, i.e., this call modifies `self._polyhedra`
        start_time = time.process_time()
        R = self.formula_robust(self._formula, P_seg)
        end_time = time.process_time()
        assert R, "Got no robustness polyhedra"

        # add_to_trace("R", *R)

        # compute the maximum robustness over the polyhedra
        start_time_2 = time.process_time()
        M = self.compute_maxima(R)
        end_time_2 = time.process_time()

        r_time = end_time - start_time
        m_time = end_time_2 - start_time_2
        self._last_time_measure = (r_time, m_time)
        print(
            f"\033[0;32m[time: robustness + maxima]: {r_time} + {m_time} = {r_time + m_time}\033[0m"
        )

        M = self.simplify_maxima(M)
        return M

    # def compute_maxima_region(self, i: int, R):
    #    rob = R[i].robustness()
    #    P = R[i].poly()
    #    # this we handle in the parent
    #    assert rob != NEG_INFTY, P
    #
    #    covered = PolyhedraList()
    #    maxima = []
    #    for j in range(len(R)):
    #        if i == j:
    #            continue
    #
    #        P_j = R[j]
    #        covered.add(P_j.poly())
    #
    #        P_I = P.intersection(P_j.poly()).reduce()
    #        if P_I.is_empty():
    #            continue
    #        # these constraints are True (and we have to handle them explicitly because PPL does not handle infty)
    #        rob_j = P_j.robustness()
    #        if rob != INFTY and rob_j != NEG_INFTY:
    #            P_I = P.intersection(Polyhedron([rob > rob_j]))
    #    return P_I.reduce()
    #
    # def _compute_maxima(self, R):
    #    P_ninfty = PolyhedraList()
    #    new_R = []
    #    for i, P in enumerate(R):
    #        rob = P.robustness()
    #        if rob == NEG_INFTY:
    #            P_ninfty.add(P.poly())
    #        else:
    #            region = self.compute_maxima_region(i, R)
    #            print(region)
    #            if region.is_empty():
    #                continue
    #            new_R.append(RobustnessPolyhedron(rob, region))
    #
    #    return new_R

    def compute_maxima(self, R):
        M: set[RobustnessPolyhedron] = [R[0]]
        wbg: set[RobustnessPolyhedron] = set(R[1:])
        while wbg:
            P = wbg.pop()
            # add_to_trace(
            #    "M", *(f"{m} covers {And(*m.poly().constraints()).as_set()}" for m in M)
            # )
            # add_to_trace(
            #    "  together covers", Or(*(And(*m.poly().constraints()) for m in M)).as_set()
            # )
            # if __debug__:
            #    for i in range(len(M)):
            #        for j in range(len(M)):
            #            if i == j:
            #                continue
            #            assert (
            #                M[i].poly().intersection(M[j].poly()).reduce().is_empty()
            #            ), (str(M[i]), str(M[j]))
            newM: set[RobustnessPolyhedron] = set()
            intersected = False
            for n, X in enumerate(M):
                # robustness where P and X intersect
                r_P, r_X = P.robustness(), X.robustness()
                P_I = X.poly().intersection(P.poly()).reduce()
                if not P_I.is_empty():
                    # split the polyhedra to multiple parts based on the value of robustness
                    intersected = True
                    # explicitely handle infinity, because the polyhedra cannot cope with them
                    # (more concretely, the `reduce` method that is called automatically after intersection)
                    if r_P == INFTY:
                        newM.add(RobustnessPolyhedron(r_P, P_I))
                    elif r_P == NEG_INFTY:
                        newM.add(RobustnessPolyhedron(r_X, P_I))
                    else:
                        P_r = P_I.intersection(Polyhedron([r_P >= r_X])).reduce()
                        if not P_r.is_empty():
                            newM.add(RobustnessPolyhedron(r_P, P_r))
                        P_x = P_I.intersection(Polyhedron([r_P < r_X])).reduce()
                        if not P_x.is_empty():
                            newM.add(RobustnessPolyhedron(r_X, P_x))

                    # handle the robustness where P and X do not intersect
                    C: PolyhedraList = PolyhedraList(*P_I.complement())
                    for c in C:
                        # the part of P that is outside intersection needs to go back to
                        # the workbag, because it may intersect with other elements of M
                        cn = c.intersection(P.poly()).reduce()
                        if not cn.is_empty():
                            wbg.add(RobustnessPolyhedron(r_P, cn))
                        # the part of X that is not in the intersection is preserved in M
                        cx = c.intersection(X.poly()).reduce()
                        if not cx.is_empty():
                            newM.add(RobustnessPolyhedron(r_X, cx))

                    # at the moment we found this intersection, we modified the workbag
                    # and we need to restart. Just append the rest of M to newM and go
                    # for another polyhedron from the workbag
                    newM.update(iter(M[n + 1 :]))
                    M = list(newM)
                    break
                else:
                    newM.add(X)
            if not intersected:
                newM.add(P)
            M = list(newM)

        res: list[RobustnessPolyhedron] = []
        for m in M:
            if m.reduce().is_empty():
                continue
            res.append(m)

        return res

    def simplify_maxima(self, M):
        map = dict()
        for R in M:
            interval = And(*R.poly().constraints()).as_set()
            rob = R.robustness()
            cur = map.get(rob)
            if cur is None:
                map[rob] = interval
            else:
                map[rob] = cur | interval

        return [(r, C) for r, C in map.items()]

    # @trace_calls
    def formula_robust(self, formula, P_seg) -> RobustnessPolyhedraList:
        """
        Compute the robustness of the formula `self._formula`
        over the list of polyhdera `P`. Return a new list of polyhedra
        encoding the constraints gathered on the trace and the monitoring signal.
        """

        chld = formula.children()

        if isinstance(formula, Exists):
            q = formula.quantifier()
            r: Var = q.var().expr()
            r_bounds = q.bounds()
            P: RobustnessPolyhedraList = self.formula_robust(chld[0], P_seg)
            return self.eliminate_by_sup(P, r, r_bounds)
        elif isinstance(formula, Not):
            raise NotImplementedError("RobustnessPolyhedra")
            assert len(chld) == 1, "Negation must have only one sub-formula"
            newP = self.formula_robust(chld[0], P_seg)
            newv = self._fresh_variable()

            phl: PolyhedraList = (
                newP.intersection(Polyhedron([Eq(newv, -newP.var())]))
                .eliminate(newP.var())
                .reduce()
            )
            return FormulaPolyhedraList(newv, *phl)
        elif isinstance(formula, (LessThan, LessOrEqual)):
            lhs = self.term(chld[0])
            rhs = self.term(chld[1])
            return RobustnessPolyhedraList(
                (
                    RobustnessPolyhedron(
                        r.robustness() - l.robustness(),
                        l.poly().intersection(r.poly()).intersection(P_seg),
                    )
                    for l in lhs
                    for r in rhs
                )
            )

        # elif isinstance(formula, Or):
        #    P1, sig1 = self.formula_robust(chld[0], P)
        #    P2, sig2 = self.formula_robust(chld[1], P)
        #    raise NotImplementedError()
        # elif isinstance(formula, And):
        #    newv = self._fresh_variable()
        #    raise NotImplementedError()
        else:
            raise NotImplementedError(
                f"Unhandled formula type '{type(formula)}': {formula}"
            )

    # @trace_calls
    def term(self, formula: Formula) -> RobustnessPolyhedraList:
        """
        Compute robustness value (and constraints) for a term
        """
        if isinstance(formula, (TimeVar, ValueVar)):
            v = self._get_var(formula.name())
            return RobustnessPolyhedron(
                v, Polyhedron([], variables=set((v, self.timevar)))
            ).to_list()
        if isinstance(formula, Constant):
            # The constraints are a universe poly for the time variable (we cannot put there the empty polyhedron
            # as that would mean that the robustness is void)
            return RobustnessPolyhedron(
                formula.value(),
                Polyhedron(
                    [],
                    variables=set((self.timevar,)),
                ),
            ).to_list()
        if isinstance(formula, (TimeOp, ValueOp)):
            op: str = formula.op()
            if op in ("+", "-"):
                assert len(formula.children()) == 2, formula

                # simplify adding/substracting 0
                children = formula.children()
                if isinstance(children[0], Constant) and children[0].value() == 0:
                    # 0 on the left can be ignored for addition
                    if op == "+":
                        return self.term(children[1])
                    else:
                        # otherwise we negate the value of the subterm
                        lhs: RobustnessPolyhedraList = self.term(children[1])
                        return RobustnessPolyhedraList(
                            (
                                RobustnessPolyhedron(-ph.robustness(), ph.poly())
                                for ph in lhs
                            )
                        )
                elif isinstance(children[1], Constant) and children[1].value() == 0:
                    # 0 on the right can be ignored for addition and substraction
                    return self.term(children[0])

                rpl_0: RobustnessPolyhedraList = self.term(children[0])
                rpl_1: RobustnessPolyhedraList = self.term(children[1])
                assert rpl_0 is not None, formula
                assert rpl_1 is not None, formula

                return RobustnessPolyhedraList(
                    (
                        RobustnessPolyhedron(
                            robustness_poly_op(op, lhs, rhs),
                            lhs.poly().intersection(rhs.poly()),
                        )
                        for lhs in rpl_0
                        for rhs in rpl_1
                    )
                )
            else:
                raise NotImplementedError(f"Operation not implemented: {formula}")
        if isinstance(formula, Signal):
            sig: str = formula.name()
            time_term: Term = formula.arg()
            # get the list of segments for the given signal
            segments = (elem[sig] for elem in self._signal)
            segments = [
                seg.substitute({seg.timevar(): time_term.expr()}) for seg in segments
            ]
            return RobustnessPolyhedraList(segments)
        else:
            raise NotImplementedError(f"Translation of term not implemented: {formula}")

    # @trace_calls
    def eliminate_by_sup(
        self, P_in: RobustnessPolyhedraList, x: Var, x_bounds: tuple
    ) -> RobustnessPolyhedraList:
        P_res = []
        for ph in P_in:
            P_I = (
                ph.poly()
                .intersection(Polyhedron([x_bounds[0] <= x, x <= x_bounds[1]]))
                .reduce()
            )
            if P_I.is_empty():
                continue
            Q = self.parametric_lp_maximize(P_I, ph.robustness(), x)
            P_res.extend(Q)

        return RobustnessPolyhedraList(P_res)

    # @trace_calls
    def parametric_lp_maximize(
        self, P: Polyhedron, robustness_expr, x: Var
    ) -> FormulaPolyhedraList:
        """
        `robustness_expr` is the current robustness expression
        `x` is the quantified variable
        """
        assert isinstance(P, Polyhedron), (P, type(P))
        assert robustness_expr.has(x), (x, robustness_expr)

        # rewrite the robustness expression to the form `alpha*x + beta` and get `alpha` and `beta`
        alpha, beta = split_coeff(robustness_expr, x)

        # get upper and lower bounds on `x`
        L, U, P_0 = isolate_bounds(P, x)
        P_Y = P.eliminate(x)

        G_pos = P_0.intersection(Polyhedron([alpha > 0], variables=P_0.vars())).reduce()
        G_neg = P_0.intersection(Polyhedron([alpha < 0], variables=P_0.vars())).reduce()
        G_zero = P_0.intersection(
            Polyhedron([Eq(alpha, 0)], variables=P_0.vars())
        ).reduce()
        Q = []

        if not G_pos.is_empty():
            if not U:
                q = G_pos.intersection(P_Y).intersection(robustness_poly).reduce()
                if not q.is_empty():
                    Q.append(RobustnessPolyhedron(INFTY, q))
                    # add_to_trace("G_pos (not U)", Q[-1])
            else:
                for u in U:
                    A_u = Polyhedron([(u <= un) for un in U], variables=P_Y.vars())
                    F_u = Polyhedron([(l <= u) for l in L], variables=P_Y.vars())
                    q = (
                        G_pos.intersection(A_u).intersection(F_u).intersection(P_Y)
                    ).reduce()
                    # add_to_trace("A_u constraints", [(u <= un) for un in U])
                    # add_to_trace('G_pos computation (P_Y, G_pos, A_u, F_u, intersection of all)', P_Y, G_pos, A_u, F_u, q)
                    if not q.is_empty():
                        Q.append(RobustnessPolyhedron(alpha * u + beta, q))
                        # add_to_trace("G_pos", Q[-1])

        if not G_neg.is_empty():
            if not L:
                q = G_neg.intersection(P_Y).reduce()
                if not q.is_empty():
                    Q.append(RobustnessPolyhedron(INFTY, q))
                    # add_to_trace("G_neg", Q[-1])
            else:
                for l in L:
                    A_l = Polyhedron([(l >= ln) for ln in L], variables=P_Y.vars())
                    F_l = Polyhedron([(l <= u) for u in U], variables=P_Y.vars())
                    q = (
                        G_neg.intersection(A_l).intersection(F_l).intersection(P_Y)
                    ).reduce()
                    if not q.is_empty():
                        Q.append(RobustnessPolyhedron(alpha * l + beta, q))
                        # add_to_trace("G_neg", Q[-1])

        if not G_zero.is_empty():
            q = G_zero.intersection(P_Y).reduce()
            if not q.is_empty():
                Q.append(RobustnessPolyhedron(beta, q))
                # add_to_trace("G_zero", Q[-1])

        q = (PolyhedraList(P_Y.complement()).intersection(P_0)).reduce()
        if not q.is_empty():
            for ph in q:
                Q.append(RobustnessPolyhedron(NEG_INFTY, ph))
                # add_to_trace("G_complement", Q[-1])

        return RobustnessPolyhedraList(Q)


# @trace_calls
def split_coeff(expr, x):  # now rewirte to `\alpha*x \beta`
    """
    Rewrite expression `expr` into the form `alpha * x + beta`
    """
    expr = expr.collect(x)
    alpha = expr.coeff(x)
    beta = expr - alpha * x
    return alpha, beta


# @trace_calls
def isolate_bounds(P, x) -> tuple[list, list, Polyhedron]:
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
            # expr >= 0
            if coeff > 0:
                L.append(bound)  # x {>,>=} bound
            else:
                U.append(bound)  # x {<,<=} bound

    return L, U, Polyhedron(P_0)


class OfflineMonitor:

    def __init__(self, formula, trace, horizon=None):
        self._formula = formula
        self._trace = trace
        self._horizon = horizon

    def signal(self):
        mon = OnlineMonitor(self._formula, self._horizon)
        signal_names = self._trace.header()[1:]
        piecewise_signals: dict[str, TraceSegment] = {
            name: self._trace.piecewise_linear_signal(name) for name in signal_names
        }
        timevar: Var = self._trace.timevar()

        for n in range(len(self._trace) - 1):
            # merge constraints for all signals together,
            # the algorithm asssumes it
            segment: dict[str, TraceSegment] = {
                name: piecewise_signals[name][n] for name in signal_names
            }
            # the time interval is the same for all signals, so just take one signal
            time_interval: TraceSegment = piecewise_signals[signal_names[0]][n]
            time_interval: Polyhedron = time_interval.time_bounds_as_ph().substitute(
                {time_interval.timevar(): mon.timevar}
            )

            yield mon.update(segment, time_interval)
