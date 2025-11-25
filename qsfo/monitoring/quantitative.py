from sympy.external.gmpy import is_fermat_prp
from qsfo.formula import *
from qsfo.monitoring.trace import TraceSegment
from qsfo.monitoring.polyhedralist import FormulaPolyhedraList, PolyhedraList
from qsfo.polyhedron import Var, Polyhedron, INFTY, NEG_INFTY, solve_for_variable
from sympy import And, Eq
from qsfo.dbg import trace_calls, add_to_trace


class RobustnessPolyhedron:
    """
    A polyhedron with assigned robustness value.

    NOTE: this class does not inherit from `Polyhedron` on purpose,
    to make operations with the robustness expression explicit.
    """

    def __init__(self, r_expr, poly: Polyhedron) -> None:
        self._robustness_expr = r_expr
        self._poly = poly

    def poly(self) -> PolyhedraList:
        return self._poly

    def robustness(self):
        return self._robustness_expr

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
    def __init__(self, r_expr, poly: Polyhedron, timevar: Var) -> None:
        self._robustness_expr = r_expr
        self._poly = poly
        self._timevar = timevar

    def timevar(self) -> Var:
        return self._timevar


def segment_to_rph(var: str, segment: TraceSegment) -> RobustnessTraceSegment:
    # TODO: we assume that the value of the segment is named `v_{var}`
    print(var, segment)
    var = Var(f"v_{var}")
    defeq = [c for c in segment.constraints() if isinstance(c, Eq) and c.has(var)]
    rest = [c for c in segment.constraints() if not (isinstance(c, Eq) and c.has(var))]
    assert len(defeq) == 1, defeq

    expr = defeq[0]
    expr = (expr.lhs - expr.rhs).collect(var)
    coef = expr.coeff(var)
    robustness = (expr - coef * var) / (-1 * coef)

    return RobustnessTraceSegment(robustness, Polyhedron(rest), segment.timevar())


def robustness_poly_op(op, lhs, rhs):
    if op == "+":
        expr = lhs.robustness() + rhs.robustness()
    elif op == "-":
        expr = lhs.robustness() - rhs.robustness()
    else:
        raise NotImplementedError(f"Operation not implemented: {op}")


class OnlineMonitor:
    def __init__(self, formula: Formula):
        self._formula: Formula = formula
        # the signal history up to the horizon (P_f)
        self._signal: list[dict[str, TraceSegment]] = []
        # at this moment, we hardcode that our free time variable is 't'
        self.timevar = Var("t")

        # TODO: gather constraints from the formula
        self._P_dom: Polyhedron | None = Polyhedron([self.timevar >= 0])

        # we need to create new fresh variables while computing signals,
        # we cache them here
        # XXX: if the cache becomes too big, it might be better not
        # to cache the variables, but ust create them and let garbage collection
        # get rid of them once we do not need them
        self._vars = {}
        # numbering for unnamed variables
        self.__annon_vars_idx: int = 0

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

    def append_signal(self, segment) -> None:
        # transform the signal into a robustness polyhedron
        segment = {sig: segment_to_rph(sig, seg) for sig, seg in segment.items()}
        print(
            "NEW SEGMENT:\n", "".join(f"{sig}: {seg}\n" for sig, seg in segment.items())
        )
        self._signal.append(segment)

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
        self.append_signal(segment)

        # TODO: trim `self._signal` to the horizon

        # compute current contstraints on variables
        # P = self._P_dom.intersection(time_interval)
        P_seg = self._P_dom.intersection(time_interval)  # .simplify()

        # compute the monitoring signal and update the list of
        # known polyhedra, i.e., this call modifies `self._polyhedra`
        return self.formula_robust(self._formula, P_seg)

    @trace_calls
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

    @trace_calls
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

    @trace_calls
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

    @trace_calls
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
                    add_to_trace("G_pos (not U)", Q[-1])
            else:
                for u in U:
                    A_u = Polyhedron([(u <= un) for un in U], variables=P_Y.vars())
                    F_u = Polyhedron([(l <= u) for l in L], variables=P_Y.vars())
                    q = (
                        G_pos.intersection(A_u).intersection(F_u).intersection(P_Y)
                    ).reduce()
                    add_to_trace("A_u constraints", [(u <= un) for un in U])
                    add_to_trace('G_pos computation (P_Y, G_pos, A_u, F_u, intersection of all)', P_Y, G_pos, A_u, F_u, q)
                    if not q.is_empty():
                        Q.append(RobustnessPolyhedron(alpha * u + beta, q))
                        add_to_trace("G_pos", Q[-1])

        if not G_neg.is_empty():
            if not L:
                q = G_neg.intersection(P_Y).reduce()
                if not q.is_empty():
                    Q.append(RobustnessPolyhedron(INFTY, q))
                    add_to_trace("G_neg", Q[-1])
            else:
                for l in L:
                    A_l = Polyhedron([(l >= ln) for ln in L], variables=P_Y.vars())
                    F_l = Polyhedron([(l <= u) for u in U], variables=P_Y.vars())
                    q = (
                        G_neg.intersection(A_l).intersection(F_l).intersection(P_Y)
                    ).reduce()
                    if not q.is_empty():
                        Q.append(RobustnessPolyhedron(alpha * l + beta, q))
                        add_to_trace("G_neg", Q[-1])

        if not G_zero.is_empty():
            q = G_zero.intersection(P_Y).reduce()
            if not q.is_empty():
                Q.append(RobustnessPolyhedron(beta, q))
                add_to_trace("G_zero", Q[-1])

        q = (PolyhedraList(P_Y.complement()).intersection(P_0)).reduce()
        if not q.is_empty():
            for ph in q:
                Q.append(RobustnessPolyhedron(NEG_INFTY, ph))
                add_to_trace("G_complement", Q[-1])

        return RobustnessPolyhedraList(Q)


@trace_calls
def split_coeff(expr, x):  # now rewirte to `\alpha*x \beta`
    expr = expr.collect(x)
    alpha = expr.coeff(x)
    beta = expr - alpha * x
    return alpha, beta


@trace_calls
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

    def __init__(self, formula, trace):
        self._formula = formula
        self._trace = trace

    def signal(self):
        mon = OnlineMonitor(self._formula)
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
