from qsfo.formula import *
from qsfo.monitoring.trace import TraceSegment
from qsfo.monitoring.polyhedralist import FormulaPolyhedraList, PolyhedraList
from qsfo.polyhedron import Var, Polyhedron, INFTY, NEG_INFTY
from sympy import simplify, And, Eq
from qsfo.dbg import trace_calls


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

    def _get_var(self, name) -> Var:
        return self._vars.get(name, self._fresh_variable(name))

    def negate(self, P: Polyhedron, v: Var) -> Polyhedron:
        """
        Negate the value of polyhedron `P`, where the value is given
        in the variable `v`. The output polyhedron will still have
        the value in `v`.
        """
        new_v = self._fresh_variable()
        P.substitute({v: new_v})
        return P.intersection(Polyhedron([Eq(v, -new_v)]))

    def update(self, segment: dict, time_interval: Polyhedron):
        """
        :param: segment - new segment (w_i in the paper), it is a dict that maps
                          signals names to polyhdera. These polyhedra already contain
                          the time constraints, that we might want to change in the future.
        """
        # add this new segment to the signal history (update P_f, Alg 1. line 5)
        self._signal.append(segment)
        print(
            "NEW SEGMENT:\n", "".join(f"{sig}: {seg}\n" for sig, seg in segment.items())
        )

        # segment_poly = Polyhedron(
        #     [c for seg in segment.values() for c in seg.constraints()]
        # )

        # TODO: trim `self._signal` to the horizon

        # compute current contstraints on variables
        # P = self._P_dom.intersection(time_interval)
        P_seg = self._P_dom.intersection(time_interval).simplify()

        # compute the monitoring signal and update the list of
        # known polyhedra, i.e., this call modifies `self._polyhedra`
        res = self.formula_robust(self._formula, P_seg)

        return res.var(), res

    @trace_calls
    def formula_robust(self, formula, P_seg) -> FormulaPolyhedraList:
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
            P = self.formula_robust(chld[0], P_seg)
            return self.eliminate_by_sup(P, r, r_bounds)
        elif isinstance(formula, Not):
            assert len(chld) == 1, "Negation must have only one sub-formula"
            newP = self.formula_robust(chld[0], P_seg)
            newv = self._fresh_variable()
            return FormulaPolyhedraList(newv, list(P) + [newv == -newP.var()])
        elif isinstance(formula, (LessThan, LessOrEqual)):
            term = ValueOp("-", chld[1], chld[0])
            term = self.term(term)
            # TODO: remove the `simplify` if it takes too much time. It is nice mainly for debugging
            return FormulaPolyhedraList(
                term.var(), *term.intersection(P_seg).simplify()
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
    def term(self, formula: Formula):
        """
        Compute robustness value (and constraints) for a term
        """
        resvar: Var = self._fresh_variable()

        if isinstance(formula, (TimeVar, ValueVar)):
            v = self._get_var(formula.name())
            return FormulaPolyhedraList(resvar, Polyhedron([Eq(v, resvar)]))
        if isinstance(formula, Constant):
            c = formula.value()
            return FormulaPolyhedraList(resvar, Polyhedron([Eq(resvar, c)]))
        if isinstance(formula, (TimeOp, ValueOp)):
            op: str = formula.op()
            if op in ("+", "-"):
                assert len(formula.children()) == 2, formula
                lhs: FormulaPolyhedraList = self.term(formula.children()[0])
                rhs: FormulaPolyhedraList = self.term(formula.children()[1])
                assert lhs is not None, formula
                assert rhs is not None, formula
                assert len(lhs) > 0, lhs
                assert len(rhs) > 0, rhs

                if op == "+":
                    expr: Term = lhs.var() + rhs.var()
                elif op == "-":
                    expr: Term = lhs.var() - rhs.var()
                else:
                    raise NotImplementedError(f"Operation not implemented: {formula}")

                phl: PolyhedraList = (
                    lhs.intersection(rhs)
                    .intersection(Polyhedron([Eq(resvar, expr)]))
                    .eliminate(lhs.var())
                    .eliminate(rhs.var())
                )
                return FormulaPolyhedraList(resvar, *phl)
            else:
                raise NotImplementedError(f"Operation not implemented: {formula}")
        if isinstance(formula, Signal):
            sig: str = formula.name()
            time_term: Term = formula.arg()
            # get the list of segments for the given signal
            segments: list[TraceSegment] = [elem[sig] for elem in self._signal]
            # XXX: we assume that the output of the signal is named 'v_{sig}'
            # as the signal itself
            segments = [
                seg.substitute(
                    {seg.timevar(): time_term.expr(), Var(f"v_{sig}"): resvar},
                    new_timevar=self.timevar,
                )
                for seg in segments
            ]
            # XXX: the `simplify` takes quite some time..
            # segments = PolyhedraList([seg.substitute({seg.timevar(): time_term.expr()}) for seg in segments]).simplify()
            # for seg in segments:
            #    print('S', str(seg))
            return FormulaPolyhedraList(resvar, *segments)
        else:
            raise NotImplementedError(f"Translation of term not implemented: {formula}")

    @trace_calls
    def eliminate_by_sup(
        self, P_in: FormulaPolyhedraList, x: Var, x_bounds: tuple
    ) -> FormulaPolyhedraList:
        P_res = PolyhedraList()
        v = P_in.var()
        v_new = self._fresh_variable()
        for ph in P_in:
            P_I = ph.intersection(Polyhedron([x_bounds[0] <= x, x <= x_bounds[1]]))
            Q = self.parametric_lp_maximize(P_I, v, x, v_new)
            P_res = P_res.union(Q)

        return FormulaPolyhedraList(v_new, *(P_res.simplify()))

    @trace_calls
    def parametric_lp_maximize(
        self, P: Polyhedron, v: Var, x: Var, v_new: Var
    ) -> FormulaPolyhedraList:
        assert isinstance(P, Polyhedron), (P, type(P))
        alpha, beta = split_coeff(P, v, x)
        #print("alpha, beta", alpha, beta)
        L, U, P_0 = isolate_bounds(P, x)
        #print("L, U, P_0", L, U, P_0)
        P_Y = P.eliminate(x)
        #print("P_Y", P_Y)
        G_pos = P_0.intersection(Polyhedron([alpha > 0], variables=P_0.vars()))
        G_neg = P_0.intersection(Polyhedron([alpha < 0], variables=P_0.vars()))
        G_zero = P_0.intersection(Polyhedron([Eq(alpha, 0)], variables=P_0.vars()))
        #print("G_pos", G_pos)
        #print("G_neg", G_neg)
        #print("G_zero", G_zero)
        Q = PolyhedraList()

        if not G_pos.is_empty():
            if not U:
                Q.add(
                    G_pos.intersection(P_Y).intersection(Polyhedron([Eq(v_new, INFTY)]))
                )
            else:
                for u in U:
                    A_u = Polyhedron([(u <= un) for un in U])
                    F_u = Polyhedron([(l <= u) for l in L])
                    Q.add(
                        G_pos.intersection(A_u)
                        .intersection(F_u)
                        .intersection(P_Y)
                        .intersection(Polyhedron([Eq(v_new, alpha * u + beta)]))
                    )

        if not G_neg.is_empty():
            if not L:
                Q.append(
                    G_neg.intersection(P_Y).intersection(Polyhedron([Eq(v_new, INFTY)]))
                )
            else:
                for l in L:
                    A_l = Polyhedron([(l >= ln) for ln in L])
                    F_l = Polyhedron([(l <= u) for u in U])
                    Q.add(
                        G_neg.intersection(A_l)
                        .intersection(F_l)
                        .intersection(P_Y)
                        .intersection(Polyhedron([Eq(v_new, alpha * l + beta)]))
                    )

        if not G_zero.is_empty():
            Q.add(
                G_zero.intersection(P_Y).intersection(Polyhedron([Eq(v_new, beta)]))
            )

        Q.add(P_0.intersection(self.negate(P_Y, v)).intersection(Polyhedron([Eq(v_new, INFTY)])))

        return Q


def split_coeff(P, v, x):
    # take the polyhedron and get the expression that defines `v`
    exprs = [constr for constr in P.constraints() if constr.has(v)]
    assert len(exprs) == 1, (P, exprs)
    expr = exprs[0]
    assert isinstance(expr, Eq), expr

    # rewrite the expression such that coeff. of `v` is -1, so that we have
    # `-v + RHS == 0`. Then add `v` to get RHS.
    v_expr = (expr.lhs - expr.rhs).collect(v)
    expr = (-1) * (v_expr / v_expr.coeff(v)) + v
    assert not expr.has(v), expr

    # now rewirte to `\alpha*x \beta`
    expr = expr.collect(x)
    alpha = expr.coeff(x)
    beta = expr - alpha * x
    return alpha, beta


def isolate_bounds(P, x) -> tuple[list, list, Polyhedron]:
    L, U, P_0 = [], [], []
    for expr in P.constraints():
        if not expr.has(x):
            P_0.append(expr)
            continue

        op = expr.rel_op
        assert op in ("<", "<=", ">", ">=", "=="), expr
        expr = (expr.lhs - expr.rhs).collect(x)
        coeff = expr.coeff(x)
        bound = (expr - coeff * x) / coeff
        if op == "==":
            U.append(bound)
            L.append(bound)
        else:
            (U if op in ("<=", "<") else L).append(bound)

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
            print('SEGMENT', segment)
            # the time interval is the same for all signal, so just take one signal
            time_interval: TraceSegment = piecewise_signals[signal_names[0]][n]
            time_interval: Polyhedron = time_interval.time_bounds_as_ph().substitute(
                {time_interval.timevar(): mon.timevar}
            )

            yield mon.update(segment, time_interval)
