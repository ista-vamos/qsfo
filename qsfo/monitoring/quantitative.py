from qsfo.formula import *
from qsfo.polyhedron import Var, Polyhedron


class OnlineMonitor:
    def __init__(self, formula):
        self._formula = formula
        # these constraints are \mathcal{P} in the paper
        self._constraints = []
        # the signal history up to the horizon (P_f)
        self._signal = []

        # TODO: gather constraints from the formula
        self._P_dom = []

        # cache for variables
        self._vars = {}
        # numbering for unnamed variables
        self.__annon_vars_idx = 0

    def _fresh_variable(self, name=None):
        if name:
            return self._vars.get(name, Var(name))

        self.__annon_vars_idx += 1
        idx = self.__annon_vars_idx
        return Var(f"v_{idx}")

    def _get_var(self, name):
        return self._vars.get(name, self._fresh_variable(name))

    def update(self, segment):
        segment_poly = Polyhedron(
            [c for seg in segment.values() for c in seg.constraints()]
        )
        # add this new segment to the signal history
        self._signal.append(segment)
        # TODO: trim `self._signal` to the horizon

        # update the list of polyhedra we have with the new segment
        # TODO: I think we can modify the list in place, but I wanted to
        # stick to the code in the paper
        # TODO: trim `self._polyhdera` based on the horizon
        P = self._constraints + [segment_poly]

        # compute the monitoring signal and update the list of
        # known polyhedra, i.e., this call modifies `self._polyhedra`
        P, sig = self.formula_robust(self._formula, P)

        # remember the current polyhedra for future calls of `update`
        self._polyhedra = P

        return sig

    def formula_robust(self, formula, P):
        """
        Compute the robustness of the formula `self._formula`
        over the list of polyhdera `P`. Return a new list of polyhedra
        encoding the constraints gathered on the trace and the monitoring signal.
        """

        chld = formula.children()

        if isinstance(formula, Exists):
            assert False
        # q = formula.quantifier()
        # qv = q.var().expr()
        # bounds = q.bounds()

        # new_var_bounds = {} if not var_bounds else var_bounds.copy()
        # assert qv not in new_var_bounds, (qv, new_var_bounds)
        # new_var_bounds[qv] = bounds

        # phl = self._translate(formula.children()[0], trace, new_var_bounds)
        # if bounds:
        #    phl = phl.intersection(
        #        self._create_ph(bounds[0] <= qv, qv <= bounds[1])
        #    )
        # print("Elim", qv, "\n", phl)
        # phl = phl.eliminate(qv)
        # print("Elim:", phl)
        # print("F", formula)
        # return phl
        elif isinstance(formula, Not):
            assert len(chld) == 1, "Negation must have only one sub-formula"
            newP, sig = self.formula_robust(chld[0], P)
            newv = self._fresh_variable()
            # TODO: make this operation more efficient (maybe keep the last element separately
            # as we often update it?)
            P = newP[:-1]
            P.append(newP[-1].intersection(Polyhedron([newv == -sig])))
            return P, sig
        elif isinstance(formula, (LessThan, LessOrEqual)):
            term = ValueOp("-", chld[1], chld[0])
            return self.term(term, P)
        elif isinstance(formula, Or):
            P1, sig1 = self.formula_robust(chld[0], P)
            P2, sig2 = self.formula_robust(chld[1], P)
        elif isinstance(formula, And):
            newv = self._fresh_variable()
            pass
        else:
            raise NotImplementedError(
                f"Unhandled formula type '{type(formula)}': {formula}"
            )

    def term(self, formula: Formula, P):
        """
        Compute robustness value (and constraints) for a term
        """
        resvar = self._fresh_variable()
        if isinstance(formula, (TimeVar, ValueVar)):
            print("FIXME 102: add bounds on the value from quantifiers", bounds)
            v = self._get_var(formula.name())
            sub_vars = resvar - v
            return FormulaPolyhedraList(
                resvar, Polyhedron([sub_vars <= 0, 0 <= sub_vars])
            )
        if isinstance(formula, Constant):
            sub_vars = resvar - formula.value()
            return FormulaPolyhedraList(
                resvar, Polyhedron([sub_vars <= 0, 0 <= sub_vars])
            )
        if isinstance(formula, (TimeOp, ValueOp)):
            op = formula.op()
            if op in ("+", "-"):
                assert len(formula.children()) == 2, formula
                lhs = self.term(formula.children()[0], P)
                rhs = self.term(formula.children()[1], P)
                assert lhs is not None, formula
                assert rhs is not None, formula
                assert len(lhs) > 0, lhs
                assert len(rhs) > 0, rhs

                if op == "+":
                    expr = lhs.var() + rhs.var()
                elif op == "-":
                    expr = lhs.var() - rhs.var()
                else:
                    raise NotImplementedError(f"Operation not implemented: {formula}")

                phl = (
                    lhs.intersection(rhs)
                    .intersection(Polyhedron([resvar <= expr, expr <= resvar]))
                    .eliminate(lhs.var())
                    .eliminate(rhs.var())
                )
                return FormulaPolyhedraList(resvar, *phl)
            else:
                raise NotImplementedError(f"Operation not implemented: {formula}")
        if isinstance(formula, Signal):
            resvar = self._fresh_variable()
            sig = formula.name()
            arg = formula.arg()
            # get the list of segments for the given signal
            segments = [elem[sig] for elem in self._signal]
            # XXX: we assume that the output of the signal is named identically
            # as the signal itself
            segments = [seg.substitute({seg.timevar(): arg.expr()}) for seg in segments]
            print(list(map(str, segments)))
            # for seg in segments:
            #    print(str(seg))
            phl = FormulaPolyhedraList(resvar, *segments)
            if bounds:
                applicable_bounds = []
                for v in phl.vars():
                    B = bounds.get(v)
                    if B:
                        applicable_bounds.append(B.start <= v)
                        applicable_bounds.append(v <= B.end)

                if applicable_bounds:
                    phl = FormulaPolyhedraList(
                        resvar, *phl.intersection(self._create_ph(*applicable_bounds))
                    )
            return phl
        else:
            raise NotImplementedError(f"Translation of term not implemented: {formula}")


class OfflineMonitor:
    def __init__(self, formula, trace):
        self._formula = formula
        self._trace = trace

    def signal(self):
        mon = OnlineMonitor(self._formula)
        signal_names = self._trace.header()[1:]
        piecewise_signals = {
            name: self._trace.piecewise_linear_signal(name) for name in signal_names
        }
        timevar = self._trace.timevar()

        for n, elem in enumerate(self._trace):
            # merge constraints for all signals together,
            # the algorithm asssumes it
            segment = {name: piecewise_signals[name][n] for name in signal_names}

            print("-----------------------------------")
            print(
                "\033[0;36mSegment @",
                elem[timevar],
                ":",
                Polyhedron([c for seg in segment.values() for c in seg.constraints()]),
                "\033[0m",
            )
            yield mon.update(segment)
