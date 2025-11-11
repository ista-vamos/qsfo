from qsfo.polyhedron import Var, Polyhedron, Interval
from qsfo.monitoring.polyhedralist import FormulaPolyhedraList
from qsfo.formula import *

from sympy import Eq


class Formula2Polyhedra:
    """
    Translate a formula to a polyhedra list. If the formula contains a signal,
    this process amounts to monitoring.
    """

    def __init__(self):
        # cache for variables
        self._vars = {}
        # numbering for unnamed variables
        self.__annon_vars_idx = 0

    def term(self, formula, trace, bounds) -> FormulaPolyhedraList:
        t = self._term(formula, trace, bounds)
        print("Translated")
        print(formula)
        print(t)
        return t

    def translate(self, formula: Formula, trace):
        timevar = trace.timevar()
        l, u = trace[0][timevar], trace[-1][timevar]
        var_bounds = {Var(timevar): Interval(l, u)}
        print("var_bounds", var_bounds)

        phl = self._translate(formula, trace, var_bounds)

        phl = phl.simplify(eq_break=False)
        print("Translated")
        print(formula)
        print(phl)
        print("-----")
        return phl

    def _new_var(self, name=None):
        if name:
            return self._vars.get(name, Var(name))

        self.__annon_vars_idx += 1
        idx = self.__annon_vars_idx
        return Var(f"v_{idx}")

    def _get_var(self, name):
        return self._vars.get(name, self._new_var(name))

    def _create_ph(self, *args):
        return Polyhedron(list(args))

    def _term(self, formula, trace, bounds):
        resvar = self._new_var()
        if isinstance(formula, (TimeVar, ValueVar)):
            print("FIXME 102: add bounds on the value from quantifiers", bounds)
            v = self._get_var(formula.name())
            sub_vars = resvar - v
            return FormulaPolyhedraList(
                resvar, self._create_ph(sub_vars <= 0, 0 <= sub_vars)
            )
        if isinstance(formula, Constant):
            sub_vars = resvar - formula.value()
            return FormulaPolyhedraList(
                resvar, self._create_ph(sub_vars <= 0, 0 <= sub_vars)
            )
        if isinstance(formula, (TimeOp, ValueOp)):
            op = formula.op()
            if op in ("+", "-"):
                assert len(formula.children()) == 2, formula
                lhs = self.term(formula.children()[0], trace, bounds)
                rhs = self.term(formula.children()[1], trace, bounds)
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
                    .intersection(self._create_ph(resvar <= expr, expr <= resvar))
                    .eliminate(lhs.var())
                    .eliminate(rhs.var())
                )
                return FormulaPolyhedraList(resvar, *phl)
            else:
                raise NotImplementedError(f"Operation not implemented: {formula}")
        if isinstance(formula, Signal):
            sig = formula.name()
            arg = formula.arg()
            segments = trace.piecewise_linear_signal(sig)
            tvar, svar = segments.timevar(), segments.sigvar()
            segments = [
                seg.substitute({tvar: arg.expr(), svar: resvar}) for seg in segments
            ]
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

    def _translate(self, formula: Formula, trace, var_bounds: dict) -> PolyhedraList:
        """
        Translate a formula into a polyhedra list.

        :param bounds: bounds on variables gathered while traversing the
                       formula
        """

        chld = formula.children()

        if isinstance(formula, Exists):
            q = formula.quantifier()
            qv = q.var().expr()
            bounds = q.bounds()

            new_var_bounds = {} if not var_bounds else var_bounds.copy()
            assert qv not in new_var_bounds, (qv, new_var_bounds)
            new_var_bounds[qv] = bounds

            phl = self._translate(formula.children()[0], trace, new_var_bounds)
            if bounds:
                phl = phl.intersection(
                    self._create_ph(bounds[0] <= qv, qv <= bounds[1])
                )
            print("Elim", qv, "\n", phl)
            phl = phl.eliminate(qv)
            print("Elim:", phl)
            print("F", formula)
            return phl
        elif isinstance(formula, Not):
            # TODO
            f = self._translate(formula.children()[0], trace, var_bounds)
            bounds = []
            phl = f.complement(Var(trace.timevar()))
            if var_bounds:
                for v in f.vars():
                    B = var_bounds.get(v)
                    if B is not None:
                        bounds.append(B.start <= v)
                        bounds.append(v <= B.end)

            if bounds:
                phl = phl.intersection(self._create_ph(*bounds))

            print("Translated")
            print(formula)
            print(phl)
            print("-----")
            return phl
        elif isinstance(formula, (LessThan, LessOrEqual)):
            assert len(chld) == 2, chld
            if isinstance(chld[0], TimeTerm):
                assert isinstance(chld[1], (TimeTerm, Constant)), chld[1]
                term = TimeOp("-", chld[0], chld[1])
            elif isinstance(chld[0], ValueTerm):
                assert isinstance(chld[1], (ValueTerm, Constant)), chld[1]
                term = ValueOp("-", chld[0], chld[1])
            else:
                raise NotImplementedError(f"Unhandled term: {chld[0]}")

            lhs = self.term(term, trace, var_bounds)
            lvar = lhs.var()
            if isinstance(formula, LessOrEqual):
                cmp_term = lvar <= 0
            elif isinstance(formula, LessThan):
                cmp_term = lvar < 0
            else:
                raise NotImplementedError(f"Invalid comparison: {formula}")

            phl = lhs.intersection(self._create_ph(cmp_term)).eliminate(lvar)
            print("Translated")
            print(formula)
            print(phl)
            print("-----")
            return phl
        elif isinstance(formula, Or):
            assert len(chld) == 2, chld
            return self._translate(chld[0], trace, var_bounds).union(
                self._translate(chld[1], trace, var_bounds)
            )
        elif isinstance(formula, And):
            assert len(chld) == 2, chld
            return self._translate(chld[0], trace, var_bounds).intersection(
                self._translate(chld[1], trace, var_bounds)
            )
        else:
            raise NotImplementedError(
                f"Unhandled formula type '{type(formula)}': {formula}"
            )
