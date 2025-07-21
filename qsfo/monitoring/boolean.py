from qsfo.polyhedron import Var, Polyhedron
from qsfo.formula import *

from sympy import Eq, LessThan


class PolyhedraList:
    """
    A set of polyhedra describing a part of the n-dimensional space.
    The interpretation is the _union_ of all polyhedra.

    TODO: keep it sorted to optimize the operations
    """

    def __init__(self, *args):
        assert all(isinstance(i, Polyhedron) for i in args), args
        self._phs = list(args)

    def add(self, ph):
        self._phs.append(ph)

    def union(self, other: "PolyhedraList"):
        return PolyhedraList(*(self._phs + other._phs))

    def intersection(self, other):
        """
        Intersect this polyhedra list with another polyhedra list or with a polyhedron
        """
        if isinstance(other, Polyhedron):
            other = PolyhedraList(other)

        print("FIXME: use ordering on lists")
        new_phs = []
        for lhs in self._phs:
            for rhs in other._phs:
                ph = lhs.intersection(rhs)
                if ph:
                    new_phs.append(ph)

        return PolyhedraList(*new_phs)

    def eliminate(self, var: Var):
        return PolyhedraList(*(p.eliminate(var) for p in self._phs))

    def __len__(self):
        return len(self._phs)

    def __iter__(self):
        return iter(self._phs)

    def __str__(self):
        return f'{{{", ".join(map(str, self._phs))}}}'


class FormulaPolyhedraList(PolyhedraList):
    """
    A pair of a PolyhedronSet and a variable which represents the value of the formula.
    """

    def __init__(self, var: Var, *args):
        super().__init__(*args)
        self._var = var

    def var(self):
        return self._var

    def __str__(self):
        return f"{self._var} ==> {super().__str__()}"


class Formula2Polyhedra:
    def __init__(self):
        # cache for variables
        self._vars = {}
        # numbering for unnamed variables
        self.__annon_vars_idx = 0

    def _new_var(self, name=None):
        if name:
            print("Creating var", name)
            return self._vars.get(name, Var(name))

        self.__annon_vars_idx += 1
        idx = self.__annon_vars_idx
        return Var(f"v_{idx}")

    def _get_var(self, name):
        return self._vars.get(name, self._new_var(name))

    def _create_ph(self, bounds, *args):
        # FIXME: not using bounds here
        return Polyhedron(list(args))

    def _term(self, formula, trace, bounds):
        resvar = self._new_var()
        if isinstance(formula, (TimeVar, ValueVar)):
            sub_vars = resvar - self._get_var(formula.name())
            return FormulaPolyhedraList(
                resvar, self._create_ph((None, None), sub_vars <= 0, 0 <= sub_vars)
            )
        if isinstance(formula, Constant):
            print("FIXME: add bounds on the value from quantifiers")
            sub_vars = resvar - formula.value()
            return FormulaPolyhedraList(
                resvar, self._create_ph((None, None), sub_vars <= 0, 0 <= sub_vars)
            )
        if isinstance(formula, (TimeOp, ValueOp)):
            op = formula.op()
            if op in ("+", "-"):
                assert len(formula.children()) == 2, formula
                lhs = self.term(formula.children()[0], trace)
                rhs = self.term(formula.children()[1], trace)
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

                fph = FormulaPolyhedraList(
                    resvar,
                    *lhs.intersection(rhs).intersection(
                        self._create_ph((None, None), resvar <= expr, expr <= resvar)
                    ),
                )
                fph.eliminate(lhs.var()).eliminate(rhs.var())
                return fph
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
            return FormulaPolyhedraList(resvar, *segments)

        else:
            raise NotImplementedError(f"Translation of term not implemented: {formula}")

    def term(self, formula, trace):
        return self._term(formula, trace, (None, None))

    def translate(self, formula, trace):

        chld = formula.children()

        if isinstance(formula, Exists):
            # TODO: add bounds
            q = formula.quantifier()
            qv = q.var().expr()
            phl = self.translate(formula.children()[0], trace)
            bounds = q.bounds()
            if bounds:
                phl = phl.intersection(
                    self._create_ph((None, None), bounds[0] <= qv, qv <= bounds[1])
                )
            return phl.eliminate(qv)
        elif isinstance(formula, Not):
            # TODO
            print("TODO: implement Not")
            f = self.translate(formula.children()[0], trace)
            return f
        elif isinstance(formula, LessOrEqual):
            assert len(chld) == 2, chld
            if isinstance(chld[0], TimeTerm):
                assert isinstance(chld[1], (TimeTerm, Constant)), chld[1]
                term = TimeOp("-", chld[0], chld[1])
            elif isinstance(chld[0], ValueTerm):
                assert isinstance(chld[1], (ValueTerm, Constant)), chld[1]
                term = ValueOp("-", chld[0], chld[1])
            else:
                raise NotImplementedError(f"Unhandled term: {chld[0]}")

            lhs = self.term(term, trace)
            lvar = lhs.var()
            return lhs.intersection(self._create_ph((None, None), lvar < 0)).eliminate(
                lvar
            )
        elif isinstance(formula, Or):
            assert len(chld) == 2, chld
            return self.translate(chld[0], trace).union(self.translate(chld[1], trace))
        else:
            raise NotImplementedError(
                f"Unhandled formula type '{type(formula)}': {formula}"
            )
