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
        self._phs = list(args)

    def add(self, ph):
        self._phs.append(ph)

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
        return f'{self._var} ==> {super().__str__()}'



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
        return Var(f'v_{idx}')

    def _get_var(self, name):
        return self._vars.get(name, self._new_var(name))

    def _create_ph(self, bounds, *args):
        # FIXME: not using bounds here
        return Polyhedron(list(args))

    def _term(self, formula, bounds):
        resvar = self._new_var()
        if isinstance(formula, (TimeVar, ValueVar)):
            sub_vars = resvar - self._get_var(formula.name())
            return FormulaPolyhedraList(
                resvar,
                self._create_ph(
                    (None, None), sub_vars <= 0, 0 <= sub_vars
                )
            )
        if isinstance(formula, Constant):
            print("FIXME: add bounds on the value from quantifiers")
            sub_vars = resvar - formula.value()
            return FormulaPolyhedraList(
                resvar,
                self._create_ph(
                    (None, None), sub_vars <= 0, 0 <= sub_vars
                )
            )
        if isinstance(formula, (TimeOp, ValueOp)):
            op = formula.op()
            if op in ("+", "-"):
                assert len(formula.children()) == 2, formula
                lhs = self.term(formula.children()[0])
                rhs = self.term(formula.children()[1])
                assert lhs is not None, formula
                assert rhs is not None, formula
                assert len(lhs) == 1, lhs
                assert len(rhs) == 1, rhs


                if op == "+":
                    expr = lhs.var() + rhs.var()
                elif op == "-":
                    expr = lhs.var() - rhs.var()
                else:
                    raise NotImplementedError(f"Operation not implemented: {formula}")

                fph = FormulaPolyhedraList(
                    resvar,
                    lhs.intersection(rhs).intersection(self._create_ph((None, None), resvar <= expr, expr <= resvar))
                )
                fph.eliminate(lhs.var()).eliminate(rhs.var())
                return fph
            else:
                raise NotImplementedError(f"Operation not implemented: {formula}")


    def term(self, formula):
        return self._term(formula, (None, None))

    def translate(self, formula):
        def _translate(f, lvl):
            if isinstance(f, Term):
                print(f)
                r = self.term(f)
                print(r)
                print("----")

        # This is for testing now, in the real version
        # we do a manual top-down recursion
        formula.visit_dfs(_translate)
