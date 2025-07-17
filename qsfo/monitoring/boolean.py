from qsfo.polyhedron import Var, Polyhedron
from qsfo.formula import *


class PolyhedronList:
    """
    A set of polyhedra describing a part of the n-dimensional space.
    The interpretation is the _union_ of all polyhedra.

    TODO: keep it sorted to optimize the operations
    """
    def __init__(self, *args):
        self._phs = list(args)

    def add(self, ph):
        self._phs.append(ph)

    def __str__(self):
        return f'{{{", ".join(map(str, self._phs))}}}'


class FormulaPolyhedra:
    """
    A pair of a PolyhedronSet and a variable which represents the value of the formula.
    """

    def __init__(self, var: Var, phs: PolyhedronList):
        self._var = var
        self._phs = phs

    def __str__(self):
        return f'{self._var} ==> {self._phs}'



class Formula2Polyhedra:
    def __init__(self):
        # cache for variables
        self._vars = {}
        # numbering for unnamed variables
        self.__annon_vars_idx = 0

    def _new_var(self, name=None):
        if name:
            return self._vars.get(name, Var(name))

        self.__annon_vars_idx += 1
        idx = self.__annon_vars_idx
        return Var(f'v_{idx}')

    def _get_var(self, name):
        return self._vars.get(name, self._new_var(name))

    def _create_ph(self, bounds, *args):
        # FIXME: not using bounds here
        return Polyhedron(*args)

    def _term(self, formula, bounds):
        resvar = self._new_var()
        if isinstance(formula, (TimeVar, ValueVar)):
            return FormulaPolyhedra(
                resvar,
                PolyhedronList(
                    self._create_ph(
                        (None, None), resvar == self._get_var(formula.name())
                    )
                ),
            )
        if isinstance(formula, (TimeConstant, ValueConstant)):
            print("FIXME: add bounds on the value from quantifiers")
            return FormulaPolyhedra(
                resvar,
                PolyhedronList(
                    self._create_ph(
                        (None, None), resvar == formula.value()
                    )
                ),
            )


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
