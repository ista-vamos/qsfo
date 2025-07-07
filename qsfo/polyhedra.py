from .formula import *
from ppl import Variable
from ppl import Constraint_System, C_Polyhedron


class Polyhedron:
    """
    Convex Polyhedron.
    `_time` bounds is a pair (l, u) with lower and upper bound on time (None for infinity)
    """

    def __init__(self, t, ph: C_Polyhedron):
        # time bounds
        self._time_bounds = t
        # PPL C_Polyhedron
        self._ph = ph

    def __lt__(self, other):
        """
        Order polyhedra according to `sup(time_bounds)`
        """
        return self._time_bounds[1] < other._time_bounds[1]

    def __str__(self):
        return f'<{self._time_bounds} @ {self._ph.constraints()}>'


#
# class Var:
#     def __init__(self, idx, name=None):
#         self._var = PPLVariable(idx)
#         self._idx = idx
#         self._name = name
#
#     def idx(self):
#         return self._idx
#
#     def __hash__(self):
#         return self._idx
#
#     def __eq__(self, other):
#         return self.idx() == other.idx()


class PolyhedraSet:
    def __init__(self, *args):
        self._phs = list(args)

    def __str__(self):
        return f'{{{", ".join(map(str, self._phs))}}}'

class FormulaPolyhedron:
    """
    A pair of a PolyhedraSet and a variable which represents the value of a variable.
    """

    def __init__(self, var: Variable, phs: PolyhedraSet):
        self._var = var
        self._phs = phs

    def __str__(self):
        return f'{self._var} ==> {self._phs}'


class Formula2Polyhedra:
    def __init__(self):
        self._vars_num = 0
        self._var_to_idx = {}

    def _new_var(self, name=None):
        idx = self._vars_num
        v = Variable(idx)
        if name:
            self._var_to_idx[name] = idx

        self._vars_num += 1
        return v

    def _get_var(self, name):
        idx = self._var_to_idx.get(name)
        if idx is None:
            v = self._new_var(name)
        else:
            return Variable(idx)
        return v

    def _create_ph(self, bounds, *args):
        cs = Constraint_System()
        for a in args:
            cs.insert(a)
        return Polyhedron(bounds, C_Polyhedron(cs))

    def _term(self, formula, bounds):
        resvar = self._new_var()
        if isinstance(formula, (TimeVar, ValueVar)):
            return FormulaPolyhedron(
                resvar,
                PolyhedraSet(
                    self._create_ph(
                        (None, None), resvar == self._get_var(formula.name())
                    )
                ),
            )
        if isinstance(formula, (TimeConstant, ValueConstant)):
            print("FIXME: add bounds on the value from quantifiers")
            return FormulaPolyhedron(
                resvar,
                PolyhedraSet(
                    self._create_ph(
                        (None, None), resvar == formula.value()
                    )
                ),
            )


    def term(self, formula):
        return self._term(formula, (None, None))

    def translate(self, formula):
        def _translate(formula, lvl):
            if isinstance(formula, Term):
                print(formula)
                r = self.term(formula)
                print(r)
                print("----")

        # This is for testing now, in the real version
        # we do a manual top-down recursion
        formula.visit_dfs(_translate)
        print(self._var_to_idx)
