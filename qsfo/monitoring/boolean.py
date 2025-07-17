from qsfo.formula import *

class FormulaPolyhedron:
    """
    A pair of a PolyhedronSet and a variable which represents the value of a variable.
    """

    def __init__(self, var: Variable, phs: PolyhedronSet):
        self._var = var
        self._phs = phs

    def __str__(self):
        return f'{self._var} ==> {self._phs}'


class PolyhedronSet:
    """
    A set of polyhedra describing a part of the n-dimensional space.
    The interpretation is the _union_ of all polyhedra.
    """
    def __init__(self, *args):
        self._phs = list(args)

    def add(self, ph):
        self._phs.append(ph)

    def __str__(self):
        return f'{{{", ".join(map(str, self._phs))}}}'


class Formula2Polyhedron:
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
                PolyhedronSet(
                    self._create_ph(
                        (None, None), resvar == self._get_var(formula.name())
                    )
                ),
            )
        if isinstance(formula, (TimeConstant, ValueConstant)):
            print("FIXME: add bounds on the value from quantifiers")
            return FormulaPolyhedron(
                resvar,
                PolyhedronSet(
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
