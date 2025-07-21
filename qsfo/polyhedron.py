from itertools import product

from sympy import symbols, Symbol, simplify, reduce_inequalities, And
from sympy.core.numbers import Infinity, NegativeInfinity

Var = Symbol


def _break_eqs(C: list) -> list:
    for c in C:
        if c.rel_op == "==":
            yield c.lhs <= c.rhs
            yield c.rhs <= c.lhs
        else:
            yield c


def break_eqs(C):
    # NOTE: return a list so that we can check for the emptiness
    return list(_break_eqs(C))


def to_le(term):
    """
    Convert the inequality to be less-or-equal
    """
    assert term.rel_op in ("<=", ">=", "<", ">"), term
    if term.rel_op == ">=":
        term = term.rhs <= term.lhs
    elif term.rel_op == ">":
        term = term.rhs < term.lhs

    assert term.rel_op in ("<=", "<")
    return term


def simplify_constraints(C: list):
    expr = simplify(And(*C))
    elems = expr.args
    if expr is False:
        return []
    assert expr is not True, f"And'ed constraints simplified to True: {C}"

    if isinstance(expr, And):
        return [c for e in expr.args for c in break_eqs((e,))]
    else:
        # simplified to a single expression
        return [elems]


class Polyhedron:
    """
    N-dimensional Polyhedron (bounded polytope).

    `constraints` is a list of linear sympy polynomials.
    """

    def __init__(self, constraints: list, variables=None):
        # matrix of inequalities
        self._constraints = constraints
        self._vars = variables or set(v for c in constraints for v in c.atoms(Var))

    def vars(self):
        return self._vars

    def is_empty(self):
        return not self._vars

    def intersection(self, rhs: "Polyhedron"):
        print("FIXME: simplify and return empty/universal if possible")
        # C = simplify_constraints(self._constraints + rhs._constraints)
        C = self._constraints + rhs._constraints
        if not C:
            # unsat constraints
            return Polyhedron([])
        return Polyhedron(C, variables=self.vars().union(rhs.vars()))

    def eliminate(self, var: Var):
        if len(self.vars()) == 1:
            raise RuntimeError(
                "Eliminating the last variable will yield an empty Polyhedron"
            )

        # filter out inequalities that does not have `var`, these will be preserved
        preserved, to_reduce = [], []
        for c in self._constraints:
            (to_reduce if c.has(var) else preserved).append(c)

        # do the Fourier-Motzkin elimination
        lefts, rights = [], []
        solved_for_var = break_eqs(
            reduce_inequalities(to_reduce, var).args
        )  # [term for ineq in break_eqs(to_reduce) for term in solve(ineq, var).args]
        # print("S", solved_for_var)
        if not solved_for_var:
            # Inequalities have no solution
            return Polyhedron([], set())

        for term in solved_for_var:
            # these do not contribute to the result
            if term.has(Infinity) or term.has(NegativeInfinity):
                continue
            term = to_le(term)

            if term.lhs.has(var):
                assert not term.rhs.has(var), term
                assert term.lhs == var, "Term is not just the symbol"
                rights.append(term)
            elif term.rhs.has(var):
                assert term.rhs == var, "Term is not just the symbol"
                lefts.append(term)

        reduced = []
        if lefts and rights:
            for t_lhs, t_rhs in product(lefts, rights):
                assert t_lhs.rhs == t_rhs.lhs == var, (var, t_lhs, t_rhs)

                if t_lhs.rel_op == "<" or t_rhs.rel_op == "<":
                    term = simplify(t_lhs.lhs < t_rhs.rhs)
                else:
                    assert t_lhs.rel_op == t_rhs.rel_op == "<=", (t_lhs, t_rhs)
                    term = simplify(t_lhs.lhs <= t_rhs.rhs)
                if term == True:
                    continue
                if term == False:
                    return Polyhedron([])
                reduced.append(term)

        constraints = preserved + reduced
        assert not any(c.has(var) for c in constraints), (var, constraints)
        variables = self.vars().copy()
        variables.remove(var)
        return Polyhedron(constraints, variables)

    def constraints(self):
        return self._constraints

    def substitute_constraints(self, S: dict) -> list:
        """
        Perform substitution in the constraints, return the modified constraints.
        """
        S_list = list(S.items())
        return [c.subs(S_list) for c in self._constraints]

    def substitute(self, S: dict, variables=None):
        return Polyhedron(self.substitute_constraints(S), variables)

    def __str__(self):
        return f'{{{", ".join(map(str, self._constraints))}}} in {self._vars}'
        # return f'{{{", ".join(map(str, self._constraints))}}}'


class PolyhedronWithTime(Polyhedron):
    """
    Polyhedron with explicit bounds on the time variable.
    """

    def __init__(self, timevar: Var, bounds: tuple, constraints: list, variables=None):
        super().__init__(constraints, variables)
        assert isinstance(bounds, tuple), bounds
        self._timevar = timevar
        self._bounds = bounds

        if bounds[0] is not None:
            self._constraints.append(timevar >= bounds[0])
        if bounds[1] is not None:
            self._constraints.append(timevar <= bounds[1])
        if bounds[0] is not None or bounds[1] is not None:
            self._vars.add(timevar)

    def substitute(self, S: dict, variables=None):
        return PolyhedronWithTime(
            self._timevar, self._bounds, self.substitute_constraints(S), variables
        )


if __name__ == "__main__":
    x, y, z = symbols("x y z")

    P1 = Polyhedron(
        [x - y <= 1, 2 * x <= 1, 2 * x >= 1, -x <= 3, x + z >= 3, z + y <= x]
    )
    print("P1:", P1)
    P = P1.eliminate(x)
    print("elim x", P)
    print("elim z")
    print(P.eliminate(z))
    print("elim y")
    print(P.eliminate(y))

    print("----")
    P = P1
    print("P1:", P1)
    P = P.eliminate(y)
    print("elim y", P)
    print("elim z")
    print(P.eliminate(z))
    print("elim x")
    print(P.eliminate(x))
    print("----")
    P = P1
    print("P1:", P1)
    P = P.eliminate(z)
    print("elim z", P)
    print("elim y")
    print(P.eliminate(y))
    print("elim x")
    print(P.eliminate(x))
    print("----")
    print("----")
    P = Polyhedron([x + y <= 1, x - y <= 0, x >= 0, 0 <= y, y <= 1])
    print(P)
    print(P.eliminate(y))
