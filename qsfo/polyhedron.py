from itertools import product

from sympy import symbols, Symbol, simplify, reduce_inequalities, And, false, true, Interval as SymPyInterval
from sympy.core.numbers import Infinity, NegativeInfinity

Var = Symbol

class Interval(SymPyInterval):
    def __new__(cls, start, end, lopen=False, ropen=False):
        return SymPyInterval.__new__(cls, start, end, lopen, ropen)

    def __str__(self):
        return f'{"<" if self.left_open else "["}{self.start} .. {self.end}{">" if self.right_open else "]"}'



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


def get_bounds(C: list) -> dict:
    """
    Scan the list of constraints and get integer bounds
    on the variables.

    The function could be done more efficient (not storing the lists of values, but computing
    min/max on the fly), but we'll see if it is necessary.

    TODO: use Interval from sympy, to handle also strict inequalities
    """
    # eqs = {}
    lb = {}
    ub = {}
    for term in C:
        op, lhs, rhs = term.rel_op, term.lhs, term.rhs
        if op == "==":
            if lhs.is_symbol and rhs.is_constant:
                ub.setdefault(lhs, []).append(rhs)
                lb.setdefault(lhs, []).append(rhs)
                # eqs.setdefault(lhs, []).append(rhs)
            elif rhs.is_symbol and lhs.is_constant:
                ub.setdefault(rhs, []).append(lhs)
                lb.setdefault(rhs, []).append(lhs)
                # eqs.setdefault(rhs, []).append(lhs)
        elif op in ("<=", "<"):
            if lhs.is_symbol and rhs.is_constant:
                ub.setdefault(lhs, []).append(rhs)
            elif rhs.is_symbol and lhs.is_constant:
                lb.setdefault(rhs, []).append(lhs)
        elif op in (">=", ">"):
            if lhs.is_symbol and rhs.is_constant:
                lb.setdefault(lhs, []).append(rhs)
            elif rhs.is_symbol and lhs.is_constant:
                ub.setdefault(rhs, []).append(lhs)

    bounds = {}
    variables = set(iter(lb.keys()))
    variables.update(iter(ub.keys()))

    for v in variables:
        bounds[v] = (max(lb.get(v, []), default=None), min(ub.get(v, []), default=None))

    return bounds


def remove_redundant_constraints(C: list) -> list:
    B = get_bounds(C)
    if not B:
        return C

    return _remove_redundant_constraints(C, B)


def _remove_redundant_constraints(C: list, bounds: dict) -> list:
    new_C = []
    # add bounds for these variables to the constraints
    add_bounds_for = set()
    for term in C:
        op, lhs, rhs = term.rel_op, term.lhs, term.rhs
        # if op not in ("==", "<=", ">=", "<", ">"):
        # NOTE: the strict inequalities are not handled here yet
        if op not in ("==", "<=", ">="):
            new_C.append(term)
            continue

        if lhs.is_symbol and lhs in bounds and rhs.is_constant:
            # drop this term and add the bound instead
            add_bounds_for.add(lhs)
        elif rhs.is_symbol and rhs in bounds and lhs.is_constant:
            # drop this term and add the bound instead
            add_bounds_for.add(rhs)
        else:
            new_C.append(term)

    for v in add_bounds_for:
        l, u = bounds[v]
        if l is not None:
            new_C.append(l <= v)
        if u is not None:
            new_C.append(v <= u)

    return new_C


def simplify_constraints(C: list, eq_break=True):
    expr = simplify(And(*C))
    elems = expr.args
    if expr == false:
        return []
    assert expr != true, f"And'ed constraints simplified to True: {C}"
    assert elems != (), (elems, expr, type(expr))

    if isinstance(expr, And):
        if eq_break:
            C = [c for e in expr.args for c in break_eqs((e,))]
        else:
            C = list(expr.args)
        return remove_redundant_constraints(C)
    else:
        # simplified to a single expression
        return [elems]


def complement_term(term):
    """
    Return a list of terms whose union describe the complementary constraints.
    """
    op, lhs, rhs = term.rel_op, term.lhs, term.rhs
    if op == "==":
        return [lhs < rhs, rhs < lhs]
    elif op == "<=":
        return [lhs > rhs]
    elif op == "<":
        return [lhs >= rhs]
    elif op == ">":
        return [lhs <= rhs]
    elif op == ">=":
        return [lhs < rhs]


def solve_for_variable(to_reduce, var) -> list:
    """
    Solve inequalities for a single variable.
    """
    if not to_reduce:
        return []

    res = reduce_inequalities(to_reduce, var)
    if isinstance(res, And):
        C = [a for a in res.args]
    else:
        C = [res]

    if false in C:
        return false

    if C == [true]:
        return true

    return C


INFTY = float("inf")
NEG_INFTY = float("-inf")
NO_BOUNDS = Interval(NEG_INFTY, INFTY)

class Polyhedron:
    """
    N-dimensional Polyhedron (bounded polytope).

    `constraints` is a list of linear sympy polynomials.
    """

    def __init__(self, constraints: list, variables=None, bounds: Interval = NO_BOUNDS):
        # matrix of inequalities
        assert () not in constraints, constraints

        self._constraints = constraints
        self._vars = variables or set(v for c in constraints for v in c.atoms(Var))
        # time bounds -- used to sort polyhedra during operations
        self._bounds = bounds

    def vars(self):
        return self._vars

    def is_empty(self):
        return not self._vars

    def is_universal(self):
        return self._vars and not self._constraints

    def time_bounds(self):
        return self._bounds

    def simplify(self, eq_break=True) -> "Polyhedron":
        if self.is_empty() or self.is_universal():
            return Polyhedron(self.constraints(), variables=self.vars())

        C = simplify_constraints(self._constraints, eq_break)
        if not C:
            # unsat constraints
            return Polyhedron([])
        return Polyhedron(C, variables=self.vars(), bounds=self._bounds)

    def intersection(self, rhs: "Polyhedron"):
        # print("FIXME: simplify and return empty/universal if possible")
        # C = simplify_constraints(self._constraints + rhs._constraints)
        C = self._constraints + rhs._constraints
        if not C:
            # unsat constraints
            return Polyhedron([])
        return Polyhedron(C, variables=self.vars().union(rhs.vars()),
                          bounds=self._bounds.intersect(rhs._bounds))

    def complement(self) -> list:
        """
        Return a list of Polyhedra that describe the complement of this polyhedron.
        """
        print("FIXME: compute bounds on complemented polyhedra (at least for trace segments)")
        return [
            Polyhedron([cc], variables=self.vars())
            for c in self._constraints
            for cc in complement_term(c)
        ]

    def eliminate(self, var: Var, do_simplify=False):
        """
        Eliminate the variable `var` from this polyhedron.
        We use Fourier-Motzkin elimination for now.
        Simplify the final polyhedron constraints if `simplify` is set to True.
        """
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
        solved_for_var = solve_for_variable(to_reduce, var)
        # [term for ineq in break_eqs(to_reduce) for term in solve(ineq, var).args]
        # print("S", solved_for_var)
        if solved_for_var == false:
            # Inequalities have no solution
            return Polyhedron([], set())
        if solved_for_var == true:
            # Inequalities are universally satisfied
            return Polyhedron([], self.vars())

        for term in break_eqs(solved_for_var):
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
        if do_simplify:
            constraints = simplify_constraints(constraints)
        return Polyhedron(constraints, variables, bounds=self._bounds)

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
        if self.is_empty():
            return "∅"
        if self.is_universal():
            return f"UNIV({self._vars})"
        return f'{{{", ".join(map(str, self._constraints))}}} over {self._vars} @ {self._bounds}'
        # return f'{{{", ".join(map(str, self._constraints))}}}'


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
    print(P.eliminate(y).simplify())
