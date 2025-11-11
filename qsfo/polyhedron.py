from itertools import product

from sympy import (
    symbols,
    Symbol,
    simplify,
    reduce_inequalities,
    And,
    false,
    true,
    Interval as SymPyInterval,
    FiniteSet,
    EmptySet,
    Eq,
    LessThan,
)
from sympy.core.numbers import Infinity, NegativeInfinity

from qsfo.dbg import trace_calls


class Var(Symbol):
    pass


class Interval(SymPyInterval):
    def __new__(cls, start, end, lopen=False, ropen=False):
        return SymPyInterval.__new__(cls, start, end, lopen, ropen)

    def __str__(self):
        return f'{"<" if self.left_open else "["}{self.start} .. {self.end}{">" if self.right_open else "]"}'


INFTY = float("inf")
NEG_INFTY = float("-inf")
NO_BOUNDS = Interval(NEG_INFTY, INFTY)


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


def infer_eqs(C):
    """
    Merge a <= b, b <= a to a == b
    """
    new_C = []
    seen = set()
    eqs = set()
    for c in C:
        if c.rel_op in ("==", "<", ">"):
            new_C.append(c)  # strict ineq
            continue
        # if not isinstance(c, (Le, Lt, Ge, Gt)):
        #    new_c.append(c)
        assert c.rel_op in ("<=", ">="), c
        c = to_le(c)

        lhs, rhs = c.lhs, c.rhs
        if (rhs, lhs) in seen:
            eqs.add((rhs, lhs))
        else:
            seen.add((lhs, rhs))

    seen = seen.difference(eqs)

    return [(Eq(rhs, lhs)) for rhs, lhs in eqs] + [lhs <= rhs for lhs, rhs in seen]


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


def _get_bounds(term) -> Interval:
    op, lhs, rhs = term.rel_op, term.lhs, term.rhs
    if op == "==":
        if lhs.is_symbol and rhs.is_number:
            return lhs, Interval(rhs, rhs)
        elif rhs.is_symbol and lhs.is_number:
            return rhs, Interval(lhs, lhs)
    elif op in ("<=", "<"):
        if lhs.is_symbol and rhs.is_number:
            return lhs, Interval(NEG_INFTY, rhs, lopen=False, ropen=(op == "<"))
        elif rhs.is_symbol and lhs.is_number:
            return rhs, Interval(lhs, INFTY, lopen=(op == "<"), ropen=False)
    elif op in (">=", ">"):
        if lhs.is_symbol and rhs.is_number:
            return lhs, Interval(rhs, INFTY, lopen=(op == ">"), ropen=False)
        elif rhs.is_symbol and lhs.is_number:
            return rhs, Interval(NEG_INFTY, lhs, lopen=False, ropen=(op == ">"))

    return None, None


def get_bounds(C: list) -> dict:
    """
    Scan the list of constraints and get integer bounds
    on the variables.

    The function could be done more efficient (not storing the lists of values, but computing
    min/max on the fly), but we'll see if it is necessary.

    TODO: use Interval from sympy, to handle also strict inequalities
    """
    # eqs = {}
    bounds = {}
    for term in C:
        sym, B = _get_bounds(term)
        if sym is None:
            continue

        bounds[sym] = bounds.get(sym, NO_BOUNDS).intersect(B)

    return bounds


def remove_redundant_constraints(C) -> list:
    B = get_bounds(C)
    if not B:
        return C

    return _remove_redundant_constraints(C, B)


def _remove_redundant_constraints(C: list, bounds: dict) -> list:
    # FIXME
    # return C

    new_C = set()
    # add bounds for these variables to the constraints
    add_bounds_for = set()
    for term in C:
        op, lhs, rhs = term.rel_op, term.lhs, term.rhs
        # if op not in ("==", "<=", ">=", "<", ">"):
        # NOTE: the strict inequalities are not handled here yet
        if op not in ("==", "<=", ">="):
            new_C.add(term)
            continue

        if lhs.is_symbol and lhs in bounds and rhs.is_number:
            # drop this term and add the bound instead
            add_bounds_for.add(lhs)
        elif rhs.is_symbol and rhs in bounds and lhs.is_number:
            # drop this term and add the bound instead
            add_bounds_for.add(rhs)
        else:
            new_C.add(term)

    for v in add_bounds_for:
        l, u = bounds[v]
        if l is not None:
            new_C.add(l <= v)
        if u is not None:
            new_C.add(v <= u)

    return new_C


def simplify_constraints(C: list):
    expr = simplify(And(*C))
    elems = expr.args
    if expr == false:
        return []
    assert expr != true, f"And'ed constraints simplified to True: {C}"
    assert elems != (), (elems, expr, type(expr))

    if isinstance(expr, And):
        # if eq_break:
        #    C = [c for e in expr.args for c in break_eqs((e,))]
        # else:
        return list(expr.args)
    elif isinstance(expr, Eq):
        # if eq_break:
        #    return [LessThan(elems[0], elems[1]), LessThan(elems[1], elems[0])]
        return [expr]
    else:
        # simplified to a single expression
        return list(elems)


def complement_term(term, timevar, time_bounds):
    """
    Return a list of terms whose union describe the complementary constraints.
    """
    C = [term.negated]
    if timevar and time_bounds:
        if isinstance(time_bounds, FiniteSet):
            C.append(Eq(timevar, next(iter(time_bounds))))
        else:
            C.append(time_bounds.start <= timevar)
            C.append(timevar <= time_bounds.end)

    return C


# op, lhs, rhs = term.rel_op, term.lhs, term.rhs
# if op == "==":
#    return [lhs < rhs, rhs < lhs]
# elif op == "<=":
#    return [lhs > rhs]
# elif op == "<":
#    return [lhs >= rhs]
# elif op == ">":
#    return [lhs <= rhs]
# elif op == ">=":
#    return [lhs < rhs]


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


class Polyhedron:
    """
    N-dimensional Polyhedron (bounded polytope).

    `constraints` is a list of linear sympy polynomials.
    """

    def __init__(
        self, constraints: list, variables=None, time_bounds: Interval = NO_BOUNDS
    ):
        # matrix of inequalities
        assert () not in constraints, constraints

        # on the first call of __str__, we cache the string (as constraints and variables do not change)
        # this is to make str, but mainly __hash__ more efficient as __hash__ uses the string
        # NOTE: must be here in the case we return from __init__ early
        self.__str = None

        # time bounds -- used to sort polyhedra during operations
        self._time_bounds = time_bounds
        self._vars = set()

        # constant bounds on variables used to simplify the operations on this polyhedron
        # self._bounds = {}
        self._constraints = set()
        if not self._add_constraints(constraints):
            # the constraints are unsat, clear them and bail out
            # without setting `_vars`, which will result in the empty polyhedron
            self._constraints = set()
            return

        self._vars = variables or set(
            v for c in self._constraints for v in c.atoms(Var)
        )
        assert all(isinstance(v, Symbol) for v in self._vars), self._vars
        assert (
            not self._constraints or self._vars
        ), f"Have constraints but no vars: {self}"

    def _add_constraints(self, constraints):
        # Gather constraints that bound the polyhedron by a constant.
        # Do not add them directly. Rather gather all of them first in a set
        # add only the intersected constraints at the end.
        bounds = {}  # self._bounds
        for c in constraints:
            if c == True:
                continue
            elif c == False:
                return False
            sym, B = _get_bounds(c)
            if sym is not None:
                B = bounds.get(sym, NO_BOUNDS).intersect(B)
                if B == EmptySet:
                    # unsat constraints
                    return False

                bounds[sym] = B
                continue

            # if we have no bound, just copy the constraint
            self._constraints.add(c)

        for sym, I in bounds.items():
            if isinstance(I, FiniteSet):
                # aaaah, I hate the automatic type conversions that SymPy does...
                # we need to check if the interval is not a single number.
                self._constraints.add(Eq(sym, next(iter(I))))
                continue

            if not I.is_left_unbounded:
                self._constraints.add(I.start < sym if I.left_open else I.start <= sym)
            if not I.is_right_unbounded:
                self._constraints.add(sym < I.end if I.right_open else sym <= I.end)

        return True

    def vars(self):
        return self._vars

    def is_empty(self):
        return not self._vars

    def is_universal(self):
        return self._vars and not self._constraints

    def time_bounds(self):
        return self._time_bounds

    def simplify(self) -> "Polyhedron":
        if self.is_empty() or self.is_universal():
            # do not return `self`, return a copy
            return Polyhedron(self.constraints(), variables=self.vars())

        C = simplify_constraints(self._constraints)
        if not C:
            # unsat constraints
            return Polyhedron([])
        return Polyhedron(C, variables=self.vars(), time_bounds=self._time_bounds)

    def intersection(self, rhs: "Polyhedron", ignore_variables=True):
        """
        Do intersection of two polyhedra. If `ignore_variables` is `True`, the operation first
        "extends" both polyhedra to be in the same dimensions (the same set of variables)
        and then do the intersection.

        :param ignore_variables:  if set to `True`, the operation assumes that any variable missing
                                  in `self` or `rhs` is present and unconstraint. If set to False,
                                  the intersection works as usual: a missing variable means that there
                                  is no intersection along that dimension, so the whole intersection
                                  is empty.
        """
        # TODO: cache a hash of `_vars` to make this comparison more efficient?
        if not ignore_variables and self.vars() != rhs.vars():
            return Polyhedron([])

        if rhs.is_empty() or self.is_empty():
            return Polyhedron([])

        # print("FIXME: simplify and return empty/universal if possible")
        # C = simplify_constraints(self._constraints + rhs._constraints)
        C = self._constraints.copy()
        C.update(rhs._constraints)
        # C = remove_redundant_constraints(C)
        # if not C:
        #     # unsat constraints
        #     return Polyhedron([])

        return Polyhedron(
            C,
            # if we do not ignore variables, then self.vars() == rhs.vars(), so skip the union
            variables=(
                self.vars().union(rhs.vars()) if ignore_variables else self.vars()
            ),
            time_bounds=self._time_bounds.intersect(rhs._time_bounds),
        )

    def complement(self, timevar=None) -> list:
        """
        Return a list of Polyhedra that describe the complement of this polyhedron.

        :param timevar:  if this param is given, each element of the complement is constrained
                         to its time domain (e.g., assuming that the time bounds are not complemented).
        """
        return [
            Polyhedron([cc], variables=self.vars(), time_bounds=self._time_bounds)
            for c in self._constraints
            for cc in complement_term(c, timevar, self._time_bounds)
        ]

    @trace_calls
    def eliminate(self, var: Var, do_simplify=False, restore_eqs=False):
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
        if restore_eqs:
            constraints = infer_eqs(constraints)
        return Polyhedron(constraints, variables, time_bounds=self._time_bounds)

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

    def __eq__(self, rhs: "Polyhedron") -> bool:
        # TODO: use __str too? It should work, right?
        return self._vars == rhs._vars and self._constraints == rhs._constraints

    def __hash__(self) -> bool:
        if not self.__str:
            self.__create_str()
        return hash(self.__str)

    def __create_str(self):
        if self.is_empty():
            self.__str = "∅"
        elif self.is_universal():
            self.__str = f"UNIV({self._vars})"
        else:
            self.__str = f'{{{", ".join(map(str, self._constraints))}}} over {self._vars} @ {self._time_bounds}'

    def __str__(self):
        if not self.__str:
            self.__create_str()

        return self.__str


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
