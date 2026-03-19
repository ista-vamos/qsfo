from itertools import product
import ppl
from fractions import Fraction
from math import lcm

from sympy import (
    symbols,
    Symbol,
    simplify as sympy_simplify,
    reduce_inequalities,
    And,
    false,
    true,
    Interval as SymPyInterval,
    FiniteSet,
    Eq,
    Le,
    Ge,
    Lt,
    Gt,
)
from sympy.core.numbers import Infinity, NegativeInfinity
from sympy.logic.boolalg import BooleanFalse, BooleanTrue

# from qsfo.dbg import trace_calls, add_to_trace

FRACTIONS_PREC = 1000000


class Var(Symbol):
    pass


class Interval(SymPyInterval):
    def __new__(cls, start, end, lopen=False, ropen=False):
        return SymPyInterval.__new__(cls, start, end, lopen, ropen)

    def __str__(self):
        return f"{'<' if self.left_open else '['}{self.start} .. {self.end}{'>' if self.right_open else ']'}"


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


def _cmp_numbers(lhs, rhs) -> int | None:
    """Compare two numeric SymPy/Python values.

    Returns 1 if lhs > rhs, -1 if lhs < rhs, 0 if lhs == rhs, and None if
    comparison cannot be established cheaply.
    """

    if lhs == rhs:
        return 0
    try:
        if bool(lhs > rhs):
            return 1
        if bool(lhs < rhs):
            return -1
    except TypeError:
        return None
    return None


def _tighten_lower(current, candidate):
    """Keep the tighter lower bound (bigger value, stricter on ties)."""

    if current is None:
        return candidate
    cmp = _cmp_numbers(candidate[0], current[0])
    if cmp is None:
        return None
    if cmp > 0:
        return candidate
    if cmp < 0:
        return current
    return (current[0], current[1] or candidate[1])


def _tighten_upper(current, candidate):
    """Keep the tighter upper bound (smaller value, stricter on ties)."""

    if current is None:
        return candidate
    cmp = _cmp_numbers(candidate[0], current[0])
    if cmp is None:
        return None
    if cmp < 0:
        return candidate
    if cmp > 0:
        return current
    return (current[0], current[1] or candidate[1])


def _extract_linear_bound(term, var):
    """Try extracting a bound on `var` from a linear relational constraint.

    Returns:
      - ("lower", bound, strict) for var >/>= bound
      - ("upper", bound, strict) for var </<= bound
      - ("eq", bound, False) for var == bound
      - None if this is not a supported simple linear bound
    """

    op = getattr(term, "rel_op", None)
    if op not in ("<", "<=", ">", ">=", "=="):
        return None

    expr = (term.lhs - term.rhs).collect(var)
    coeff = expr.coeff(var)
    if coeff == 0:
        return None

    rest = expr - coeff * var
    if rest.has(var):
        return None
    if rest.free_symbols:
        return None

    sign = _cmp_numbers(coeff, 0)
    if sign is None or sign == 0:
        return None

    bound = -rest / coeff
    if not getattr(bound, "is_number", False):
        return None

    if op == "==":
        return ("eq", bound, False)

    strict = op in ("<", ">")
    if op in ("<", "<="):
        return ("upper", bound, strict) if sign > 0 else ("lower", bound, strict)
    return ("lower", bound, strict) if sign > 0 else ("upper", bound, strict)


def _tri_bool(term) -> bool | None:
    """Return concrete bool for SymPy/Python booleans, else None."""

    if term is True or term is False:
        return term
    if isinstance(term, (BooleanTrue, BooleanFalse)):
        return bool(term)
    return None


def constraints_time_set_fast(constraints, timevar: Var):
    """Fast path for extracting a 1D time set from simple constraints.

    Returns Interval/FiniteSet for constraints over `timevar` only.
    Returns None when constraints are multi-variate or not in the supported
    simple linear form; callers should then fall back to the generic SymPy
    `as_set()` path.
    """

    if timevar is None:
        return None

    lower = None  # tuple(bound_value, is_strict)
    upper = None  # tuple(bound_value, is_strict)
    saw_time_constraint = False

    for term in constraints:
        tb = _tri_bool(term)
        if tb is True:
            continue
        if tb is False:
            return None

        if not hasattr(term, "free_symbols"):
            return None
        vars_in_term = term.free_symbols
        if not vars_in_term:
            # A non-boolean constant term (or otherwise unsupported expression):
            # bail out and let the generic path decide.
            return None
        if vars_in_term != {timevar}:
            return None

        parsed = _extract_linear_bound(term, timevar)
        if parsed is None:
            return None
        saw_time_constraint = True

        kind, bound, is_strict = parsed
        if kind == "lower":
            lower = _tighten_lower(lower, (bound, is_strict))
            if lower is None:
                return None
        elif kind == "upper":
            upper = _tighten_upper(upper, (bound, is_strict))
            if upper is None:
                return None
        else:
            lower = _tighten_lower(lower, (bound, False))
            upper = _tighten_upper(upper, (bound, False))
            if lower is None or upper is None:
                return None

        if lower is not None and upper is not None:
            cmp = _cmp_numbers(lower[0], upper[0])
            if cmp is None:
                return None
            if cmp > 0:
                return None
            if cmp == 0 and (lower[1] or upper[1]):
                return None

    if not saw_time_constraint:
        return None

    if lower is not None and upper is not None:
        cmp = _cmp_numbers(lower[0], upper[0])
        if cmp is None:
            return None
        if cmp == 0 and not lower[1] and not upper[1]:
            return FiniteSet(lower[0])

    start = lower[0] if lower is not None else NEG_INFTY
    end = upper[0] if upper is not None else INFTY
    left_open = lower[1] if lower is not None else False
    right_open = upper[1] if upper is not None else False
    return Interval(start, end, left_open, right_open)


def get_bounds(C: list) -> dict:
    """
    Scan the list of constraints and get integer bounds
    on the variables.

    The function could be done more efficient (not storing the lists of values, but computing
    min/max on the fly), but we'll see if it is necessary.
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
    raise RuntimeError("This might be buggy")
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
    expr = sympy_simplify(And(*C))
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


def frac(x):
    # FIXME: use better precision
    # return Fraction(str(x))
    return Fraction(float(x)).limit_denominator(FRACTIONS_PREC)


def coef_with_denom(c: Fraction, denom):
    return int(c.numerator * (denom / c.denominator))


def sympy_to_ppl_expr(expr, variables):
    """
    Convert a SymPy linear inequality (Le, Ge, Lt, Gt) to a ppl.Constraint

    `variables` is a list of (sympy var, PPL var) tuples and `var_map`
    is a mapping made from this list.
    """
    # Extract coefficients
    coeff_dict = {k: frac(v) for k, v in expr.as_coefficients_dict().items()}
    constant = frac(coeff_dict.get(1, 0))

    denom = lcm(*(v.denominator for v in coeff_dict.values()), constant.denominator)

    # Create PPL expression
    coeffs = {
        pplv.id(): coef_with_denom(coeff_dict.get(v, frac(0)), denom)
        for v, pplv in variables
    }
    constant = coef_with_denom(constant, denom)
    return ppl.Linear_Expression(coeffs, constant)


def sympy_to_ppl_constraint(sympy_expr, variables):
    """
    Convert a SymPy linear inequality (Le, Ge, Lt, Gt) to a ppl.Constraint

    `variables` is a list of (sympy var, PPL var) tuples and `var_map`
    is a mapping made from this list.
    """
    # move all terms to LHS
    expr = sympy_to_ppl_expr(sympy_expr.lhs - sympy_expr.rhs, variables)

    # Restore the inequality
    if isinstance(sympy_expr, Le):
        return ppl.Constraint(expr <= 0)
    elif isinstance(sympy_expr, Ge):
        return ppl.Constraint(expr >= 0)
    elif isinstance(sympy_expr, Lt):
        return ppl.Constraint(expr < 0)
    elif isinstance(sympy_expr, Gt):
        return ppl.Constraint(expr > 0)
    elif isinstance(sympy_expr, Eq):
        return ppl.Constraint(expr == 0)

    raise ValueError(f"Unsupported SymPy inequality type: {sympy_expr}")


def ppl_constraint_to_sympy(ppl_c, variables):
    monomials = [
        c * v for (c, (v, _)) in zip(ppl_c.coefficients(), variables) if c != 0
    ]
    lhs = sum(monomials) + ppl_c.inhomogeneous_term()
    if ppl_c.is_strict_inequality():
        return lhs > 0
    if ppl_c.is_equality():
        return Eq(lhs, 0)

    assert ppl_c.is_nonstrict_inequality(), ppl_c
    return lhs >= 0


def complement_term(term, timevar, time_bounds):
    """
    Yield lists of constraints whose union describe the complement of the given term
    """

    if timevar and time_bounds:
        if isinstance(time_bounds, FiniteSet):
            timebounds = [Eq(timevar, next(iter(time_bounds)))]
        else:
            timebounds = [time_bounds.start <= timevar, timevar <= time_bounds.end]
    else:
        timebounds = []

    if isinstance(term, Eq):
        # in this case we yield two sets of constraints
        for C in [term.lhs < term.rhs], [term.rhs < term.lhs]:
            yield C + timebounds
        return

    # only one set of constraints
    yield [term.negated] + timebounds


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
        # FIXME: time bounds are not implemented now
        self._time_bounds = NO_BOUNDS  # time_bounds
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
        assert not self._constraints or self._vars, (
            f"Have constraints but no vars: {self}"
        )
        # assert constraints != [True] or self._vars, "Universal poly that became empty, use variables="

        if constraints and not self._constraints and not self._vars:
            # we had constraints but they reduced to True which was dropped..
            raise RuntimeError(
                "Universal poly that became empty because we do not know variables"
            )

        # self.reduce()

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
            # sym, B = _get_bounds(c)
            # if sym is not None:
            #    B = bounds.get(sym, NO_BOUNDS).intersect(B)
            #    if B == EmptySet:
            #        # unsat constraints
            #        return False
            #
            #    bounds[sym] = B
            #    continue

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
        raise NotImplementedError("Not implemented now")
        return self._time_bounds

    def simplify_constraints(self) -> "Polyhedron":
        if self.is_empty() or self.is_universal():
            # do not return `self`, return a copy
            return Polyhedron(self.constraints(), variables=self.vars())

        C = simplify_constraints(self._constraints)
        if not C:
            # unsat constraints
            return Polyhedron([])
        return Polyhedron(C, variables=self.vars(), time_bounds=self._time_bounds)

    def intersection(self, rhs: "Polyhedron", ignore_variables=True) -> "Polyhedron":
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
            Polyhedron(cc, variables=self.vars(), time_bounds=self._time_bounds)
            for c in self._constraints
            for cc in complement_term(c, timevar, self._time_bounds)
        ]

    # @trace_calls
    def eliminate_ppl(self, elim_vars: list[Var]):
        raise NotImplementedError()
        poly, variables = self.to_ppl_polyhedron()
        print(f"Elim {elim_vars} from {poly.constraints()}")
        print(dir(poly))
        poly = poly.existentially_quantify(elim_vars)
        print(f" ==> {poly.constraints()}")

        return Polyhedron.from_ppl_polyhedron(poly, variables)

    # @trace_calls
    def eliminate(self, var: Var, do_simplify=False, restore_eqs=False) -> "Polyhedron":
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
                    term = t_lhs.lhs < t_rhs.rhs
                    # term = simplify(t_lhs.lhs < t_rhs.rhs)
                else:
                    assert t_lhs.rel_op == t_rhs.rel_op == "<=", (t_lhs, t_rhs)
                    term = t_lhs.lhs <= t_rhs.rhs
                    # term = simplify(t_lhs.lhs <= t_rhs.rhs)
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

    def to_ppl_polyhedron(self) -> tuple["Polyhedron", list]:
        """ """
        # FIXME: return empty PPL poly
        if self.is_empty():
            return None, []

        vars_num = len(self.vars())
        # fix order of variables and create PPL variables for them
        variables = [(v, ppl.Variable(n)) for n, v in enumerate(self.vars())]
        # create a mapping for efficient lookup
        var_map = {v: pplv for v, pplv in variables}
        C = ppl.Constraint_System()
        for c in self._constraints:
            ppl_c = sympy_to_ppl_constraint(c, variables)
            C.insert(ppl_c)

        poly = ppl.NNC_Polyhedron(C)
        if poly.is_empty():
            return None, []

        return poly, variables

    @staticmethod
    def from_ppl_polyhedron(poly, variables):
        return Polyhedron(
            [ppl_constraint_to_sympy(c, variables) for c in poly.constraints()]
        )

    def reduce(self) -> "Polyhedron":
        """
        This is **in-place** operation, make sure to copy the polyhedron
        if this one cannot be modified.
        """
        if self.is_empty():
            return self

        P, variables = self.to_ppl_polyhedron()
        if P is None:
            self._vars = set()
            self._constraints = set()
            return self

        if P.is_universe():
            self._constraints = set()
            assert self._vars, "We must have variables.."
            return self

        # update the constraints and variables
        self._constraints = {
            ppl_constraint_to_sympy(c, variables) for c in P.constraints()
        }
        self._vars = set(v for c in self._constraints for v in c.atoms(Var))

        assert self._constraints or self._vars, "The Polyhedron must be non-empty"

        return self

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
        # FIXME
        # if not self.__str:
        #    self.__create_str()
        self.__create_str()
        return hash(self.__str)

    def __create_str(self):
        if self.is_empty():
            self.__str = "∅"
        elif self.is_universal():
            self.__str = f"UNIV({self._vars})"
        else:
            assert self._constraints
            assert self._vars
            # self.__str = f'{{{", ".join(map(str, self._constraints))}}} over {self._vars} @ {self._time_bounds}'
            self.__str = (
                f"{{{', '.join(map(str, self._constraints))}}} over {self._vars}"
            )

    def __str__(self):
        # if not self.__str:
        #    self.__create_str()

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
