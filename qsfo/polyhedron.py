from itertools import product
import ppl
from fractions import Fraction
from math import lcm

from qsfo.sym import (
    Var,
    Relation,
    Interval,
    FiniteSet,
    EmptySet,
    Eq,
    Le,
    Ge,
    Lt,
    Gt,
    frac,
    sym_num,
    _to_sym,
    expr_has,
    expr_subs,
    expr_free_symbols,
    expr_collect,
    expr_coefficient,
    expr_replace,
    expr_is_symbol,
    expr_to_var,
    expr_to_comparable,
    expr_is_inf,
    _is_constant,
    _make_rel,
)

# from qsfo.dbg import trace_calls, add_to_trace

FRACTIONS_PREC = 1000000

INFTY = float("inf")
NEG_INFTY = float("-inf")
NO_BOUNDS = Interval(NEG_INFTY, INFTY)


def _break_eqs(C: list) -> list:
    for c in C:
        if c.rel_op == "==":
            yield Le(c.lhs, c.rhs)
            yield Le(c.rhs, c.lhs)
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
        assert c.rel_op in ("<=", ">="), c
        c = to_le(c)

        lhs, rhs = c.lhs, c.rhs
        if (rhs, lhs) in seen:
            eqs.add((rhs, lhs))
        else:
            seen.add((lhs, rhs))

    seen = seen.difference(eqs)

    return [(Eq(rhs, lhs)) for rhs, lhs in eqs] + [Le(lhs, rhs) for lhs, rhs in seen]


def to_le(term):
    """
    Convert the inequality to be less-or-equal
    """
    assert term.rel_op in ("<=", ">=", "<", ">"), term
    if term.rel_op == ">=":
        term = Le(term.rhs, term.lhs)
    elif term.rel_op == ">":
        term = Lt(term.rhs, term.lhs)

    assert term.rel_op in ("<=", "<")
    return term


def _get_bounds(term) -> Interval:
    op, lhs, rhs = term.rel_op, term.lhs, term.rhs
    lhs_is_sym = _is_sym(lhs)
    rhs_is_sym = _is_sym(rhs)
    lhs_is_num = _is_constant(lhs)
    rhs_is_num = _is_constant(rhs)

    if op == "==":
        if lhs_is_sym and rhs_is_num:
            return _to_var(lhs), Interval(rhs, rhs)
        elif rhs_is_sym and lhs_is_num:
            return _to_var(rhs), Interval(lhs, lhs)
    elif op in ("<=", "<"):
        if lhs_is_sym and rhs_is_num:
            return _to_var(lhs), Interval(NEG_INFTY, rhs, lopen=False, ropen=(op == "<"))
        elif rhs_is_sym and lhs_is_num:
            return _to_var(rhs), Interval(lhs, INFTY, lopen=(op == "<"), ropen=False)
    elif op in (">=", ">"):
        if lhs_is_sym and rhs_is_num:
            return _to_var(lhs), Interval(rhs, INFTY, lopen=(op == ">"), ropen=False)
        elif rhs_is_sym and lhs_is_num:
            return _to_var(rhs), Interval(NEG_INFTY, lhs, lopen=False, ropen=(op == ">"))

    return None, None


_is_sym = expr_is_symbol
_to_var = expr_to_var


def _cmp_numbers(lhs, rhs) -> int | None:
    """Compare two numeric values.

    Returns 1 if lhs > rhs, -1 if lhs < rhs, 0 if lhs == rhs, and None if
    comparison cannot be established cheaply.
    """
    # Convert Expressions to comparable values
    lhs = _to_comparable(lhs)
    rhs = _to_comparable(rhs)
    if lhs is None or rhs is None:
        return None

    if lhs == rhs:
        return 0
    try:
        if lhs > rhs:
            return 1
        if lhs < rhs:
            return -1
    except TypeError:
        return None
    return None


_to_comparable = expr_to_comparable


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

    diff = term.lhs - term.rhs
    expr = expr_collect(diff, var)
    coeff = expr_coefficient(expr, var)
    if _is_constant(coeff) and _to_comparable(coeff) == 0:
        return None

    var_sym = _to_sym(var)
    rest = expr - coeff * var_sym
    if not _is_constant(rest):
        return None
    # Check rest has no free symbols
    rest_syms = expr_free_symbols(rest)
    if rest_syms:
        return None

    sign = _cmp_numbers(coeff, 0)
    if sign is None or sign == 0:
        return None

    bound = -rest / coeff
    if not _is_constant(bound):
        return None

    if op == "==":
        return ("eq", bound, False)

    strict = op in ("<", ">")
    if op in ("<", "<="):
        return ("upper", bound, strict) if sign > 0 else ("lower", bound, strict)
    return ("lower", bound, strict) if sign > 0 else ("upper", bound, strict)


def _tri_bool(term) -> bool | None:
    """Return concrete bool for Python booleans, else None."""

    if term is True or term is False:
        return term
    if isinstance(term, bool):
        return term
    return None


def constraints_time_set_fast(constraints, timevar: Var):
    """Fast path for extracting a 1D time set from simple constraints.

    Returns Interval/FiniteSet for constraints over `timevar` only.
    Returns None when constraints are multi-variate or not in the supported
    simple linear form; callers should then fall back to the generic path.
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
    """
    bounds = {}
    for term in C:
        sym, B = _get_bounds(term)
        if sym is None:
            continue

        bounds[sym] = bounds.get(sym, NO_BOUNDS).intersect(B)

    return bounds


def remove_redundant_constraints(C) -> list:
    raise RuntimeError("This might be buggy")


def simplify_constraints(C: list):
    """Simplify constraints via PPL round-trip."""
    C = list(C)
    if not C:
        return []

    # Gather all variables
    all_vars = set()
    for c in C:
        if hasattr(c, 'free_symbols'):
            all_vars.update(c.free_symbols)

    if not all_vars:
        return C

    # Build PPL polyhedron and extract minimized constraints
    try:
        vars_list = list(all_vars)
        variables = [(v, ppl.Variable(n)) for n, v in enumerate(vars_list)]
        cs = ppl.Constraint_System()
        for c in C:
            cs.insert(sympy_to_ppl_constraint(c, variables))
        poly = ppl.NNC_Polyhedron(cs)
        if poly.is_empty():
            return []
        return [ppl_constraint_to_sympy(c, variables) for c in poly.minimized_constraints()]
    except Exception:
        return C


def coef_with_denom(c: Fraction, denom):
    return int(c.numerator * (denom / c.denominator))


def _expr_coefficients_dict(expr, variables):
    """Extract coefficients from an expression for the given variables.

    Returns a dict mapping each variable (as a Var) to its Fraction coefficient,
    plus a special key 1 for the constant term.
    """
    expr_sym = _to_sym(expr)
    result = {}

    for var, _ in variables:
        c = expr_coefficient(expr_sym, var)
        if _is_constant(c):
            cv = _to_comparable(c)
            if cv != 0:
                result[var] = frac(cv)

    # Constant term: substitute all variables with 0
    const_expr = expr_sym
    for var, _ in variables:
        const_expr = expr_replace(const_expr, var, 0)

    if _is_constant(const_expr):
        cv = _to_comparable(const_expr)
        if cv != 0:
            result[1] = frac(cv)

    return result


def sympy_to_ppl_expr(expr, variables):
    """
    Convert a Symbolica expression to a PPL Linear_Expression.

    `variables` is a list of (Var, PPL var) tuples.
    """
    coeff_dict = _expr_coefficients_dict(expr, variables)
    constant = coeff_dict.get(1, Fraction(0))

    all_fracs = list(coeff_dict.values()) + [constant]
    denom = lcm(*(v.denominator for v in all_fracs if isinstance(v, Fraction)), 1)

    # Create PPL expression
    coeffs = {
        pplv.id(): coef_with_denom(coeff_dict.get(v, Fraction(0)), denom)
        for v, pplv in variables
    }
    constant_int = coef_with_denom(constant, denom)
    return ppl.Linear_Expression(coeffs, constant_int)


def sympy_to_ppl_constraint(rel, variables):
    """
    Convert a Relation to a ppl.Constraint.

    `variables` is a list of (Var, PPL var) tuples.
    """
    # move all terms to LHS
    diff = rel.lhs - rel.rhs
    expr = sympy_to_ppl_expr(diff, variables)

    op = rel.rel_op
    if op == "<=":
        return ppl.Constraint(expr <= 0)
    elif op == ">=":
        return ppl.Constraint(expr >= 0)
    elif op == "<":
        return ppl.Constraint(expr < 0)
    elif op == ">":
        return ppl.Constraint(expr > 0)
    elif op == "==":
        return ppl.Constraint(expr == 0)

    raise ValueError(f"Unsupported relation type: {rel}")


def ppl_constraint_to_sympy(ppl_c, variables):
    monomials = [
        c * v for (c, (v, _)) in zip(ppl_c.coefficients(), variables) if c != 0
    ]
    lhs = sum(monomials) + ppl_c.inhomogeneous_term()
    if ppl_c.is_strict_inequality():
        return Gt(lhs, 0)
    if ppl_c.is_equality():
        return Eq(lhs, 0)

    assert ppl_c.is_nonstrict_inequality(), ppl_c
    return Ge(lhs, 0)


def complement_term(term, timevar, time_bounds):
    """
    Yield lists of constraints whose union describe the complement of the given term
    """

    if timevar and time_bounds:
        if isinstance(time_bounds, FiniteSet):
            timebounds = [Eq(timevar, next(iter(time_bounds)))]
        else:
            timebounds = [Le(time_bounds.start, timevar), Le(timevar, time_bounds.end)]
    else:
        timebounds = []

    if term.rel_op == "==":
        # in this case we yield two sets of constraints
        for C in [Lt(term.lhs, term.rhs)], [Lt(term.rhs, term.lhs)]:
            yield [C] + timebounds if not isinstance(C, list) else C + timebounds
        return

    # only one set of constraints
    yield [term.negated] + timebounds


def solve_for_variable(to_reduce, var) -> list:
    """
    Solve linear inequalities for a single variable.
    Custom implementation replacing sympy.reduce_inequalities.
    """
    if not to_reduce:
        return []

    var_sym = _to_sym(var)
    results = []

    for term in to_reduce:
        op = term.rel_op
        diff = term.lhs - term.rhs
        expr = expr_collect(diff, var)
        coeff = expr_coefficient(expr, var)

        coeff_val = _to_comparable(coeff)
        if coeff_val is None or coeff_val == 0:
            # Constraint doesn't involve var; check if it's trivially true/false
            if _is_constant(expr):
                val = _to_comparable(expr)
                if val is not None:
                    if op == "<=":
                        if val <= 0:
                            continue  # trivially true
                        else:
                            return False  # unsatisfiable
                    elif op == "<":
                        if val < 0:
                            continue
                        else:
                            return False
                    elif op == ">=":
                        if val >= 0:
                            continue
                        else:
                            return False
                    elif op == ">":
                        if val > 0:
                            continue
                        else:
                            return False
                    elif op == "==":
                        if val == 0:
                            continue
                        else:
                            return False
            # Non-trivial constraint without var: preserve it
            results.append(term)
            continue

        rest = expr - coeff * var_sym
        bound = -rest / coeff

        # Determine the resulting relation direction
        # If coeff > 0: direction preserved
        # If coeff < 0: direction flipped
        if op == "==":
            results.append(Eq(var, bound))
        elif op in ("<", "<="):
            if coeff_val > 0:
                results.append(_make_rel(var_sym, op, bound))
            else:
                flipped = ">=" if op == "<" else ">"  # flip and strict stays same dir
                # Actually: < with negative coeff flips to >
                flipped = ">" if op == "<" else ">="
                results.append(_make_rel(var_sym, flipped, bound))
        elif op in (">", ">="):
            if coeff_val > 0:
                results.append(_make_rel(var_sym, op, bound))
            else:
                flipped = "<" if op == ">" else "<="
                results.append(_make_rel(var_sym, flipped, bound))

    if not results:
        return True

    # Filter out trivially true results
    filtered = []
    for r in results:
        if r is True:
            continue
        if r is False:
            return False
        filtered.append(r)

    if not filtered:
        return True

    return filtered


class Polyhedron:
    """
    N-dimensional Polyhedron (bounded polytope).

    `constraints` is a list of Relation objects.
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
        self._time_bounds = NO_BOUNDS  # time_bounds
        self._vars = set()

        self._constraints = set()
        if not self._add_constraints(constraints):
            # the constraints are unsat, clear them and bail out
            # without setting `_vars`, which will result in the empty polyhedron
            self._constraints = set()
            return

        self._vars = variables or set(
            v for c in self._constraints for v in c.atoms(Var)
        )
        assert all(isinstance(v, Var) for v in self._vars), self._vars
        assert not self._constraints or self._vars, (
            f"Have constraints but no vars: {self}"
        )

        if constraints and not self._constraints and not self._vars:
            # we had constraints but they reduced to True which was dropped..
            raise RuntimeError(
                "Universal poly that became empty because we do not know variables"
            )

    def _add_constraints(self, constraints):
        bounds = {}
        for c in constraints:
            if c is True or c == True:
                continue
            elif c is False or c == False:
                return False
            self._constraints.add(c)

        for sym, I in bounds.items():
            if isinstance(I, FiniteSet):
                self._constraints.add(Eq(sym, next(iter(I))))
                continue

            if not I.is_left_unbounded:
                self._constraints.add(Lt(I.start, sym) if I.left_open else Le(I.start, sym))
            if not I.is_right_unbounded:
                self._constraints.add(Lt(sym, I.end) if I.right_open else Le(sym, I.end))

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
            return Polyhedron(self.constraints(), variables=self.vars())

        C = simplify_constraints(self._constraints)
        if not C:
            return Polyhedron([])
        return Polyhedron(C, variables=self.vars(), time_bounds=self._time_bounds)

    def intersection(self, rhs: "Polyhedron", ignore_variables=True) -> "Polyhedron":
        if not ignore_variables and self.vars() != rhs.vars():
            return Polyhedron([])

        if rhs.is_empty() or self.is_empty():
            return Polyhedron([])

        C = self._constraints.copy()
        C.update(rhs._constraints)

        return Polyhedron(
            C,
            variables=(
                self.vars().union(rhs.vars()) if ignore_variables else self.vars()
            ),
            time_bounds=self._time_bounds.intersect(rhs._time_bounds),
        )

    def complement(self, timevar=None) -> list:
        return [
            Polyhedron(cc, variables=self.vars(), time_bounds=self._time_bounds)
            for c in self._constraints
            for cc in complement_term(c, timevar, self._time_bounds)
        ]

    def eliminate_ppl(self, elim_vars: list[Var]):
        raise NotImplementedError()

    def eliminate(self, var: Var, do_simplify=False, restore_eqs=False) -> "Polyhedron":
        """
        Eliminate the variable `var` from this polyhedron.
        We use Fourier-Motzkin elimination for now.
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
        if solved_for_var is False:
            return Polyhedron([], set())
        if solved_for_var is True:
            return Polyhedron([], self.vars())

        for term in break_eqs(solved_for_var):
            # these do not contribute to the result
            if _is_inf(term):
                continue
            term = to_le(term)

            if expr_has(term.lhs, var):
                assert not expr_has(term.rhs, var), term
                assert _is_just_var(term.lhs, var), "Term is not just the symbol"
                rights.append(term)
            elif expr_has(term.rhs, var):
                assert _is_just_var(term.rhs, var), "Term is not just the symbol"
                lefts.append(term)

        reduced = []
        if lefts and rights:
            for t_lhs, t_rhs in product(lefts, rights):
                assert _is_just_var(t_lhs.rhs, var) and _is_just_var(t_rhs.lhs, var), (var, t_lhs, t_rhs)

                if t_lhs.rel_op == "<" or t_rhs.rel_op == "<":
                    term = Lt(t_lhs.lhs, t_rhs.rhs)
                else:
                    assert t_lhs.rel_op == t_rhs.rel_op == "<=", (t_lhs, t_rhs)
                    term = Le(t_lhs.lhs, t_rhs.rhs)
                if term is True or term == True:
                    continue
                if term is False or term == False:
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
        if self.is_empty():
            return None, []

        variables = [(v, ppl.Variable(n)) for n, v in enumerate(self.vars())]
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
        return self._vars == rhs._vars and self._constraints == rhs._constraints

    def __hash__(self) -> bool:
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
            self.__str = (
                f"{{{', '.join(map(str, self._constraints))}}} over {self._vars}"
            )

    def __str__(self):
        self.__create_str()
        return self.__str


def _is_inf(term):
    """Check if a Relation involves infinity."""
    return expr_is_inf(term.lhs) or expr_is_inf(term.rhs)


def _is_just_var(expr, var):
    """Check if expr is exactly the given var."""
    if isinstance(expr, Var):
        return expr == var
    var_sym = _to_sym(var)
    try:
        return bool(_to_sym(expr) == var_sym)
    except TypeError:
        return False


if __name__ == "__main__":
    x, y, z = Var("x"), Var("y"), Var("z")

    P1 = Polyhedron(
        [Le(x - y, 1), Le(2 * x, 1), Ge(2 * x, 1), Le(-x, 3), Ge(x + z, 3), Le(z + y, x)]
    )
    print("P1:", P1)
    P = P1.eliminate(x)
    print("elim x", P)
    print("elim z")
    print(P.eliminate(z))
    print("elim y")
    print(P.eliminate(y))
