"""
Compatibility layer replacing SymPy with Symbolica.

Provides Var, Relation, Interval, FiniteSet, and factory functions
(Eq, Le, Ge, Lt, Gt) that mirror the SymPy relational API used by
the polyhedron engine.
"""

from __future__ import annotations

from fractions import Fraction
from symbolica import Expression, AtomType

# ---------------------------------------------------------------------------
# Helpers: number conversion
# ---------------------------------------------------------------------------

FRACTIONS_PREC = 1000000


def frac(x) -> Fraction:
    return Fraction(float(x)).limit_denominator(FRACTIONS_PREC)


def sym_num(x) -> Expression:
    """Create a Symbolica rational Expression from a Python numeric value."""
    if isinstance(x, Expression):
        return x
    if isinstance(x, Fraction):
        return Expression.num(x.numerator) / Expression.num(x.denominator)
    if isinstance(x, int):
        return Expression.num(x)
    if isinstance(x, float):
        f = Fraction(x).limit_denominator(FRACTIONS_PREC)
        return Expression.num(f.numerator) / Expression.num(f.denominator)
    # fallback
    f = Fraction(float(x)).limit_denominator(FRACTIONS_PREC)
    return Expression.num(f.numerator) / Expression.num(f.denominator)


def _to_sym(x) -> Expression:
    """Coerce *x* to a Symbolica Expression."""
    if isinstance(x, Expression):
        return x
    if isinstance(x, Var):
        return x._expr
    if isinstance(x, (int, float, Fraction)):
        return sym_num(x)
    # Handle gmpy2.mpz and similar integer-like types
    try:
        return Expression.num(int(x))
    except (TypeError, ValueError):
        pass
    raise TypeError(f"Cannot convert {type(x)} to Expression")


def to_python_fraction(expr) -> Fraction:
    """Convert a constant Symbolica Expression (or Python number) to Fraction."""
    if isinstance(expr, Fraction):
        return expr
    if isinstance(expr, int):
        return Fraction(expr)
    if isinstance(expr, float):
        return Fraction(expr).limit_denominator(FRACTIONS_PREC)
    if isinstance(expr, Expression):
        try:
            return Fraction(expr.to_int())
        except Exception:
            return Fraction(float(str(expr.to_float()))).limit_denominator(FRACTIONS_PREC)
    return Fraction(float(expr)).limit_denominator(FRACTIONS_PREC)


# ---------------------------------------------------------------------------
# Expression helpers (free-standing, work on Expression objects)
# ---------------------------------------------------------------------------

def expr_has(expr, var) -> bool:
    """Check whether *expr* contains *var* (a Var or Expression symbol)."""
    if isinstance(expr, (int, float, Fraction)):
        return False
    if not isinstance(expr, Expression):
        return False
    sym = var._expr if isinstance(var, Var) else var
    return sym in expr.get_all_indeterminates()


def expr_subs(expr, substitutions):
    """Apply substitutions to *expr*.

    *substitutions* can be a dict {Var/Expression: replacement} or a list
    of (Var/Expression, replacement) pairs.
    """
    if isinstance(substitutions, dict):
        items = substitutions.items()
    else:
        items = substitutions
    result = expr
    for old, new in items:
        old_e = old._expr if isinstance(old, Var) else _to_sym(old)
        new_e = _to_sym(new)
        result = result.replace(old_e, new_e)
    return result


def _sym_name(sym_expr) -> str:
    """Extract the short name from a Symbolica symbol (strip 'python::' prefix)."""
    name = str(sym_expr.get_name())
    if name.startswith("python::"):
        return name[len("python::"):]
    return name


def expr_free_symbols(expr) -> set:
    """Return the set of Var objects appearing in *expr*."""
    if isinstance(expr, (int, float, Fraction)):
        return set()
    if isinstance(expr, Var):
        return {expr}
    if not isinstance(expr, Expression):
        return set()
    return {Var(_sym_name(s)) for s in expr.get_all_indeterminates()}


def expr_collect(expr, var):
    """Collect terms with respect to *var*, return a new expression."""
    return _to_sym(expr).collect(_to_sym(var))


def expr_coefficient(expr, var):
    """Return the coefficient of *var* in *expr*."""
    return _to_sym(expr).coefficient(_to_sym(var))


def expr_replace(expr, old, new):
    """Substitute *old* with *new* in *expr*."""
    return _to_sym(expr).replace(_to_sym(old), _to_sym(new))


def expr_is_symbol(expr) -> bool:
    """Check if *expr* is a single symbolic variable."""
    if isinstance(expr, Var):
        return True
    if isinstance(expr, Expression):
        return expr.get_type() == AtomType.Var
    return False


def expr_to_var(expr) -> "Var":
    """Convert a single-symbol expression to a Var."""
    if isinstance(expr, Var):
        return expr
    if isinstance(expr, Expression):
        return Var(_sym_name(expr))
    raise TypeError(f"Cannot convert {type(expr)} to Var")


def expr_to_comparable(val):
    """Convert *val* to a Python Fraction/int/float for numeric comparison.

    Returns None if *val* is symbolic (not a constant).
    """
    if isinstance(val, (int, float, Fraction)):
        return val
    if isinstance(val, Var):
        return None
    if isinstance(val, Expression):
        if val.is_constant():
            try:
                return Fraction(val.to_int())
            except Exception:
                return Fraction(float(str(val.to_float()))).limit_denominator(FRACTIONS_PREC)
        return None
    try:
        return float(val)
    except (TypeError, ValueError):
        return None


def expr_is_inf(expr) -> bool:
    """Check whether *expr* is ±infinity."""
    if isinstance(expr, (int, float)):
        return expr == float("inf") or expr == float("-inf")
    if isinstance(expr, Expression) and expr.is_constant():
        v = float(str(expr.to_float()))
        return v == float("inf") or v == float("-inf")
    return False


# ---------------------------------------------------------------------------
# Var
# ---------------------------------------------------------------------------

_var_cache: dict[str, "Var"] = {}


class Var:
    """Symbolic variable wrapping a Symbolica Expression.symbol().

    Arithmetic operators produce Symbolica Expressions.
    Comparison operators produce Relation objects.
    Instances are cached by name for identity stability.
    """

    def __new__(cls, name: str):
        existing = _var_cache.get(name)
        if existing is not None:
            return existing
        obj = object.__new__(cls)
        obj._name = name
        obj._expr = Expression.symbol(name)
        _var_cache[name] = obj
        return obj

    # -- identity / hashing --------------------------------------------------

    @property
    def name(self):
        return self._name

    @property
    def is_symbol(self):
        return True

    @property
    def is_number(self):
        return False

    @property
    def free_symbols(self):
        return {self}

    def has(self, other) -> bool:
        return self is other or (isinstance(other, Var) and self._name == other._name)

    def atoms(self, typ=None):
        if typ is None or isinstance(self, typ):
            return {self}
        return set()

    def __hash__(self):
        return hash(self._name)

    def __eq__(self, other):
        if isinstance(other, Var):
            return self._name == other._name
        if isinstance(other, Expression):
            return bool(self._expr == other)
        return NotImplemented

    def __ne__(self, other):
        r = self.__eq__(other)
        if r is NotImplemented:
            return r
        return not r

    def __str__(self):
        return self._name

    def __repr__(self):
        return f"Var({self._name!r})"

    # -- arithmetic → Expression ---------------------------------------------

    def __add__(self, other):
        return self._expr + _to_sym(other)

    def __radd__(self, other):
        return _to_sym(other) + self._expr

    def __sub__(self, other):
        return self._expr - _to_sym(other)

    def __rsub__(self, other):
        return _to_sym(other) - self._expr

    def __mul__(self, other):
        return self._expr * _to_sym(other)

    def __rmul__(self, other):
        return _to_sym(other) * self._expr

    def __truediv__(self, other):
        return self._expr / _to_sym(other)

    def __rtruediv__(self, other):
        return _to_sym(other) / self._expr

    def __neg__(self):
        return -self._expr

    def __pos__(self):
        return self._expr

    # -- comparison → Relation -----------------------------------------------

    def __le__(self, other):
        return Le(self._expr, _to_sym(other))

    def __lt__(self, other):
        return Lt(self._expr, _to_sym(other))

    def __ge__(self, other):
        return Ge(self._expr, _to_sym(other))

    def __gt__(self, other):
        return Gt(self._expr, _to_sym(other))

    # -- Expression-compatible methods ----------------------------------------

    def collect(self, sym):
        return self._expr.collect(_to_sym(sym))

    def coeff(self, sym):
        return self._expr.coefficient(_to_sym(sym))

    def coefficient(self, sym):
        return self._expr.coefficient(_to_sym(sym))

    def subs(self, substitutions):
        return expr_subs(self._expr, substitutions)

    def replace(self, old, new):
        return self._expr.replace(_to_sym(old), _to_sym(new))

    def is_constant(self):
        return False

    def get_all_indeterminates(self):
        return self._expr.get_all_indeterminates()

    def to_float(self):
        raise TypeError("Var is not a number")


# ---------------------------------------------------------------------------
# Relation
# ---------------------------------------------------------------------------

_NEGATED_OP = {
    "<=": ">",
    "<": ">=",
    ">=": "<",
    ">": "<=",
    "==": "!=",
    "!=": "==",
}


class Relation:
    """A symbolic relational constraint: lhs op rhs.

    Provides the same interface as SymPy Le/Ge/Lt/Gt/Eq objects
    (`.lhs`, `.rhs`, `.rel_op`, `.has()`, `.subs()`, `.free_symbols`,
    `.atoms()`, `.negated`).
    """

    __slots__ = ("_lhs", "_rhs", "_op", "_hash")

    def __init__(self, lhs: Expression, op: str, rhs: Expression):
        self._lhs = lhs
        self._rhs = rhs
        self._op = op
        self._hash = None

    @property
    def lhs(self):
        return self._lhs

    @property
    def rhs(self):
        return self._rhs

    @property
    def rel_op(self):
        return self._op

    @property
    def negated(self):
        return Relation(self._lhs, _NEGATED_OP[self._op], self._rhs)

    @property
    def free_symbols(self) -> set:
        return expr_free_symbols(self._lhs) | expr_free_symbols(self._rhs)

    @property
    def is_number(self):
        return False

    @property
    def is_symbol(self):
        return False

    def has(self, var) -> bool:
        return expr_has(self._lhs, var) or expr_has(self._rhs, var)

    def atoms(self, typ=None):
        result = set()
        for s in self.free_symbols:
            if typ is None or isinstance(s, typ):
                result.add(s)
        return result

    def subs(self, substitutions):
        new_lhs = expr_subs(self._lhs, substitutions)
        new_rhs = expr_subs(self._rhs, substitutions)
        return _make_rel(new_lhs, self._op, new_rhs)

    def collect(self, sym):
        """Collect is not meaningful on a relation, raise for clarity."""
        raise TypeError("collect() not supported on Relation; use on .lhs/.rhs")

    def __eq__(self, other):
        if isinstance(other, Relation):
            return (
                self._op == other._op
                and bool(self._lhs == other._lhs)
                and bool(self._rhs == other._rhs)
            )
        if isinstance(other, bool):
            return False
        return NotImplemented

    def __ne__(self, other):
        r = self.__eq__(other)
        if r is NotImplemented:
            return r
        return not r

    def __hash__(self):
        if self._hash is None:
            self._hash = hash((str(self._lhs), self._op, str(self._rhs)))
        return self._hash

    def __bool__(self):
        # If both sides are constant, evaluate.
        lhs_const = _is_constant(self._lhs)
        rhs_const = _is_constant(self._rhs)
        if lhs_const and rhs_const:
            lv = _const_value(self._lhs)
            rv = _const_value(self._rhs)
            return _eval_op(lv, self._op, rv)
        raise TypeError(
            f"Cannot evaluate symbolic Relation as bool: {self}"
        )

    def __str__(self):
        return f"{self._lhs} {self._op} {self._rhs}"

    def __repr__(self):
        return f"Relation({self._lhs!r}, {self._op!r}, {self._rhs!r})"


# ---------------------------------------------------------------------------
# Internal helpers
# ---------------------------------------------------------------------------

def _is_constant(expr) -> bool:
    if isinstance(expr, (int, float, Fraction)):
        return True
    if isinstance(expr, Var):
        return False
    if isinstance(expr, Expression):
        return expr.is_constant()
    return False


def _const_value(expr) -> Fraction:
    if isinstance(expr, Fraction):
        return expr
    if isinstance(expr, int):
        return Fraction(expr)
    if isinstance(expr, float):
        return Fraction(expr).limit_denominator(FRACTIONS_PREC)
    if isinstance(expr, Expression):
        try:
            return Fraction(expr.to_int())
        except Exception:
            return Fraction(float(str(expr.to_float()))).limit_denominator(FRACTIONS_PREC)
    return Fraction(float(expr)).limit_denominator(FRACTIONS_PREC)


def _eval_op(lv, op, rv) -> bool:
    if op == "<=":
        return lv <= rv
    if op == "<":
        return lv < rv
    if op == ">=":
        return lv >= rv
    if op == ">":
        return lv > rv
    if op == "==":
        return lv == rv
    if op == "!=":
        return lv != rv
    raise ValueError(f"Unknown op: {op}")


def _make_rel(lhs, op, rhs):
    """Create a Relation, constant-folding to bool when both sides are numeric."""
    if _is_constant(lhs) and _is_constant(rhs):
        return _eval_op(_const_value(lhs), op, _const_value(rhs))
    return Relation(lhs, op, rhs)


# ---------------------------------------------------------------------------
# Factory functions (constant-folding)
# ---------------------------------------------------------------------------

def Eq(lhs, rhs=None):
    if rhs is None:
        raise TypeError("Eq() requires two arguments")
    return _make_rel(_to_sym(lhs), "==", _to_sym(rhs))


def Le(lhs, rhs):
    return _make_rel(_to_sym(lhs), "<=", _to_sym(rhs))


def Ge(lhs, rhs):
    return _make_rel(_to_sym(lhs), ">=", _to_sym(rhs))


def Lt(lhs, rhs):
    return _make_rel(_to_sym(lhs), "<", _to_sym(rhs))


def Gt(lhs, rhs):
    return _make_rel(_to_sym(lhs), ">", _to_sym(rhs))


# ---------------------------------------------------------------------------
# Interval (pure Python, no SymPy)
# ---------------------------------------------------------------------------

class Interval:
    """A real interval [start, end] with optional open endpoints."""

    __slots__ = ("_start", "_end", "_left_open", "_right_open")

    def __init__(self, start, end, lopen=False, ropen=False):
        self._start = start
        self._end = end
        self._left_open = lopen
        self._right_open = ropen

    @property
    def start(self):
        return self._start

    @property
    def end(self):
        return self._end

    @property
    def left_open(self):
        return self._left_open

    @property
    def right_open(self):
        return self._right_open

    @property
    def is_left_unbounded(self):
        return self._start == float("-inf")

    @property
    def is_right_unbounded(self):
        return self._end == float("inf")

    def intersect(self, other):
        if isinstance(other, FiniteSet):
            # intersect finite set with interval
            result = frozenset(
                v for v in other._elements
                if self._contains(v)
            )
            if not result:
                return EmptySet()
            return FiniteSet(result)

        # Interval ∩ Interval
        if not isinstance(other, Interval):
            raise TypeError(f"Cannot intersect Interval with {type(other)}")

        # Determine new start
        cmp = _cmp(self._start, other._start)
        if cmp is None:
            raise ValueError("Cannot compare interval bounds")
        if cmp > 0:
            new_start, new_lo = self._start, self._left_open
        elif cmp < 0:
            new_start, new_lo = other._start, other._left_open
        else:
            new_start = self._start
            new_lo = self._left_open or other._left_open

        # Determine new end
        cmp = _cmp(self._end, other._end)
        if cmp is None:
            raise ValueError("Cannot compare interval bounds")
        if cmp < 0:
            new_end, new_ro = self._end, self._right_open
        elif cmp > 0:
            new_end, new_ro = other._end, other._right_open
        else:
            new_end = self._end
            new_ro = self._right_open or other._right_open

        # Check empty
        cmp_se = _cmp(new_start, new_end)
        if cmp_se is not None:
            if cmp_se > 0:
                return EmptySet()
            if cmp_se == 0 and (new_lo or new_ro):
                return EmptySet()

        return Interval(new_start, new_end, new_lo, new_ro)

    def _contains(self, value) -> bool:
        if self._left_open:
            if not (value > self._start):
                return False
        else:
            if not (value >= self._start):
                return False
        if self._right_open:
            if not (value < self._end):
                return False
        else:
            if not (value <= self._end):
                return False
        return True

    def __or__(self, other):
        """Union of intervals – returns a new Interval covering both."""
        if isinstance(other, EmptySet):
            return self
        if isinstance(other, FiniteSet):
            # simple: just extend bounds
            vals = list(other._elements)
            start = min(self._start, *vals)
            end = max(self._end, *vals)
            lo = self._left_open and all(v != start for v in vals)
            ro = self._right_open and all(v != end for v in vals)
            return Interval(start, end, lo, ro)
        if not isinstance(other, Interval):
            raise TypeError(f"Cannot union Interval with {type(other)}")
        start = min(self._start, other._start)
        end = max(self._end, other._end)
        lo = (self._left_open if self._start <= other._start else other._left_open)
        ro = (self._right_open if self._end >= other._end else other._right_open)
        if self._start == other._start:
            lo = self._left_open and other._left_open
        if self._end == other._end:
            ro = self._right_open and other._right_open
        return Interval(start, end, lo, ro)

    def __eq__(self, other):
        if isinstance(other, EmptySet):
            return False
        if isinstance(other, Interval):
            return (
                self._start == other._start
                and self._end == other._end
                and self._left_open == other._left_open
                and self._right_open == other._right_open
            )
        return NotImplemented

    def __hash__(self):
        return hash((self._start, self._end, self._left_open, self._right_open))

    def __str__(self):
        return f"{'(' if self._left_open else '['}{self._start}, {self._end}{')' if self._right_open else ']'}"

    def __repr__(self):
        return f"Interval({self._start}, {self._end}, lopen={self._left_open}, ropen={self._right_open})"


def _cmp(a, b):
    """Compare two values, return -1/0/1 or None."""
    try:
        if a == b:
            return 0
        if a < b:
            return -1
        if a > b:
            return 1
    except TypeError:
        return None
    return None


# ---------------------------------------------------------------------------
# FiniteSet
# ---------------------------------------------------------------------------

class FiniteSet:
    """A finite set of values (wraps frozenset)."""

    __slots__ = ("_elements",)

    def __init__(self, *args):
        if len(args) == 1 and isinstance(args[0], (frozenset, set)):
            self._elements = frozenset(args[0])
        else:
            self._elements = frozenset(args)

    @property
    def start(self):
        return min(self._elements)

    @property
    def end(self):
        return max(self._elements)

    @property
    def left_open(self):
        return False

    @property
    def right_open(self):
        return False

    def __iter__(self):
        return iter(self._elements)

    def __len__(self):
        return len(self._elements)

    def __contains__(self, item):
        return item in self._elements

    def __or__(self, other):
        if isinstance(other, FiniteSet):
            return FiniteSet(self._elements | other._elements)
        if isinstance(other, Interval):
            return other | self
        if isinstance(other, EmptySet):
            return self
        raise TypeError(f"Cannot union FiniteSet with {type(other)}")

    def __eq__(self, other):
        if isinstance(other, FiniteSet):
            return self._elements == other._elements
        return NotImplemented

    def __hash__(self):
        return hash(self._elements)

    def __str__(self):
        return "{" + ", ".join(str(e) for e in sorted(self._elements)) + "}"

    def __repr__(self):
        return f"FiniteSet({self._elements!r})"


class EmptySet:
    """Sentinel for empty intersection results."""

    def __or__(self, other):
        return other

    def __eq__(self, other):
        return isinstance(other, EmptySet)

    def __hash__(self):
        return hash("EmptySet")

    def __str__(self):
        return "∅"

    def __repr__(self):
        return "EmptySet()"
