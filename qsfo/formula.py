from sympy import Rational, Abs
from qsfo.polyhedron import Var

# from ppl import Variable as PPLVariable


class Formula:
    def __init__(self, children):
        assert self not in children, "Have self in children"
        self._children = children

    def time_variables(self) -> list:
        return [v for c in self.children() for v in c.time_variables()]

    def value_variables(self) -> list:
        return [v for c in self.children() for v in c.value_variables()]

    def variables(self):
        return self.time_variables() + self.value_variables()

    def free_variables(self):
        return [v for c in self.children() for v in c.free_variables()]

    def bound_variables(self):
        return [v for v in self.variables() if v not in self.free_variables()]

    def signals(self):
        if isinstance(self, Signal):
            return [self]
        else:
            return [s for c in self.children() for s in c.signals()]

    def root_str(self) -> str:
        """__str__ without children (overridden by child classes)"""
        return str(self)

    def children(self):
        return self._children

    def get_constant_bounds(self):
        return [x for c in self._children for x in c.get_constant_bounds()]

    def visit_dfs(self, fn):
        def _visit(node: Formula, lvl):
            for c in node._children:
                _visit(c, lvl + 1)
                fn(c, lvl)

        _visit(self, 0)
        fn(self, 0)

    def visit_bfs(self, fn):
        """
        :param fn: Function to run on all ast nodes. If this function returns false for a node, its children are not visited.
        :return:
        """

        def _visit(node: Formula, lvl):
            for c in node._children:
                if fn(c, lvl):
                    _visit(c, lvl + 1)

        if fn(self, 0):
            _visit(self, 0)

    visit = visit_dfs

    def pretty(self) -> str:
        """
        Return an indented __str__ of the formula
        """
        S = []

        def to_str(ast, lvl):
            if isinstance(ast, Term):
                S.append(f"{' ' * lvl}{ast}")
                return False

            S.append(f"{' ' * lvl}{ast.root_str()}")
            return True

        self.visit_bfs(to_str)

        return "\n".join(S)

    def substitute(self, S: dict):
        """
        Substitute items in `S` recursively in children (i.e., the substitution does not apply to `self`,
        but only to children.
        """
        self._children = [S.get(c, c.substitute(S)) for c in self._children]


class Not(Formula):
    """
    `not: formula(q)`
    """

    def __init__(self, formula: Formula):
        super().__init__([formula])

    def formula(self):
        """The negated formula"""
        return self.children()[0]

    def root_str(self):
        return f"¬"

    def __str__(self):
        return f"¬({self.formula()})"


class And(Formula):
    def __init__(self, lhs: Formula, rhs: Formula):
        super().__init__([lhs, rhs])

    def lhs(self):
        return self.children()[0]

    def rhs(self):
        return self.children()[1]

    def root_str(self):
        return "⋀"

    def __str__(self):
        return f"({self.lhs()} ⋀ {self.rhs()})"


class Or(Formula):
    def __init__(self, lhs: Formula, rhs: Formula):
        super().__init__([lhs, rhs])

    def lhs(self):
        return self.children()[0]

    def rhs(self):
        return self.children()[1]

    def root_str(self):
        return "⋁"

    def __str__(self):
        return f"({self.lhs()} ⋁ {self.rhs()})"


class LessThan(Formula):
    def __init__(self, lhs: Formula, rhs: Formula):
        super().__init__([lhs, rhs])

    def lhs(self):
        return self.children()[0]

    def rhs(self):
        return self.children()[1]

    def root_str(self):
        return "<"

    def __str__(self):
        return f"({self.lhs()} < {self.rhs()})"


class LessOrEqual(Formula):
    def __init__(self, lhs: Formula, rhs: Formula):
        super().__init__([lhs, rhs])

    def lhs(self):
        return self.children()[0]

    def rhs(self):
        return self.children()[1]

    def root_str(self):
        return " ≤"

    def __str__(self):
        return f"{self.lhs()} ≤ {self.rhs()}"


class Term(Formula):
    def expr(self):
        """Return Sympy expr"""
        raise NotImplementedError("Must be overriden")


class Constant(Term):
    def __init__(self, c):
        super().__init__([])
        self._value = c

    def time_variables(self) -> list:
        return []

    def value_variables(self) -> list:
        return []

    def free_variables(self):
        return []

    def value(self):
        return self._value

    def expr(self):
        return Rational(self._value)

    def __str__(self):
        return str(self.value())


class TimeTerm(Term):
    pass


var_cnt: int = 0


class TimeVar(TimeTerm):
    def __init__(self, c):
        super().__init__([])
        self._name = c

    def name(self):
        return self._name

    def time_variables(self) -> list:
        return [self]

    def free_variables(self):
        return [self]

    def expr(self):
        # XXX: we might want to cache these
        return Var(self._name)

    def __hash__(self):
        return hash(self.name())

    def __eq__(self, other):
        return isinstance(other, (TimeVar, ValueVar)) and self.name() == other.name()

    def __str__(self):
        return f"{self.name()}ₜ"


class TimeOp(TimeTerm):
    def __init__(self, op: str, *args):
        super().__init__(list(args))
        self._op = op

    def op(self):
        return self._op

    def root_str(self):
        return str(self.op())

    def expr(self):
        op = self.op()
        ch = self.children()
        if op == "+":
            return ch[0].expr() + ch[1].expr()
        if op == "-":
            return ch[0].expr() - ch[1].expr()
        raise NotImplementedError(f"Unknown operation: {op}")

    def __str__(self):
        op = self.op()
        if op in ("+", "-"):
            ch = self.children()
            return f"{ch[0]}{self.op()}ₜ{ch[1]}"
        return f"{self.op()}({', '.join(map(str, self.children()))})ₜ"


class ValueTerm(Term):
    pass


class ValueVar(ValueTerm):
    def __init__(self, c):
        super().__init__([])
        self._name = c

    def name(self):
        return self._name

    def value_variables(self) -> list:
        return [self]

    def free_variables(self):
        return [self]

    def expr(self):
        # XXX: we might want to cache these
        return Var(self._name)

    def __hash__(self):
        return hash(self.name())

    def __eq__(self, other):
        return isinstance(other, (TimeVar, ValueVar)) and self.name() == other.name()

    def __str__(self):
        return f"{self.name()}ᵥ"


class Signal(ValueTerm):
    def __init__(self, name: str, arg: Term):
        super().__init__([arg])
        self._name = name

    def name(self):
        return self._name

    def arg(self):
        return self.children()[0]

    def root_str(self):
        return str(self._name)

    def __str__(self):
        return f"{self.name()}({self.arg()})ᵥ"


class ValueOp(ValueTerm):
    def __init__(self, op: str, *args):
        super().__init__(list(args))
        self._op = op

    def op(self):
        return self._op

    def root_str(self):
        return str(self.op())

    def expr(self):
        op = self.op()
        ch = self.children()
        if op == "+":
            return ch[0].expr() + ch[1].expr()
        if op == "-":
            return ch[0].expr() - ch[1].expr()
        if op == "abs":
            return Abs(ch[0].expr(), ch[1].expr())
        raise NotImplementedError(f"Unknown operation: {op}")

    def __str__(self):
        op = self.op()
        ch = self.children()
        if op in ("+", "-"):
            assert len(ch) == 2, ch
            return f"{ch[0]}{self.op()}ᵥ{ch[1]}"
        if op == "abs":
            assert len(ch) == 1, ch
            return f"|{ch[0]}|ᵥ"
        assert len(ch) > 0, ch
        return f"{self.op()}({', '.join(map(str, ch))})ᵥ"


class Quantifier(Formula):
    def __init__(self, variable, bound=None):
        super().__init__([])
        assert isinstance(variable, (TimeVar, ValueVar))
        self._var = variable
        self._bounds = bound

    def var(self):
        return self._var

    def bounds(self):
        return self._bounds

    def __eq__(self, other):
        return self.var() == other.var()

    def __str__(self):
        b = self._bounds
        bound = f"∈[{b[0]}, {b[1]}]" if b else ""
        return f"{self.var()}{bound}"


class Exists(Formula):
    """
    `exists q: formula(q)`
    """

    def __init__(self, q: Quantifier, formula: Formula):
        super().__init__([formula])

        self._quantifier = q

    def formula(self):
        """The negated formula"""
        return self.children()[0]

    def quantifier(self):
        return self._quantifier

    def get_constant_bounds(self):
        bounds = super().get_constant_bounds()
        q = self._quantifier
        return bounds + [(q.var(), q.bounds())]

    def free_variables(self):
        qv = self.quantifier().var()
        return [v for v in self.formula().free_variables() if v != qv]

    def root_str(self):
        return f"∃{self.quantifier()}:"

    def __str__(self):
        f = self.formula()
        if isinstance(f, Not):
            return f"∃{self.quantifier()}: {self.formula()}"
        return f"∃{self.quantifier()}: ({self.formula()})"
