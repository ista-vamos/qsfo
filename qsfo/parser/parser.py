from lark import Lark, Transformer
from ..formula import (
    Quantifier,
    Exists,
    Or,
    And,
    Signal,
    Formula,
    TimeVar,
    TimeOp,
    Constant,
    ValueVar,
    TimeTerm,
    ValueTerm,
    ValueOp,
    Not,
    LessOrEqual,
    LessThan,
)


class AstTransformer(Transformer):
    def timeterm(self, items):
        raise NotImplementedError("This one should be always inlined.")

    def timevar(self, items):
        return TimeVar(items[0])

    def timeadd(self, items):
        assert len(items) == 2, items
        assert isinstance(items[0], (TimeTerm, Constant)), items
        assert isinstance(items[1], (TimeTerm, Constant)), items
        return TimeOp("+", items[0], items[1])

    def timesub(self, items):
        assert len(items) == 2
        assert isinstance(items[0], (TimeTerm, Constant)), items
        assert isinstance(items[1], (TimeTerm, Constant)), items
        return TimeOp("-", items[0], items[1])

    def timemul(self, items):
        assert len(items) == 2, items
        assert isinstance(items[0], (TimeTerm, Constant)), items
        assert isinstance(items[1], (TimeTerm, Constant)), items
        return TimeOp("*", items[0], items[1])

    def timeconst(self, items):
        assert len(items) == 1
        assert isinstance(items[0], (int, float)), items[0]
        return Constant(items[0])

    def valuevar(self, items):
        return ValueVar(items[0])

    def valueconst(self, items):
        assert len(items) == 1
        assert isinstance(items[0], (int, float)), items[0]
        return Constant(items[0])

    def signal(self, items):
        assert len(items) == 2
        assert isinstance(items[0], str), items
        assert isinstance(items[1], TimeTerm), items
        return Signal(items[0], items[1])

    def valsub(self, items):
        assert len(items) == 2
        assert isinstance(items[0], (ValueTerm, Constant)), items
        assert isinstance(items[1], (ValueTerm, Constant)), items
        return ValueOp("-", items[0], items[1])

    def valadd(self, items):
        assert len(items) == 2
        assert isinstance(items[0], (ValueTerm, Constant)), items
        assert isinstance(items[1], (ValueTerm, Constant)), items
        return ValueOp("+", items[0], items[1])

    def valmul(self, items):
        assert len(items) == 2
        assert isinstance(items[0], (ValueTerm, Constant)), items
        assert isinstance(items[1], (ValueTerm, Constant)), items
        return ValueOp("*", items[0], items[1])

    def valabs(self, items):
        assert len(items) == 1
        assert isinstance(items[0], (ValueTerm, Constant)), items
        return ValueOp("abs", items[0])

    def is_le(self, items):
        assert len(items) == 2
        assert isinstance(items[0], (ValueTerm, TimeTerm, Constant)), items
        assert isinstance(items[1], (ValueTerm, TimeTerm, Constant)), items
        return LessOrEqual(items[0], items[1])

    def is_lt(self, items):
        assert len(items) == 2
        assert isinstance(items[0], (ValueTerm, TimeTerm, Constant)), items
        assert isinstance(items[1], (ValueTerm, TimeTerm, Constant)), items
        return LessThan(items[0], items[1])

    def is_gt(self, items):
        assert len(items) == 2
        assert isinstance(items[0], (ValueTerm, TimeTerm, Constant)), items
        assert isinstance(items[1], (ValueTerm, TimeTerm, Constant)), items
        return Not(LessOrEqual(items[0], items[1]))

    def is_ge(self, items):
        assert len(items) == 2
        assert isinstance(items[0], (ValueTerm, TimeTerm, Constant)), items
        assert isinstance(items[1], (ValueTerm, TimeTerm, Constant)), items
        return Not(LessThan(items[0], items[1]))

    def bound(self, items):
        return (int(items[0]), int(items[1]))

    def quantifier(self, items):
        assert 1 <= len(items) <= 2, items
        assert isinstance(items[0], str), items
        assert len(items) == 1 or isinstance(items[1], tuple), items
        return (items[0], items[1] if len(items) > 1 else None)

    def neg(self, items):
        return Not(items[0])

    def lor(self, items):
        assert len(items) == 2
        assert isinstance(items[0], Formula), items
        assert isinstance(items[1], Formula), items
        return Or(items[0], items[1])

    def land(self, items):
        assert len(items) == 2
        assert isinstance(items[0], Formula), items
        assert isinstance(items[1], Formula), items
        return And(items[0], items[1])

    def _exists(self, items):
        assert len(items) == 2
        assert isinstance(items[0], tuple), items
        assert isinstance(items[1], Formula), items
        var, bounds = items[0]
        # gather all variables in the sub-formula with the quantified name
        vars = [v for v in items[1].free_variables() if var == v.name()]
        if not vars:
            raise RuntimeError(
                f"Binding non-existing variable `{var}` in formula `{items[1]}` with free variables: {','.join(map(str, items[1].free_variables()))}"
            )
        if any(var == v for v in items[1].bound_variables()):
            raise NotImplementedError(
                f"A variable shadows another variable, this is not supported atm: {items[1]}, bound variables: {items[1].bound_variables()}"
            )

        var = vars[0]
        if any(type(v) != type(var) for v in vars):
            raise RuntimeError(
                f"A variable is used both as a value and time variable: {items[1]}, {var}"
            )
        return Quantifier(var, bounds), items[1]

    def exists(self, items):
        q, formula = self._exists(items)
        return Exists(q, formula)

    def forall(self, items):
        q, formula = self._exists(items)
        return Not(Exists(q, Not(formula)))

    def number(self, items):
        assert len(items) == 1
        if items[0].type == "INT":
            return int(items[0])
        elif items[0].type == "REAL":
            # FIXME: Python floats are not arbitrary precision!
            return float(items[0])
        raise NotImplementedError(f"Unknown type of number: {items[0]}")

    def start(self, items):
        assert len(items) == 1, items
        assert isinstance(items[0], Formula), items[0]
        return items[0]


def process_ast(ast):
    T = AstTransformer()
    return T.transform(ast)


class Parser:
    def __init__(self):
        self._parser = Lark.open(
            "grammar.lark", rel_to=__file__, debug=False, start="start"
        )

    def parse(self, what: str):
        return process_ast(self._parser.parse(what))
