from lark import Lark, logger, Transformer
from .. formula import *

class AstTransformer(Transformer):
    def timeterm(self, items):
        raise NotImplementedError("This one should be always inlined.")

    def timevar(self, items):
        return TimeVar(items[0])

    def timeadd(self, items):
        assert len(items) == 2, items
        return TimeOp('+', items[0], items[1])

    def timeconst(self, items):
        assert len(items) == 1
        assert isinstance(items[0], (int, float)), items[0]
        return TimeConstant(items[0])

    def valuevar(self, items):
        return ValueVar(items[0])

    def valueconst(self, items):
        assert len(items) == 1
        assert isinstance(items[0], (int, float)), items[0]
        return ValueConstant(items[0])

    def signal(self, items):
        assert len(items) == 2
        assert isinstance(items[0], str), items
        assert isinstance(items[1], TimeTerm), items
        return Signal(items[0], items[1])

    def valsub(self, items):
        assert len(items) == 2
        assert isinstance(items[0], ValueTerm), items
        assert isinstance(items[1], ValueTerm), items
        return ValueOp("-", items[0], items[1])

    def valadd(self, items):
        assert len(items) == 2
        assert isinstance(items[0], ValueTerm), items
        assert isinstance(items[1], ValueTerm), items
        return ValueOp("+", items[0], items[1])

    def valabs(self, items):
        assert len(items) == 1
        assert isinstance(items[0], ValueTerm), items
        return ValueOp("abs", items[0])

    def is_le(self, items):
        assert len(items) == 2
        assert isinstance(items[0], (ValueTerm, TimeTerm)), items
        assert isinstance(items[1], (ValueTerm, TimeTerm)), items
        return LessOrEqual(items[0], items[1])

    def is_lt(self, items):
        assert len(items) == 2
        assert isinstance(items[0], (ValueTerm, TimeTerm)), items
        assert isinstance(items[1], (ValueTerm, TimeTerm)), items
        return LessThan(items[0], items[1])

    def bound(self, items):
        return (int(items[0]), int(items[1]))

    def quantifier(self, items):
        assert 1 <= len(items) <= 2, items
        assert isinstance(items[0], str), items
        assert len(items) == 1 or isinstance(items[1], tuple), items
        return (items[0], items[1] if len(items) > 1 else None)

    def exists(self, items):
        assert len(items) == 2
        assert isinstance(items[0], tuple), items
        assert isinstance(items[1], Formula), items
        print(items[1].variables())
        assert False
        return Exists(Quantifier(*items[0]), items[1])

    def neg(self, items):
        return Not(items[0])

    def lor(self, items):
        assert len(items) == 2
        assert isinstance(items[0], Formula), items
        assert isinstance(items[1], Formula), items
        return Or(items[0], items[1])

    def forall(self, items):
        assert len(items) == 2
        assert isinstance(items[0], tuple), items
        assert isinstance(items[1], Formula), items
        var, bounds = items[0]
        # gather all variables in the sub-formula with the quantified name
        vars = [v for v in items[1].free_variables() if var == v.name()]
        if not vars:
            raise RuntimeError(f'Binding non-existing variable: {items[1]}, free variables: {items[1].free_variables()}')
        if any(var == v for v in items[1].bound_variables()):
            raise NotImplementedError(f'A variable shadows another variable, this is not supported atm: {items[1]}, bound variables: {items[1].bound_variables()}')

        var = vars[0]
        if any(type(v) != type(var) for v in vars):
            raise RuntimeError(f'A variable is used both as a value and time variable: {items[1]}, {var}')


        return Not(Exists(Quantifier(var, bounds), Not(items[1])))

    def number(self, items):
        assert len(items) == 1
        if items[0].type == "INT":
            return int(items[0])
        elif items[0].type == "REAL":
            # FIXME: Python floats are not arbitrary precision!
            return float(items[0])
        raise NotImplementedError(f"Unknown type of number: {items[0]}")

   #def start(self, items):
   #    assert len(items) == 1, items
   #    assert isinstance(items[0], Formula), items[0]
   #    return items[0]


def process_ast(ast):
    T = AstTransformer()
    return T.transform(ast)

class Parser:
    def __init__(self):
        self._parser = Lark.open("grammar.lark",
                                 rel_to=__file__,
                                 debug=False,
                                 start="start")

    def parse(self, what: str):
        return process_ast(self._parser.parse(what))