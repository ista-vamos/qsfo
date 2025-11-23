from qsfo.polyhedron import Var, Polyhedron


class PolyhedraList:
    """
    A set of polyhedra describing a part of an n-dimensional space.

    The interpretation is the _union_ of all polyhedra.
    """

    def __init__(self, *args):
        self._phs: set[Polyhedron] = set()
        if len(args) == 1 and isinstance(args[0], (list, set)):
            self._add(args[0])
        else:
            self._add(args)

    def _add(self, phs) -> None:
        _phs = self._phs
        for ph in phs:
            assert isinstance(ph, Polyhedron), ph
            if ph.is_empty():
                continue
            _phs.add(ph)

    def add(self, ph: Polyhedron):
        if not ph.is_empty():
            self._phs.add(ph)

    def union(self, other: "PolyhedraList") -> "PolyhedraList":
        C = self._phs.copy()
        C.update(other._phs)
        return PolyhedraList(C)

    def reduce(self) -> "PolyhedraList":
        return PolyhedraList(
            *(ph for ph in (p.reduce() for p in self) if not ph.is_empty())
        )

    def intersection(self, other, ignore_variables=True) -> "PolyhedraList":
        """
        Intersect this polyhedra list with another polyhedra list or with a polyhedron.

        :param ignore_variables:  if set to `True`, the operation assumes that any variable missing
                                  in `self` or `other` is present and unconstraint. If set to `False`,
                                  the intersection is strict: a missing variable means that there
                                  is no intersection along that dimension and the whole intersection
                                  is empty.
        """
        if isinstance(other, Polyhedron):
            other = PolyhedraList(other)

        # print("FIXME: use ordering on sets")
        new_phs = set()
        for lhs in self._phs:
            for rhs in other._phs:
                ph = lhs.intersection(rhs, ignore_variables)
                if ph:
                    new_phs.add(ph)

        return PolyhedraList(new_phs).reduce()

    def complement(self, timevar: Var = None) -> "PolyhedraList":
        print("TODO: make complement more efficient (use ordering)")
        C = [ph.complement(timevar) for ph in self._phs]
        assert len(C) > 0

        res = PolyhedraList(C[0])
        for i in range(1, len(C)):
            res = res.intersection(PolyhedraList(C[i]))

        return res

    def eliminate(self, var: Var) -> "PolyhedraList":
        C: list[Polyhedron] = []
        for x in self._phs:
            x = x.eliminate(var)
            # if x.is_universal():
            #   continue
            C.append(x)
        return PolyhedraList(C)

    def simplify(self):
        return PolyhedraList(*(p.simplify() for p in self._phs))

    def vars(self) -> set[Var]:
        return set(v for ph in self._phs for v in ph.vars())

    def is_empty(self) -> bool:
        return not self._phs

    def __len__(self) -> int:
        return len(self._phs)

    def __iter__(self):
        return iter(self._phs)

    def __str__(self) -> str:
        return f'{{{", ".join(map(str, self._phs))}}}'


class SortedPolyhedraList(PolyhedraList):
    pass


class FormulaPolyhedraList(PolyhedraList):
    """
    A pair of a PolyhedronSet and a variable which represents the value of the formula.
    """

    def __init__(self, var: Var, *args) -> None:
        super().__init__(*args)
        self._var: Var = var

    def var(self) -> Var:
        return self._var

    def __str__(self) -> str:
        return f"{self._var} ==> {super().__str__()}"
