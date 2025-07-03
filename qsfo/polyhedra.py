class Polyhedron:
    """
    Convex Polyhedron.
    `_time` bounds is a pair (l, u) with lower and upper bound on time (None for infinity)
    """

    def __init__(self, t, *args):
        # time bounds
        self._time_bounds = t
        self._constraints = list(args)

    def __lt__(self, other):
        """
        Order polyhedra according to `sup(time_bounds)`
        """
        return self._time_bounds[1] < other._time_bounds[1]


class PolyhedraSet:
    pass
