from os.path import dirname, join as pathjoin
from sys import path as syspath

syspath.append(pathjoin(dirname(__file__), ".."))

from qsfo.polyhedron import *

if __name__ == "__main__":

    x = Var("x")
    c = x < 0
    assert c == (x < 0)
    assert Polyhedron([x < 0, x < 0, x < 0]) == Polyhedron([x < 0])

    y = Var("y")
    assert Polyhedron([x < 0, x < 0, y >= 1, x < 0]) == Polyhedron([y >= 1, x < 0])
