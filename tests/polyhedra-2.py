from os.path import dirname, join as pathjoin
from sys import path as syspath

syspath.append(pathjoin(dirname(__file__), ".."))

from qsfo.polyhedron import *

if __name__ == "__main__":

    x = Var("x")
    y = Var("y")
    px = Polyhedron([x < 0])
    py = Polyhedron([y > 0])
    assert px.intersection(py, ignore_variables=False).is_empty()
    assert px.intersection(py) == Polyhedron([x < 0, y > 0])

    i = px.intersection(py)
    print(i)
    for x in i.complement():
        print(x)
