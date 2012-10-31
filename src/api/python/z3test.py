import z3, doctest

r = doctest.testmod(z3)
if r.failed != 0:
    exit(1)

