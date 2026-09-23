#!/usr/bin/env python3
"""Incremental API microbenchmark; not a public-artifact throughput claim.

Run each setting in a fresh process with the matching Z3 Python bindings.
Times include only check(), excluding construction and model validation.
"""
import argparse
import json
import time
from z3 import *


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--cache', type=int, choices=[0, 1], required=True)
    ap.add_argument('--prime', type=int, required=True)
    ap.add_argument('--checks', type=int, default=40)
    args = ap.parse_args()
    field = FiniteFieldSort(args.prime)
    x, y = Consts('cache_x cache_y', field)
    observer = Function('cache_observer', field, IntSort())
    constraints = [x*x+y*y == 5, x*y == 2]
    solver = SimpleSolver()
    solver.set(**{'ff.basis_cache': bool(args.cache), 'timeout': 10000})
    solver.add(constraints)
    times = []
    for i in range(args.checks):
        solver.push()
        extra = observer(x) == i
        solver.add(extra)
        start = time.perf_counter()
        result = solver.check()
        times.append(time.perf_counter()-start)
        assert result == sat, (result, solver.reason_unknown())
        model = solver.model()
        assert all(is_true(model.eval(q, model_completion=True)) for q in constraints+[extra])
        solver.pop()
    stats = solver.statistics()
    print(json.dumps(dict(cache=bool(args.cache), prime=args.prime, checks=args.checks,
                          first_seconds=times[0], repeated_seconds=sum(times[1:]),
                          times=times, stats={k: stats.get_key_value(k) for k in stats.keys()})))


if __name__ == '__main__':
    main()
