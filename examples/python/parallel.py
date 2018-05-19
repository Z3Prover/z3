from z3 import *
from multiprocessing.pool import ThreadPool
from copy import deepcopy

pool = ThreadPool(8)
x = Int('x')

assert x.ctx == main_ctx()


def calculate(x, n, ctx):
    """ Do a simple computation with a context"""
    assert x.ctx == ctx
    assert x.ctx != main_ctx()

    # Parallel creation of z3 object
    condition = And(x < 2, x > n, ctx)

    # Parallel solving
    solver = Solver(ctx=ctx)
    solver.add(condition)
    solver.check()


for i in range(100):
    # Create new context for the computation
    # Note that we need to do this sequentially, as parallel access to the current context or its objects
    # will result in a segfault
    i_context = Context()
    x_i = deepcopy(x).translate(i_context)

    # Kick off parallel computation
    pool.apply_async(calculate, [x_i, i, i_context])

pool.close()
pool.join()
