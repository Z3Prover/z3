#    File name:    bubble_sort.py
#
#    BUBBLESORT  -  Copyright (c) June, 2020 - Matteo Nicoli

from z3 import Solver, Int, Array, IntSort, And, Not, If, Select, Store, sat

def init(i,j) :
    return And(i == 0, j == 0)

def invert(A0, A1, tmp, i0, i1) :
    return If(Select(A0, i0) > Select(A0, i0 + 1),  \
                And(tmp == Select(A0, i0),  \
                    A1 == Store(A0, i0, Select(A0, i0 + 1)),  \
                    A1 == Store(A0, i0 + 1, tmp)), \
                A1 == A0)

def bsort_step(A0, A1, tmp, i0, j0, i1, j1, dim) :
    return If( j0 < dim - 1, \
                And(         \
                    If( i0 < dim - 1, \
                    And(invert(A0, A1, tmp, i0, i1),i1 == i0 + 1), \
                    i1 == i0 + 1), \
                    j1 == j0 + 1), \
                And(j1 == j0 + 1, A1 == A0))

def mk_tran_condition(A, i, j, tmp, dim) :
    condition = []
    for _ in range(dim) :
        condition.append(bsort_step(A[0],A[1],tmp[0],i[0],j[0],i[1],j[1],dim))
        A = A[1:]
        i = i[1:]
        j = j[1:]
        tmp = tmp[1:]
    return condition

def check(variables, Ar, dim) :
    for e in range(dim) :
        yield variables[e] == Select(Ar,e)

def mk_post_condition(values) :
    condition = [v1 <= v2 for v1,v2 in zip(values,values[1:])]
    return And(*condition)


def main() :
    dim = int(input("size of the array: "))

    i = [Int(f"i_{x}") for x in range(dim + 1)]
    j = [Int(f"j_{x}") for x in range(dim + 1)]
    A = [Array(f"A_{x}",IntSort(),IntSort()) for x in range(dim + 1)]
    tmp = [Int(f"tmp_{x}") for x in range(dim)]

    s = Solver()

    init_condition = init(i[0],j[0])
    s.add(init_condition)

    tran_condition = mk_tran_condition(A, i, j, tmp, dim)
    s.add(And(*tran_condition))

    values = [Int(f"n_{x}") for x in range(dim)]
    init_check_condition = check(values,A[-1],dim)
    s.add(And(*init_check_condition))

    post_condition = mk_post_condition(values)

    print("Bubble sort")
    print("---------------------")

    s.push()
    s.add(Not(post_condition))

    print("Testing the validity of the algorithm; `valid expected`:")

    if s.check() == sat :
        print(f"counterexample:\n{s.model()}")
    else :
        print("valid")

    print("---------------------")

    s.pop()

    s.add(post_condition)
    print("Getting a model...")
    print("Model:")

    if s.check() == sat :
        print(s.model())


if __name__ == "__main__" :
    main()
