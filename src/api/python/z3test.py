############################################
# Copyright (c) 2012 Microsoft Corporation
# 
# Z3 Python interface
#
# Author: Leonardo de Moura (leonardo)
############################################
import z3, doctest, sys

if len(sys.argv) < 2 or sys.argv[1] == 'z3':
    r = doctest.testmod(z3.z3)
elif sys.argv[1] == 'z3num':
    r = doctest.testmod(z3.z3num)
else:
    print('Usage: z3test.py (z3 | z3num)')
    sys.exit(1)

if r.failed != 0:
    sys.exit(1)

