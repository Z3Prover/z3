############################################
# Copyright (c) 2012 Microsoft Corporation
# 
# Z3 Python interface
#
# Author: Leonardo de Moura (leonardo)
############################################
import z3, doctest

r = doctest.testmod(z3)
if r.failed != 0:
    exit(1)

