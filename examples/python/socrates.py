############################################
# Copyright (c) Microsoft Corporation. All Rights Reserved.
#
# all humans are mortal
# Socrates is a human
# so Socrates mortal 
############################################

from z3 import *

set_param(proof=True)

Object = DeclareSort('Object')

Human = Function('Human', Object, BoolSort())
Mortal = Function('Mortal', Object, BoolSort())

# a well known philosopher 
socrates = Const('socrates', Object)

# free variables used in forall must be declared Const in python
x = Const('x', Object)

axioms = [ForAll([x], Implies(Human(x), Mortal(x))), 
          Human(socrates) == True]


s = Solver()
s.add(axioms)
# classical refutation
s.add(Mortal(socrates) == False)

print(s.check()) # prints unsat so socrates is Mortal

# print(s.proof()) # prints a low level (not readable) proof object.
