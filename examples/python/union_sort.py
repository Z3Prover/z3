# Copyright Microsoft Corporation 2019
# This example illustrates the use of union types
# from the Python API. It is given as an example
# as response to #2215.

from z3 import *

u = Datatype('IntOrString')
u.declare('IntV', ('int', IntSort()))
u.declare('StringV', ('string', StringSort()))
IntOrString = u.create()
StringV = IntOrString.StringV
IntV = IntOrString.IntV

print(IntV(1))
print(StringV(StringVal("abc")))
print(IntV(1).sort())
print(IntV(1) == StringV(StringVal("abc")))
s = String('s')
print(simplify(IntV(1) == StringV(s)))
