import z3, doctest
import sys, re

if re.compile("64 bit").search(sys.version):
    z3.init("..\\x64\\external_64\\z3.dll")
else:
    z3.init("..\\external\\z3.dll")
    
doctest.testmod(z3)
