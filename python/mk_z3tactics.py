############################################
# Copyright (c) 2012 Microsoft Corporation
# 
# Extract tactics and probes from install_tactics.cpp
#
# Author: Leonardo de Moura (leonardo)
############################################
import re
import os

tactic_pat  = re.compile("^[ \t]*ADD_TACTIC_CMD")
probe_pat   = re.compile("^[ \t]*ADD_PROBE")

cppfile = open('..%slib%sinstall_tactics.cpp' % (os.sep, os.sep), 'r')

z3tactics  = open('z3tactics.py', 'w')
z3tactics.write('# Automatically generated file, generator: mk_z3tactics.py\n')
z3tactics.write('import z3core\n')
z3tactics.write('import z3\n\n')


for line in cppfile:
    m1 = tactic_pat.match(line)
    m2 = probe_pat.match(line)
    if m1:
        words     = re.split('[^\-a-zA-Z0-9_]+', line)
        tactic    = words[2]
        py_tactic = tactic.replace('-', '_')
        z3tactics.write('def %s_tactic(ctx=None):\n' % py_tactic)
        z3tactics.write('  ctx = z3._get_ctx(ctx)\n')
        z3tactics.write('  return z3.Tactic(z3core.Z3_mk_tactic(ctx.ref(), \'%s\'), ctx)\n\n' % tactic)
    elif m2:
        words = re.split('[^\-a-zA-Z0-9_]+', line)
        probe     = words[2]
        py_probe  = probe.replace('-', '_')
        z3tactics.write('def %s_probe(ctx=None):\n' % py_probe)
        z3tactics.write('  ctx = z3._get_ctx(ctx)\n')
        z3tactics.write('  return z3.Probe(z3core.Z3_mk_probe(ctx.ref(), \'%s\'), ctx)\n\n' % probe)

