############################################
# Copyright (c) 2012 Microsoft Corporation
# 
# Extract enumeration types from z3_api.h
#
# Author: Leonardo de Moura (leonardo)
############################################
import re
import os 

blank_pat      = re.compile("^ *$")
comment_pat    = re.compile("^ *//.*$")
typedef_pat    = re.compile("typedef enum *")
typedef2_pat   = re.compile("typedef enum { *")
openbrace_pat  = re.compile("{ *")
closebrace_pat = re.compile("}.*;")

api = open('..%slib%sz3_api.h' % (os.sep, os.sep), 'r')

z3consts  = open('z3consts.py', 'w')
z3consts.write('# Automatically generated file, generator: mk_z3consts.py\n\n')

SEARCHING  = 0
FOUND_ENUM = 1
IN_ENUM    = 2

mode    = SEARCHING
decls   = {}
idx     = 0

linenum = 1
for line in api:
    m1 = blank_pat.match(line)
    m2 = comment_pat.match(line)
    if m1 or m2:
        # skip blank lines and comments
        linenum = linenum + 1 
    elif mode == SEARCHING:
        m = typedef_pat.match(line)
        if m:
            mode = FOUND_ENUM
        m = typedef2_pat.match(line)
        if m:
            mode = IN_ENUM
            decls = {}
            idx   = 0
    elif mode == FOUND_ENUM:
        m = openbrace_pat.match(line)
        if m:
            mode  = IN_ENUM
            decls = {}
            idx   = 0
        else:
            assert False, "Invalid z3_api.h, line: %s" % linenum
    else:
        assert mode == IN_ENUM
        words = re.split('[^\-a-zA-Z0-9_]+', line)
        m = closebrace_pat.match(line)
        if m:
            name = words[1]
            z3consts.write('# enum %s\n' % name)
            for k, i in decls.iteritems():
                z3consts.write('%s = %s\n' % (k, i))
            z3consts.write('\n')
            mode = SEARCHING
        else:
            if words[2] != '':
                if len(words[2]) > 1 and words[2][1] == 'x':
                    idx = int(words[2], 16)
                else:
                    idx = int(words[2])
            decls[words[1]] = idx
            idx = idx + 1
    linenum = linenum + 1
