############################################
# Copyright (c) 2012 Microsoft Corporation
# 
# Extract enumeration types from z3_api.h
#
# Author: Leonardo de Moura (leonardo)
#         Christoph M. Wintersteiger (cwinter)
############################################
import re

blank_pat      = re.compile("^ *$")
comment_pat    = re.compile("^ *//.*$")
typedef_pat    = re.compile("typedef enum *")
typedef2_pat   = re.compile("typedef enum { *")
openbrace_pat  = re.compile("{ *")
closebrace_pat = re.compile("}.*;")

api = open('..\\lib\\z3_api.h', 'r')

DeprecatedEnums = { 'Z3_search_failure' }

z3consts  = open('Enumerations.cs', 'w')
z3consts.write('// Automatically generated file, generator: mk_z3consts.py\n\n')
z3consts.write('using System;\n\n'
               '#pragma warning disable 1591\n\n'
               'namespace Microsoft.Z3\n'
               '{\n');

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
            if name not in DeprecatedEnums:
                z3consts.write('  /// <summary>%s</summary>\n' % name)
                z3consts.write('  public enum %s {\n' % name)
                z3consts.write
                for k, i in decls.iteritems():
                    z3consts.write('  %s = %s,\n' % (k, i))
                z3consts.write('  }\n\n')
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

z3consts.write('}\n');
