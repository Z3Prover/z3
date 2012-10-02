import re

pat1 = re.compile(".*Z3_API.*")
api = open('..\lib\z3_api.h', 'r')

z3def = open('z3.def', 'w')
z3dbgdef = open('z3_dbg.def', 'w')

z3def.write('LIBRARY "Z3"\nEXPORTS\n')
z3dbgdef.write('LIBRARY "Z3_DBG"\nEXPORTS\n')

num = 1
for line in api:
    m = pat1.match(line)
    if m:
        words = re.split('\W+', line)
        i = 0
        for w in words:
            if w == 'Z3_API':
                f = words[i+1]
                z3def.write('\t%s @%s\n' % (f, num))
                z3dbgdef.write('\t%s @%s\n' % (f, num))
            i = i + 1
        num = num + 1
