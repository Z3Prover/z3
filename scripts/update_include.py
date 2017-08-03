# Copyright (c) 2017 Microsoft Corporation

import os
import re

is_include = re.compile("#include \"(.*)\"")
is_include2 = re.compile("#include\"(.*)\"")


def fix_include(file, paths):
    tmp = "%s.tmp" % file
    ins = open(file)
    ous = open(tmp,'w')
    line = ins.readline()
    found = False
    while line:
        m = is_include.search(line)
        if m and m.group(1) in paths:
            ous.write("#include \"")
            ous.write(paths[m.group(1)])
            ous.write("\"\n")
            found = True
            line = ins.readline()
            continue
        m = is_include2.search(line)
        if m and m.group(1) in paths:
            ous.write("#include \"")
            ous.write(paths[m.group(1)])
            ous.write("\"\n")
            found = True
            line = ins.readline()
            continue
        ous.write(line)            
        line = ins.readline()
    ins.close()
    ous.close()
    if found:
        print(file)
        os.system("move %s %s" % (tmp, file))
    else:
        os.system("del %s" % tmp)

def find_paths(dir):
    paths = {}
    for root, dirs, files in os.walk(dir):
        root1 = root.replace("\\","/")[4:]
        for f in files:
            if f.endswith('.h') or f.endswith('.hpp') or f.endswith('.cpp'):
                path = "%s/%s" % (root1, f)
                paths[f] = path
            if f.endswith('.pyg'):
                f = f.replace("pyg","hpp")
                path = "%s/%s" % (root1, f)
                paths[f] = path
    return paths

paths = find_paths('src')

def fixup(dir):
    for root, dirs, files in os.walk(dir):
        for f in files:
            if f == "z3.h":
                continue
            if f.endswith('.h') or f.endswith('.cpp'):
                path = "%s\\%s" % (root, f)
                fix_include(path, paths)


fixup('src')
