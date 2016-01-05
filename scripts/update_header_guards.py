# Copyright (c) 2015 Microsoft Corporation

import os
import re

ifndef  = re.compile("#ifndef \_(.*)\_H\_")
doubleu = re.compile("#(.*) (.*)\_\_H\_")
defn    = re.compile("#define \_(.*)\_H\_")
endif   = re.compile("#endif /\* \_(.*)\_H\_")


def fix_hdr(file):
    print(file)
    tmp = "%s.tmp" % file
    ins = open(file)
    ous = open(tmp,'w')
    line = ins.readline()
    found = False
    while line:
        m = doubleu.search(line)
        if m:
            ous.write("#")
            ous.write(m.group(1))
            ous.write(" ")
            ous.write(m.group(2))
            ous.write("_H_\n")
            line = ins.readline()
            found = True
            continue
        m = ifndef.search(line)
        if m:
            print(m.group(1))
            ous.write("#ifndef ")
            ous.write(m.group(1))
            ous.write("_H_\n")
            line = ins.readline()
            found = True
            continue
        m = defn.search(line)
        if m:
            ous.write("#define ")
            ous.write(m.group(1))
            ous.write("_H_\n")
            line = ins.readline()
            found = True
            continue
        m = endif.search(line)
        if m:
            ous.write("#endif /* ")
            ous.write(m.group(1))
            ous.write("_H_ */\n")
            line = ins.readline()
            found = True
            continue
        ous.write(line)
        line = ins.readline()
    ins.close()
    ous.close()
    if found:
        os.system("move %s %s" % (tmp, file))
    else:
        os.system("del %s" % tmp)

def fixup(dir):
    for root, dirs, files in os.walk(dir):
        for f in files:
            if f.endswith('.h'):
                path = "%s\\%s" % (root, f)
                fix_hdr(path)

fixup('src')
