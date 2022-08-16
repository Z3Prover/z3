
import subprocess
import sys
import re

Z3_EXE = "z3.exe"

def help(ous):
    
    ous.write("Z3 Options\n")
    out = subprocess.Popen([Z3_EXE, "-pm"],stdout=subprocess.PIPE).communicate()[0]
    modules = []
    if out != None:
        out = out.decode(sys.stdout.encoding)
        module_re = re.compile(r"\[module\] (.*)\,")
        lines = out.split("\n")
        for line in lines:
            m = module_re.search(line)
            if m:
                modules += [m.group(1)]
        for module in modules:
            out = subprocess.Popen([Z3_EXE, "-pmmd:%s" % module],stdout=subprocess.PIPE).communicate()[0]
            if out == None:
                continue
            out = out.decode(sys.stdout.encoding)
            out = out.replace("\r","")
            ous.write(out)

with open("Parameters.md",'w') as ous:
    help(ous)
