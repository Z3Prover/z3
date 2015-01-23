import os
import shutil
import re
import pydoc
import sys
import subprocess
import shutil

def mk_dir(d):
    if not os.path.exists(d):
        os.makedirs(d)

# Eliminate def_API and extra_API directives from file 'inf'.
# The result is stored in 'outf'.
def cleanup_API(inf, outf):
    pat1  = re.compile(".*def_API.*")
    pat2  = re.compile(".*extra_API.*")
    _inf  = open(inf, 'r')
    _outf = open(outf, 'w') 
    for line in _inf:
        if not pat1.match(line) and not pat2.match(line):
            _outf.write(line)

try:
    mk_dir('api/html')
    mk_dir('tmp')
    shutil.copyfile('website.dox', 'tmp/website.dox')
    shutil.copyfile('../src/api/python/z3.py', 'tmp/z3py.py')
    cleanup_API('../src/api/z3_api.h', 'tmp/z3_api.h')
    cleanup_API('../src/api/z3_algebraic.h', 'tmp/z3_algebraic.h')
    cleanup_API('../src/api/z3_polynomial.h', 'tmp/z3_polynomial.h')
    cleanup_API('../src/api/z3_rcf.h', 'tmp/z3_rcf.h')
    cleanup_API('../src/api/z3_interp.h', 'tmp/z3_interp.h')
    cleanup_API('../src/api/z3_fpa.h', 'tmp/z3_fpa.h')
    
    print "Removed annotations from z3_api.h."
    try:
        if subprocess.call(['doxygen', 'z3api.dox']) != 0:
            print "ERROR: doxygen returned nonzero return code"
            exit(1)
    except:
        print "ERROR: failed to execute 'doxygen', make sure doxygen (http://www.doxygen.org) is available in your system."
        exit(1)
    print "Generated C and .NET API documentation."
    os.remove('tmp/z3_api.h')
    os.remove('tmp/z3_algebraic.h')
    os.remove('tmp/z3_polynomial.h')
    os.remove('tmp/z3_rcf.h')
    os.remove('tmp/z3_interp.h')
    os.remove('tmp/z3_fpa.h')
    print "Removed temporary file z3_api.h."
    os.remove('tmp/website.dox')	
    print "Removed temporary file website.dox"
    os.remove('tmp/z3py.py')	
    print "Removed temporary file z3py.py"
    os.removedirs('tmp')
    print "Removed temporary directory tmp."
    sys.path.append('../src/api/python')
    pydoc.writedoc('z3')
    shutil.move('z3.html', 'api/html/z3.html')
    print "Generated Python documentation."
    print "Documentation was successfully generated at subdirectory './api/html'."
except:
    print "ERROR: failed to generate documentation"
    exit(1)
