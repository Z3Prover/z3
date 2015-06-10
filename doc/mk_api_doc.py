# Copyright (c) Microsoft Corporation 2015

import os
import shutil
import re
import getopt
import pydoc
import sys
import subprocess
import shutil

ML_ENABLED=False
BUILD_DIR='../build'

def norm_path(p):
    # We use '/' on mk_project for convenience
    return os.path.join(*(p.split('/')))

def display_help(exit_code):
    print("mk_api_doc.py: Z3 documentation generator\n")
    print("\nOptions:")
    print("  -h, --help                    display this message.")
    print("  -b <subdir>, --build=<subdir> subdirectory where Z3 is built (default: ../build).")
    print("  --ml                          include ML/OCaml API documentation.")

def parse_options():
    global ML_ENABLED, BUILD_DIR

    try:
        options, remainder = getopt.gnu_getopt(sys.argv[1:],
                                               'b:h',
                                               ['build=', 'help', 'ml'])
    except:
        print("ERROR: Invalid command line option")
        display_help(1)

    for opt, arg in options:
        if opt in ('-b', '--build'):
            BUILD_DIR = norm_path(arg)
        elif opt in ('h', '--help'):
            display_help()
            exit(1)
        elif opt in ('--ml'):
            ML_ENABLED=True            
        else:
            print("ERROR: Invalid command line option: %s" % opt)
            display_help(1)




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
    parse_options()

    fi = open('website.dox', 'r')
    fo = open('website-adj.dox', 'w')

    for line in fi:
        if (line != '[ML]\n'):
            fo.write(line)
        elif (ML_ENABLED):
            fo.write('   - <a class="el" href="ml/index.html">ML/OCaml API</a>\n')
    fi.close()
    fo.close()

    mk_dir('api/html')
    mk_dir('tmp')
    shutil.copyfile('website-adj.dox', 'tmp/website.dox')
    os.remove('website-adj.dox')
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

    if ML_ENABLED:
        mk_dir('api/html/ml')
        if subprocess.call(['ocamldoc', '-html', '-d', 'api\html\ml', '-sort', '-hide', 'Z3', '-I', '%s/api/ml' % BUILD_DIR, '../src/api/ml/z3enums.mli', '../src/api/ml/z3.mli']) != 0:
            print "ERROR: ocamldoc failed."
            exit(1)
        print "Generated ML/OCaml documentation."
        
    print "Documentation was successfully generated at subdirectory './api/html'."
except:
    print "ERROR: failed to generate documentation"
    exit(1)
