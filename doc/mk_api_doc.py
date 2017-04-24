# Copyright (c) Microsoft Corporation 2015
"""
Z3 API documentation generator script
"""

import argparse
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

def parse_options():
    global ML_ENABLED, BUILD_DIR
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('-b',
        '--build',
        default=BUILD_DIR,
        help='Directory where Z3 is built (default: %(default)s)',
    )
    parser.add_argument('--ml',
        action='store_true',
        default=False,
        help='Include ML/OCaml API documentation'
    )
    pargs = parser.parse_args()
    ML_ENABLED = pargs.ml
    BUILD_DIR = pargs.build
    return

def mk_dir(d):
    if not os.path.exists(d):
        os.makedirs(d)

# Eliminate def_API, extra_API, and def_Type directives from file 'inf'.
# The result is stored in 'outf'.
def cleanup_API(inf, outf):
    pat1  = re.compile(".*def_API.*")
    pat2  = re.compile(".*extra_API.*")
    pat3  = re.compile(r".*def_Type\(.*")
    _inf  = open(inf, 'r')
    _outf = open(outf, 'w')
    for line in _inf:
        if not pat1.match(line) and not pat2.match(line) and not pat3.match(line):
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
    shutil.copyfile('../src/api/python/z3/z3.py', 'tmp/z3py.py')
    cleanup_API('../src/api/z3_api.h', 'tmp/z3_api.h')
    cleanup_API('../src/api/z3_ast_containers.h', 'tmp/z3_ast_containers.h')
    cleanup_API('../src/api/z3_algebraic.h', 'tmp/z3_algebraic.h')
    cleanup_API('../src/api/z3_polynomial.h', 'tmp/z3_polynomial.h')
    cleanup_API('../src/api/z3_rcf.h', 'tmp/z3_rcf.h')
    cleanup_API('../src/api/z3_fixedpoint.h', 'tmp/z3_fixedpoint.h')
    cleanup_API('../src/api/z3_optimization.h', 'tmp/z3_optimization.h')
    cleanup_API('../src/api/z3_interp.h', 'tmp/z3_interp.h')
    cleanup_API('../src/api/z3_fpa.h', 'tmp/z3_fpa.h')

    print("Removed annotations from z3_api.h.")
    try:
        if subprocess.call(['doxygen', 'z3api.dox']) != 0:
            print("ERROR: doxygen returned nonzero return code")
            exit(1)
    except:
        print("ERROR: failed to execute 'doxygen', make sure doxygen (http://www.doxygen.org) is available in your system.")
        exit(1)
    print("Generated C and .NET API documentation.")
    os.remove('tmp/z3_api.h')
    os.remove('tmp/z3_ast_containers.h')
    os.remove('tmp/z3_algebraic.h')
    os.remove('tmp/z3_polynomial.h')
    os.remove('tmp/z3_rcf.h')
    os.remove('tmp/z3_fixedpoint.h')
    os.remove('tmp/z3_optimization.h')
    os.remove('tmp/z3_interp.h')
    os.remove('tmp/z3_fpa.h')
    print("Removed temporary file header files.")

    os.remove('tmp/website.dox')
    print("Removed temporary file website.dox")
    os.remove('tmp/z3py.py')
    print("Removed temporary file z3py.py")
    os.removedirs('tmp')
    print("Removed temporary directory tmp.")
    sys.path.append('../src/api/python/z3')
    pydoc.writedoc('z3')
    shutil.move('z3.html', 'api/html/z3.html')
    print("Generated Python documentation.")

    if ML_ENABLED:
        mk_dir('api/html/ml')
        if subprocess.call(['ocamldoc', '-html', '-d', 'api\html\ml', '-sort', '-hide', 'Z3', '-I', '%s/api/ml' % BUILD_DIR, '../src/api/ml/z3enums.mli', '../src/api/ml/z3.mli']) != 0:
            print("ERROR: ocamldoc failed.")
            exit(1)
        print("Generated ML/OCaml documentation.")

    print("Documentation was successfully generated at subdirectory './api/html'.")
except Exception:
    exctype, value = sys.exc_info()[:2]
    print("ERROR: failed to generate documentation: %s" % value)
    exit(1)
