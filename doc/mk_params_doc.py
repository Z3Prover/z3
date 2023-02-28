# Copyright (c) Microsoft Corporation 2015
"""
Z3 API documentation for parameters
"""

import argparse
import subprocess
import sys
import re
import os

BUILD_DIR='../build'
OUTPUT_DIRECTORY=os.path.join(os.getcwd(), 'api')

def parse_options():
    global BUILD_DIR, OUTPUT_DIRECTORY
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('-b',
        '--build',
        default=BUILD_DIR,
        help='Directory where Z3 is built (default: %(default)s)',
    )
    parser.add_argument('--output-dir',
        dest='output_dir',
        default=OUTPUT_DIRECTORY,
        help='Path to output directory (default: %(default)s)',
    )

    pargs = parser.parse_args()
    BUILD_DIR = pargs.build
    OUTPUT_DIRECTORY = pargs.output_dir

def help(ous):
    global BUILD_DIR
    ous.write("Z3 Options\n")
    z3_exe = BUILD_DIR + "/z3"
    out = subprocess.Popen([z3_exe, "-pm"],stdout=subprocess.PIPE).communicate()[0]
    modules = ["global"]
    if out != None:
        out = out.decode(sys.getdefaultencoding())
        module_re = re.compile(r"\[module\] (.*)\,")
        lines = out.split("\n")
        for line in lines:
            m = module_re.search(line)
            if m:
                modules += [m.group(1)]
        for module in modules:
            out = subprocess.Popen([z3_exe, "-pmmd:%s" % module],stdout=subprocess.PIPE).communicate()[0]
            if out == None:
                continue
            out = out.decode(sys.getdefaultencoding())
            out = out.replace("\r","")
            ous.write(out)

parse_options()

def mk_dir(d):
    if not os.path.exists(d):
        os.makedirs(d)

mk_dir(os.path.join(OUTPUT_DIRECTORY, 'md'))

with open(OUTPUT_DIRECTORY + "/md/Parameters.md",'w') as ous:
    help(ous)
