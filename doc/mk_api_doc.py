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
DOXYGEN_EXE='doxygen'
TEMP_DIR=os.path.join(os.getcwd(), 'tmp')
OUTPUT_DIRECTORY=os.path.join(os.getcwd(), 'api')

def parse_options():
    global ML_ENABLED, BUILD_DIR, DOXYGEN_EXE, TEMP_DIR, OUTPUT_DIRECTORY
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
    parser.add_argument('--doxygen-executable',
        dest='doxygen_executable',
        default=DOXYGEN_EXE,
        help='Doxygen executable to use (default: %(default)s)',
    )
    parser.add_argument('--temp-dir',
        dest='temp_dir',
        default=TEMP_DIR,
        help='Path to directory to use as temporary directory. '
             '(default: %(default)s)',
    )
    parser.add_argument('--output-dir',
        dest='output_dir',
        default=OUTPUT_DIRECTORY,
        help='Path to output directory (default: %(default)s)',
    )
    pargs = parser.parse_args()
    ML_ENABLED = pargs.ml
    BUILD_DIR = pargs.build
    DOXYGEN_EXE = pargs.doxygen_executable
    TEMP_DIR = pargs.temp_dir
    OUTPUT_DIRECTORY = pargs.output_dir
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

def configure_file(template_file_path, output_file_path, substitutions):
    """
        Read a template file ``template_file_path``, perform substitutions
        found in the ``substitutions`` dictionary and write the result to
        the output file ``output_file_path``.

        The template file should contain zero or more template strings of the
        form ``@NAME@``.

        The substitutions dictionary maps old strings (without the ``@``
        symbols) to their replacements.
    """
    assert isinstance(template_file_path, str)
    assert isinstance(output_file_path, str)
    assert isinstance(substitutions, dict)
    assert len(template_file_path) > 0
    assert len(output_file_path) > 0
    print("Generating {} from {}".format(output_file_path, template_file_path))

    if not os.path.exists(template_file_path):
        raise Exception('Could not find template file "{}"'.format(template_file_path))

    # Read whole template file into string
    template_string = None
    with open(template_file_path, 'r') as f:
        template_string = f.read()

    # Do replacements
    for (old_string, replacement) in substitutions.items():
        template_string = template_string.replace('@{}@'.format(old_string), replacement)

    # Write the string to the file
    with open(output_file_path, 'w') as f:
        f.write(template_string)

try:
    parse_options()

    print("Creating temporary directory \"{}\"".format(TEMP_DIR))
    mk_dir(TEMP_DIR)
    # Short-hand for path to temporary file
    def temp_path(path):
        return os.path.join(TEMP_DIR, path)

    # Create configuration file from template
    doxygen_config_substitutions = {
        'OUTPUT_DIRECTORY': OUTPUT_DIRECTORY,
    }
    doxygen_config_file = temp_path('z3api.cfg')
    configure_file('z3api.cfg.in', doxygen_config_file, doxygen_config_substitutions)

    website_dox_substitutions = {}
    if ML_ENABLED:
        website_dox_substitutions['OCAML_API'] = '\n   - <a class="el" href="ml/index.html">ML/OCaml API</a>\n'
    else:
        website_dox_substitutions['OCAML_API'] = ''
    configure_file('website.dox.in', temp_path('website.dox'), website_dox_substitutions)

    mk_dir(os.path.join(OUTPUT_DIRECTORY, 'html'))
    shutil.copyfile('../src/api/python/z3/z3.py', temp_path('z3py.py'))
    cleanup_API('../src/api/z3_api.h', temp_path('z3_api.h'))
    cleanup_API('../src/api/z3_ast_containers.h', temp_path('z3_ast_containers.h'))
    cleanup_API('../src/api/z3_algebraic.h', temp_path('z3_algebraic.h'))
    cleanup_API('../src/api/z3_polynomial.h', temp_path('z3_polynomial.h'))
    cleanup_API('../src/api/z3_rcf.h', temp_path('z3_rcf.h'))
    cleanup_API('../src/api/z3_fixedpoint.h', temp_path('z3_fixedpoint.h'))
    cleanup_API('../src/api/z3_optimization.h', temp_path('z3_optimization.h'))
    cleanup_API('../src/api/z3_interp.h', temp_path('z3_interp.h'))
    cleanup_API('../src/api/z3_fpa.h', temp_path('z3_fpa.h'))

    print("Removed annotations from z3_api.h.")
    try:
        if subprocess.call([DOXYGEN_EXE, doxygen_config_file]) != 0:
            print("ERROR: doxygen returned nonzero return code")
            exit(1)
    except:
        print("ERROR: failed to execute 'doxygen', make sure doxygen (http://www.doxygen.org) is available in your system.")
        exit(1)
    print("Generated C and .NET API documentation.")
    shutil.rmtree(os.path.realpath(TEMP_DIR))
    print("Removed temporary directory \"{}\"".format(TEMP_DIR))
    sys.path.append('../src/api/python/z3')
    pydoc.writedoc('z3')
    shutil.move('z3.html', os.path.join(OUTPUT_DIRECTORY, 'html', 'z3.html'))
    print("Generated Python documentation.")

    if ML_ENABLED:
        ml_output_dir = os.path.join(OUTPUT_DIRECTORY, 'html', 'ml')
        mk_dir(ml_output_dir)
        if subprocess.call(['ocamldoc', '-html', '-d', ml_output_dir, '-sort', '-hide', 'Z3', '-I', '%s/api/ml' % BUILD_DIR, '../src/api/ml/z3enums.mli', '../src/api/ml/z3.mli']) != 0:
            print("ERROR: ocamldoc failed.")
            exit(1)
        print("Generated ML/OCaml documentation.")

    print("Documentation was successfully generated at subdirectory '{}'.".format(OUTPUT_DIRECTORY))
except Exception:
    exctype, value = sys.exc_info()[:2]
    print("ERROR: failed to generate documentation: %s" % value)
    exit(1)
