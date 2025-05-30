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

ML_ENABLED=False
MLD_ENABLED=False
JS_ENABLED=False
BUILD_DIR='../build'
DOXYGEN_EXE='doxygen'
TEMP_DIR=os.path.join(os.getcwd(), 'tmp')
OUTPUT_DIRECTORY=os.path.join(os.getcwd(), 'api')
Z3PY_PACKAGE_PATH='../src/api/python/z3'
JS_API_PATH='../src/api/js'
Z3PY_ENABLED=True
DOTNET_ENABLED=True
JAVA_ENABLED=True
Z3OPTIONS_ENABLED=True
DOTNET_API_SEARCH_PATHS=['../src/api/dotnet']
JAVA_API_SEARCH_PATHS=['../src/api/java']
SCRIPT_DIR=os.path.abspath(os.path.dirname(__file__))

def parse_options():
    global ML_ENABLED, MLD_ENABLED, BUILD_DIR, DOXYGEN_EXE, TEMP_DIR, OUTPUT_DIRECTORY
    global Z3PY_PACKAGE_PATH, Z3PY_ENABLED, DOTNET_ENABLED, JAVA_ENABLED, JS_ENABLED
    global DOTNET_API_SEARCH_PATHS, JAVA_API_SEARCH_PATHS, JS_API_PATH
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
    parser.add_argument('--mld',
        action='store_true',
        default=False,
        help='Include ML/OCaml API documentation'
    )
    parser.add_argument('--js',
        action='store_true',
        default=False,
        help='Include JS/TS API documentation'
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
    parser.add_argument('--z3py-package-path',
        dest='z3py_package_path',
        default=Z3PY_PACKAGE_PATH,
        help='Path to directory containing Z3py package (default: %(default)s)',
    )
    # FIXME: I would prefer not to have negative options (i.e.  `--z3py`
    # instead of `--no-z3py`) but historically these bindings have been on by
    # default so we have options to disable generating documentation for these
    # bindings rather than enable them.
    parser.add_argument('--no-z3py',
        dest='no_z3py',
        action='store_true',
        default=False,
        help='Do not generate documentation for Python bindings',
    )
    parser.add_argument('--no-dotnet',
        dest='no_dotnet',
        action='store_true',
        default=False,
        help='Do not generate documentation for .NET bindings',
    )
    parser.add_argument('--no-java',
        dest='no_java',
        action='store_true',
        default=False,
        help='Do not generate documentation for Java bindings',
    )
    parser.add_argument('--dotnet-search-paths',
        dest='dotnet_search_paths',
        nargs='+',
        default=DOTNET_API_SEARCH_PATHS,
        help='Specify one or more path to look for .NET files (default: %(default)s).',
    )
    parser.add_argument('--java-search-paths',
        dest='java_search_paths',
        nargs='+',
        default=JAVA_API_SEARCH_PATHS,
        help='Specify one or more paths to look for Java files (default: %(default)s).',
    )
    pargs = parser.parse_args()
    ML_ENABLED = pargs.ml
    MLD_ENABLED = pargs.mld
    JS_ENABLED = pargs.js
    BUILD_DIR = pargs.build
    DOXYGEN_EXE = pargs.doxygen_executable
    TEMP_DIR = pargs.temp_dir
    OUTPUT_DIRECTORY = pargs.output_dir
    Z3PY_PACKAGE_PATH = pargs.z3py_package_path
    Z3PY_ENABLED = not pargs.no_z3py
    DOTNET_ENABLED = not pargs.no_dotnet
    JAVA_ENABLED = not pargs.no_java
    DOTNET_API_SEARCH_PATHS = pargs.dotnet_search_paths
    JAVA_API_SEARCH_PATHS = pargs.java_search_paths

    if Z3PY_ENABLED:
        if not os.path.exists(Z3PY_PACKAGE_PATH):
            raise Exception('"{}" does not exist'.format(Z3PY_PACKAGE_PATH))
        if not os.path.basename(Z3PY_PACKAGE_PATH) == 'z3':
            raise Exception('"{}" does not end with "z3"'.format(Z3PY_PACKAGE_PATH))
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
    pat4  = re.compile("Z3_DECLARE_CLOSURE.*")
    pat5  = re.compile("DEFINE_TYPE.*")
    _inf  = open(inf, 'r')
    _outf = open(outf, 'w')
    for line in _inf:
        if not pat1.match(line) and not pat2.match(line) and not pat3.match(line) and not pat4.match(line) and not pat5.match(line):
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

def generate_trace_tag_docs():
    """Generate trace tag documentation from trace_tags.def file.
    
    This function reads the trace_tags.def file and generates a markdown table with the following format:
    
    # Z3 Trace Tags Documentation
    
    This document contains the trace tags and their descriptions used in Z3.
    
    | Tag | Class | Description |
    |-----|-------|-------------|
    | Global | Global | Unknown Class |
    | add_bounds_tactic | arith_bounds_tactic | add bounds tactic |
    | parser | parser | parser functionality |
    
    The def file format should be:
    X(class, tag, "description")
    
    For example:
    X(Global, Global, "Unknown Class")
    X(add_bounds_tactic, arith_bounds_tactic, "add bounds tactic")
    """
    print("Generating trace tag documentation...")
    def_file = os.path.join(SCRIPT_DIR, "../src/util/trace_tags.def")
    output_md = os.path.join(OUTPUT_DIRECTORY, "trace_tags.md")
    
    if not os.path.exists(def_file):
        print(f"Warning: {def_file} not found. Skipping trace tag documentation generation.")
        return
        
    with open(def_file, "r") as f:
        lines = f.readlines()

    entries = []
    for line in lines:
        match = re.match(r'X\(\s*(\w+)\s*,\s*(\w+)\s*,\s*"([^"]+)"\s*\)', line)
        if match:
            tag_class, tag, desc = match.groups()
            entries.append((tag_class, tag, desc))

    mk_dir(os.path.dirname(output_md))
    with open(output_md, "w", encoding='utf-8') as f:
        f.write("# Z3 Trace Tags Documentation\n\n")
        f.write("This document contains the trace tags and their descriptions used in Z3.\n\n")
        f.write("| Tag | Class | Description |\n")
        f.write("|-----|-------|-------------|\n")
        for tag, class_name, desc in sorted(entries):
            f.write(f"| {tag} | {class_name} | {desc} |\n")
    
    print(f"Trace tag documentation has been generated at {output_md}")

try:
    parse_options()

    print("Creating temporary directory \"{}\"".format(TEMP_DIR))
    mk_dir(TEMP_DIR)
    
    # Generate trace tag documentation
    generate_trace_tag_docs()
    
    # Short-hand for path to temporary file
    def temp_path(path):
        return os.path.join(TEMP_DIR, path)
    # Short-hand for path to file in `doc` directory
    def doc_path(path):
        return os.path.join(SCRIPT_DIR, path)

    # Create configuration file from template
    doxygen_config_substitutions = {
        'OUTPUT_DIRECTORY': OUTPUT_DIRECTORY,
        'TEMP_DIR': TEMP_DIR,
        'CXX_API_SEARCH_PATHS': doc_path('../src/api/c++'),
    }

    if Z3PY_ENABLED:
        print("Z3Py documentation enabled")
        doxygen_config_substitutions['PYTHON_API_FILES'] = 'z3*.py'
    else:
        print("Z3Py documentation disabled")
        doxygen_config_substitutions['PYTHON_API_FILES'] = ''
    if DOTNET_ENABLED:
        print(".NET documentation enabled")
        doxygen_config_substitutions['DOTNET_API_FILES'] = '*.cs'
        dotnet_api_search_path_str = ""
        for p in DOTNET_API_SEARCH_PATHS:
            # Quote path so that paths with spaces are handled correctly
            dotnet_api_search_path_str += "\"{}\" ".format(p)
        doxygen_config_substitutions['DOTNET_API_SEARCH_PATHS'] = dotnet_api_search_path_str
    else:
        print(".NET documentation disabled")
        doxygen_config_substitutions['DOTNET_API_FILES'] = ''
        doxygen_config_substitutions['DOTNET_API_SEARCH_PATHS'] = ''
    if JAVA_ENABLED:
        print("Java documentation enabled")
        doxygen_config_substitutions['JAVA_API_FILES'] = '*.java'
        java_api_search_path_str = ""
        for p in JAVA_API_SEARCH_PATHS:
            # Quote path so that paths with spaces are handled correctly
            java_api_search_path_str += "\"{}\" ".format(p)
        doxygen_config_substitutions['JAVA_API_SEARCH_PATHS'] = java_api_search_path_str
    else:
        print("Java documentation disabled")
        doxygen_config_substitutions['JAVA_API_FILES'] = ''
        doxygen_config_substitutions['JAVA_API_SEARCH_PATHS'] = ''
    if JS_ENABLED:
        print('Javascript documentation enabled')
    else:
        print('Javascript documentation disabled')


    doxygen_config_file = temp_path('z3api.cfg')
    configure_file(
        doc_path('z3api.cfg.in'),
        doxygen_config_file,
        doxygen_config_substitutions)

    website_dox_substitutions = {}
    bullet_point_prefix='\n   - '
    website_dox_substitutions['CPP_API'] = (
            '{prefix}<a class="el" href="namespacez3.html">C++ API</a> '
            ).format(
                prefix=bullet_point_prefix)
    website_dox_substitutions['C_API'] = (
            '{prefix}<a class="el" href="z3__api_8h.html">C API</a> '
            ).format(
                prefix=bullet_point_prefix)

    if Z3PY_ENABLED:
        print("Python documentation enabled")
        website_dox_substitutions['PYTHON_API'] = (
            '{prefix}<a class="el" href="namespacez3py.html">Python API</a> '
            '(also available in <a class="el" href="z3.html">pydoc format</a>)'
            ).format(
                prefix=bullet_point_prefix)
    else:
        print("Python documentation disabled")
        website_dox_substitutions['PYTHON_API'] = ''
    if DOTNET_ENABLED:
        website_dox_substitutions['DOTNET_API'] = (
            '{prefix}'
            '<a class="el" href="namespace_microsoft_1_1_z3.html">'
            '.NET API</a>').format(
                prefix=bullet_point_prefix)
    else:
        website_dox_substitutions['DOTNET_API'] = ''
    if JAVA_ENABLED:
        website_dox_substitutions['JAVA_API'] = (
            '{prefix}<a class="el" href="namespacecom_1_1microsoft_1_1z3.html">'
            'Java API</a>').format(
                prefix=bullet_point_prefix)
    else:
        website_dox_substitutions['JAVA_API'] = ''
    if ML_ENABLED or MLD_ENABLED:
        website_dox_substitutions['OCAML_API'] = (
            '{prefix}<a class="el" href="ml/index.html">ML/OCaml API</a>'
            ).format(
                prefix=bullet_point_prefix)
    else:
        website_dox_substitutions['OCAML_API'] = ''
    if JS_ENABLED:
        website_dox_substitutions['JS_API'] = (
            '{prefix}<a class="el" href="js/index.html">Javascript/Typescript API</a>'
            ).format(
                prefix=bullet_point_prefix)
    else:
        website_dox_substitutions['JS_API'] = ''
    configure_file(
        doc_path('website.dox.in'),
        temp_path('website.dox'),
        website_dox_substitutions)

    mk_dir(os.path.join(OUTPUT_DIRECTORY, 'html'))
    if Z3PY_ENABLED:
        shutil.copyfile(doc_path('../src/api/python/z3/z3.py'), temp_path('z3py.py'))
    cleanup_API(doc_path('../src/api/z3_api.h'), temp_path('z3_api.h'))
    cleanup_API(doc_path('../src/api/z3_ast_containers.h'), temp_path('z3_ast_containers.h'))
    cleanup_API(doc_path('../src/api/z3_algebraic.h'), temp_path('z3_algebraic.h'))
    cleanup_API(doc_path('../src/api/z3_polynomial.h'), temp_path('z3_polynomial.h'))
    cleanup_API(doc_path('../src/api/z3_rcf.h'), temp_path('z3_rcf.h'))
    cleanup_API(doc_path('../src/api/z3_fixedpoint.h'), temp_path('z3_fixedpoint.h'))
    cleanup_API(doc_path('../src/api/z3_optimization.h'), temp_path('z3_optimization.h'))
    cleanup_API(doc_path('../src/api/z3_fpa.h'), temp_path('z3_fpa.h'))

    print("Removed annotations from z3_api.h.")
    try:
        if subprocess.call([DOXYGEN_EXE, doxygen_config_file]) != 0:
            print("ERROR: doxygen returned nonzero return code")
            exit(1)
    except:
        print("ERROR: failed to execute 'doxygen', make sure doxygen (http://www.doxygen.org) is available in your system.")
        exit(1)
    print("Generated Doxygen based documentation")
    shutil.rmtree(os.path.realpath(TEMP_DIR))
    print("Removed temporary directory \"{}\"".format(TEMP_DIR))
    if Z3PY_ENABLED:
        # Put z3py at the beginning of the search path to try to avoid picking up
        # an installed copy of Z3py.
        sys.path.insert(0, os.path.dirname(Z3PY_PACKAGE_PATH))

        if sys.version < '3':
            import __builtin__
            __builtin__.Z3_LIB_DIRS = [ BUILD_DIR ]
        else:
            import builtins
            builtins.Z3_LIB_DIRS = [ BUILD_DIR ]

        for modulename in (
                'z3',
                'z3.z3',
                'z3.z3consts',
                'z3.z3core',
                'z3.z3num',
                'z3.z3poly',
                'z3.z3printer',
                'z3.z3rcf',
                'z3.z3types',
                'z3.z3util',
                ):
            pydoc.writedoc(modulename)
            doc = modulename + '.html'
            shutil.move(doc, os.path.join(OUTPUT_DIRECTORY, 'html', doc))

        print("Generated pydoc Z3Py documentation.")

    if ML_ENABLED:
        ml_output_dir = os.path.join(OUTPUT_DIRECTORY, 'html', 'ml')
        mk_dir(ml_output_dir)
        if subprocess.call(['ocamldoc', '-html', '-d', ml_output_dir, '-sort', '-hide', 'Z3', '-I', '$(ocamlfind query zarith)', '-I', '%s/api/ml' % BUILD_DIR, '%s/api/ml/z3enums.mli' % BUILD_DIR, '%s/api/ml/z3.mli' % BUILD_DIR]) != 0:
            print("ERROR: ocamldoc failed.")
            exit(1)
        print("Generated ML/OCaml documentation.")

    if JS_ENABLED:
        try:
            subprocess.check_output(['npm', 'run', '--prefix=%s' % JS_API_PATH, 'check-engine'])
        except subprocess.CalledProcessError as e:
            print("ERROR: node version check failed.")
            print(e.output)
            exit(1)
        if subprocess.call(['npm', 'run', '--prefix=%s' % JS_API_PATH, 'docs']) != 0:
            print("ERROR: npm run docs failed.")
            exit(1)
        print("Generated Javascript documentation.")

    print("Documentation was successfully generated at subdirectory '{}'.".format(OUTPUT_DIRECTORY))
except Exception:
    exctype, value = sys.exc_info()[:2]
    print("ERROR: failed to generate documentation: %s" % value)
    exit(1)

