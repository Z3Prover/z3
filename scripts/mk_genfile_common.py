# This file contains code that is common to
# both the Python build system and the CMake
# build system.
#
# The code here generally is involved in
# generating files needed by Z3 at build time.
#
# You should **not** import ``mk_util`` here
# to avoid having this code depend on the
# of the Python build system.
import os
import logging
import re
import sys

# Logger for this module
_logger = logging.getLogger(__name__)


###############################################################################
# Utility functions
###############################################################################
def check_dir_exists(output_dir):
    """
        Returns ``True`` if ``output_dir`` exists, otherwise
        returns ``False``.
    """
    if not os.path.isdir(output_dir):
        _logger.error('"{}" is not an existing directory'.format(output_dir))
        return False
    return True

def check_files_exist(files):
    assert isinstance(files, list)
    for f in files:
        if not os.path.exists(f):
            _logger.error('"{}" does not exist'.format(f))
            return False
    return True

###############################################################################
# Functions for generating constant declarations for language bindings
###############################################################################

def mk_z3consts_py_internal(api_files, output_dir):
    """
        Generate ``z3consts.py`` from the list of API header files
        in ``api_files`` and write the output file into
        the ``output_dir`` directory

        Returns the path to the generated file.
    """
    assert os.path.isdir(output_dir)
    assert isinstance(api_files, list)

    blank_pat      = re.compile("^ *\r?$")
    comment_pat    = re.compile("^ *//.*$")
    typedef_pat    = re.compile("typedef enum *")
    typedef2_pat   = re.compile("typedef enum { *")
    openbrace_pat  = re.compile("{ *")
    closebrace_pat = re.compile("}.*;")

    z3consts  = open(os.path.join(output_dir, 'z3consts.py'), 'w')
    z3consts_output_path = z3consts.name
    z3consts.write('# Automatically generated file\n\n')
    for api_file in api_files:
        api = open(api_file, 'r')

        SEARCHING  = 0
        FOUND_ENUM = 1
        IN_ENUM    = 2

        mode    = SEARCHING
        decls   = {}
        idx     = 0

        linenum = 1
        for line in api:
            m1 = blank_pat.match(line)
            m2 = comment_pat.match(line)
            if m1 or m2:
                # skip blank lines and comments
                linenum = linenum + 1
            elif mode == SEARCHING:
                m = typedef_pat.match(line)
                if m:
                    mode = FOUND_ENUM
                m = typedef2_pat.match(line)
                if m:
                    mode = IN_ENUM
                    decls = {}
                    idx   = 0
            elif mode == FOUND_ENUM:
                m = openbrace_pat.match(line)
                if m:
                    mode  = IN_ENUM
                    decls = {}
                    idx   = 0
                else:
                    assert False, "Invalid %s, line: %s" % (api_file, linenum)
            else:
                assert mode == IN_ENUM
                words = re.split('[^\-a-zA-Z0-9_]+', line)
                m = closebrace_pat.match(line)
                if m:
                    name = words[1]
                    z3consts.write('# enum %s\n' % name)
                    for k in decls:
                        i = decls[k]
                        z3consts.write('%s = %s\n' % (k, i))
                    z3consts.write('\n')
                    mode = SEARCHING
                elif len(words) <= 2:
                    assert False, "Invalid %s, line: %s" % (api_file, linenum)
                else:
                    if words[2] != '':
                        if len(words[2]) > 1 and words[2][1] == 'x':
                            idx = int(words[2], 16)
                        else:
                            idx = int(words[2])
                    decls[words[1]] = idx
                    idx = idx + 1
            linenum = linenum + 1
        api.close()
    z3consts.close()
    return z3consts_output_path

###############################################################################
# Functions for generating a "module definition file" for MSVC
###############################################################################

def mk_def_file_internal(defname, dll_name, export_header_files):
    """
      Writes to a module definition file to a file named ``defname``.

      ``dll_name`` is the name of the dll (without the ``.dll`` suffix).
      ``export_header_file`` is a list of header files to scan for symbols
      to include in the module definition file.
    """
    assert isinstance(export_header_files, list)
    pat1 = re.compile(".*Z3_API.*")
    fout = open(defname, 'w')
    fout.write('LIBRARY "%s"\nEXPORTS\n' % dll_name)
    num = 1
    for export_header_file in export_header_files:
        api = open(export_header_file, 'r')
        for line in api:
            m = pat1.match(line)
            if m:
                words = re.split('\W+', line)
                i = 0
                for w in words:
                    if w == 'Z3_API':
                        f = words[i+1]
                        fout.write('\t%s @%s\n' % (f, num))
                    i = i + 1
                num = num + 1
        api.close()
    fout.close()
