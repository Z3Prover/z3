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

###############################################################################
# Functions for generating ``gparams_register_modules.cpp``
###############################################################################
def mk_gparams_register_modules_internal(component_src_dirs, path):
    """
        Generate a ``gparams_register_modules.cpp`` file in the directory ``path``.
        Returns the path to the generated file.

        This file implements the procedure

        ```
        void gparams_register_modules()
        ```

        This procedure is invoked by gparams::init()
    """
    assert isinstance(component_src_dirs, list)
    assert check_dir_exists(path)
    cmds = []
    mod_cmds = []
    mod_descrs = []
    fullname = os.path.join(path, 'gparams_register_modules.cpp')
    fout  = open(fullname, 'w')
    fout.write('// Automatically generated file.\n')
    fout.write('#include"gparams.h"\n')
    reg_pat = re.compile('[ \t]*REG_PARAMS\(\'([^\']*)\'\)')
    reg_mod_pat = re.compile('[ \t]*REG_MODULE_PARAMS\(\'([^\']*)\', *\'([^\']*)\'\)')
    reg_mod_descr_pat = re.compile('[ \t]*REG_MODULE_DESCRIPTION\(\'([^\']*)\', *\'([^\']*)\'\)')
    for component_src_dir in component_src_dirs:
        h_files = filter(lambda f: f.endswith('.h') or f.endswith('.hpp'), os.listdir(component_src_dir))
        for h_file in h_files:
            added_include = False
            fin = open(os.path.join(component_src_dir, h_file), 'r')
            for line in fin:
                m = reg_pat.match(line)
                if m:
                    if not added_include:
                        added_include = True
                        fout.write('#include"%s"\n' % h_file)
                    cmds.append((m.group(1)))
                m = reg_mod_pat.match(line)
                if m:
                    if not added_include:
                        added_include = True
                        fout.write('#include"%s"\n' % h_file)
                    mod_cmds.append((m.group(1), m.group(2)))
                m = reg_mod_descr_pat.match(line)
                if m:
                    mod_descrs.append((m.group(1), m.group(2)))
            fin.close()
    fout.write('void gparams_register_modules() {\n')
    for code in cmds:
        fout.write('{ param_descrs d; %s(d); gparams::register_global(d); }\n' % code)
    for (mod, code) in mod_cmds:
        fout.write('{ param_descrs * d = alloc(param_descrs); %s(*d); gparams::register_module("%s", d); }\n' % (code, mod))
    for (mod, descr) in mod_descrs:
        fout.write('gparams::register_module_descr("%s", "%s");\n' % (mod, descr))
    fout.write('}\n')
    fout.close()
    return fullname

###############################################################################
# Functions/data structures for generating ``install_tactics.cpp``
###############################################################################

# FIXME: Remove use of global data structures
ADD_TACTIC_DATA=[]
ADD_PROBE_DATA=[]

def ADD_TACTIC(name, descr, cmd):
    global ADD_TACTIC_DATA
    ADD_TACTIC_DATA.append((name, descr, cmd))

def ADD_PROBE(name, descr, cmd):
    global ADD_PROBE_DATA
    ADD_PROBE_DATA.append((name, descr, cmd))


def mk_install_tactic_cpp_internal(component_src_dirs, path):
    """
        Generate a ``install_tactics.cpp`` file in the directory ``path``.
        Returns the path the generated file.

        This file implements the procedure

        ```
        void install_tactics(tactic_manager & ctx)
        ```

        It installs all tactics found in the given component directories
        ``component_src_dirs`` The procedure looks for ``ADD_TACTIC`` commands
        in the ``.h``  and ``.hpp`` files of these components.
    """
    global ADD_TACTIC_DATA, ADD_PROBE_DATA
    ADD_TACTIC_DATA = []
    ADD_PROBE_DATA = []
    assert isinstance(component_src_dirs, list)
    assert check_dir_exists(path)
    fullname = os.path.join(path, 'install_tactic.cpp')
    fout  = open(fullname, 'w')
    fout.write('// Automatically generated file.\n')
    fout.write('#include"tactic.h"\n')
    fout.write('#include"tactic_cmds.h"\n')
    fout.write('#include"cmd_context.h"\n')
    tactic_pat   = re.compile('[ \t]*ADD_TACTIC\(.*\)')
    probe_pat    = re.compile('[ \t]*ADD_PROBE\(.*\)')
    for component_src_dir in component_src_dirs:
        h_files = filter(lambda f: f.endswith('.h') or f.endswith('.hpp'), os.listdir(component_src_dir))
        for h_file in h_files:
            added_include = False
            fin = open(os.path.join(component_src_dir, h_file), 'r')
            for line in fin:
                if tactic_pat.match(line):
                    if not added_include:
                        added_include = True
                        fout.write('#include"%s"\n' % h_file)
                    try:
                        exec(line.strip('\n '), globals())
                    except Exception as e:
                        _logger.error("Failed processing ADD_TACTIC command at '{}'\n{}".format(
                            fullname, line))
                        raise e
                if probe_pat.match(line):
                    if not added_include:
                        added_include = True
                        fout.write('#include"%s"\n' % h_file)
                    try:
                        exec(line.strip('\n '), globals())
                    except Exception as e:
                        _logger.error("Failed processing ADD_PROBE command at '{}'\n{}".format(
                            fullname, line))
                        raise e
            fin.close()
    # First pass will just generate the tactic factories
    idx = 0
    for data in ADD_TACTIC_DATA:
        fout.write('MK_SIMPLE_TACTIC_FACTORY(__Z3_local_factory_%s, %s);\n' % (idx, data[2]))
        idx = idx + 1
    fout.write('#define ADD_TACTIC_CMD(NAME, DESCR, FACTORY) ctx.insert(alloc(tactic_cmd, symbol(NAME), DESCR, alloc(FACTORY)))\n')
    fout.write('#define ADD_PROBE(NAME, DESCR, PROBE) ctx.insert(alloc(probe_info, symbol(NAME), DESCR, PROBE))\n')
    fout.write('void install_tactics(tactic_manager & ctx) {\n')
    idx = 0
    for data in ADD_TACTIC_DATA:
        fout.write('  ADD_TACTIC_CMD("%s", "%s", __Z3_local_factory_%s);\n' % (data[0], data[1], idx))
        idx = idx + 1
    for data in ADD_PROBE_DATA:
        fout.write('  ADD_PROBE("%s", "%s", %s);\n' % data)
    fout.write('}\n')
    fout.close()
    return fullname

###############################################################################
# Functions for generating ``mem_initializer.cpp``
###############################################################################

def mk_mem_initializer_cpp_internal(component_src_dirs, path):
    """
        Generate a ``mem_initializer.cpp`` file in the directory ``path``.
        Returns the path to the generated file.

        This file implements the procedures

        ```
        void mem_initialize()
        void mem_finalize()
        ```

       These procedures are invoked by the Z3 memory_manager
    """
    assert isinstance(component_src_dirs, list)
    assert check_dir_exists(path)
    initializer_cmds = []
    finalizer_cmds   = []
    fullname = os.path.join(path, 'mem_initializer.cpp')
    fout  = open(fullname, 'w')
    fout.write('// Automatically generated file.\n')
    initializer_pat      = re.compile('[ \t]*ADD_INITIALIZER\(\'([^\']*)\'\)')
    # ADD_INITIALIZER with priority
    initializer_prio_pat = re.compile('[ \t]*ADD_INITIALIZER\(\'([^\']*)\',[ \t]*(-?[0-9]*)\)')
    finalizer_pat        = re.compile('[ \t]*ADD_FINALIZER\(\'([^\']*)\'\)')
    for component_src_dir in component_src_dirs:
        h_files = filter(lambda f: f.endswith('.h') or f.endswith('.hpp'), os.listdir(component_src_dir))
        for h_file in h_files:
            added_include = False
            fin = open(os.path.join(component_src_dir, h_file), 'r')
            for line in fin:
                m = initializer_pat.match(line)
                if m:
                    if not added_include:
                        added_include = True
                        fout.write('#include"%s"\n' % h_file)
                    initializer_cmds.append((m.group(1), 0))
                m = initializer_prio_pat.match(line)
                if m:
                    if not added_include:
                        added_include = True
                        fout.write('#include"%s"\n' % h_file)
                    initializer_cmds.append((m.group(1), int(m.group(2))))
                m = finalizer_pat.match(line)
                if m:
                    if not added_include:
                        added_include = True
                        fout.write('#include"%s"\n' % h_file)
                    finalizer_cmds.append(m.group(1))
            fin.close()
    initializer_cmds.sort(key=lambda tup: tup[1])
    fout.write('void mem_initialize() {\n')
    for (cmd, prio) in initializer_cmds:
        fout.write(cmd)
        fout.write('\n')
    fout.write('}\n')
    fout.write('void mem_finalize() {\n')
    for cmd in finalizer_cmds:
        fout.write(cmd)
        fout.write('\n')
    fout.write('}\n')
    fout.close()
    return fullname

###############################################################################
# Functions for generating ``database.h``
###############################################################################

def mk_pat_db_internal(inputFilePath, outputFilePath):
    """
        Generate ``g_pattern_database[]`` declaration header file.
    """
    with open(inputFilePath, 'r') as fin:
        with open(outputFilePath, 'w') as fout:
            fout.write('static char const g_pattern_database[] =\n')
            for line in fin:
                fout.write('"%s\\n"\n' % line.strip('\n'))
            fout.write(';\n')
