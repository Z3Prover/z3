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

    z3consts  = open(os.path.join(output_dir, 'z3', 'z3consts.py'), 'w')
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
                    raise ValueError("Invalid %s, line: %s" % (api_file, linenum))
            else:
                if mode != IN_ENUM:
                    raise ValueError(f"Expected IN_ENUM mode, got mode {mode} in {api_file}, line: {linenum}")
                words = re.split('[^-a-zA-Z0-9_]+', line)
                m = closebrace_pat.match(line)
                if m:
                    name = words[1]
                    z3consts.write('# enum %s\n' % name)
                    # Iterate over key-value pairs ordered by value
                    for k, v in sorted(decls.items(), key=lambda pair: pair[1]):
                        z3consts.write('%s = %s\n' % (k, v))
                    z3consts.write('\n')
                    mode = SEARCHING
                elif len(words) <= 2:
                    raise ValueError("Invalid %s, line: %s" % (api_file, linenum))
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

def mk_z3consts_dotnet_internal(api_files, output_dir):
    """
        Generate ``Enumerations.cs`` from the list of API header files
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

    DeprecatedEnums = [ 'Z3_search_failure' ]
    z3consts  = open(os.path.join(output_dir, 'Enumerations.cs'), 'w')
    z3consts_output_path = z3consts.name
    z3consts.write('// Automatically generated file\n\n')
    z3consts.write('using System;\n\n'
                   '#pragma warning disable 1591\n\n'
                   'namespace Microsoft.Z3\n'
                   '{\n')

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
                    raise ValueError("Invalid %s, line: %s" % (api_file, linenum))
            else:
                if mode != IN_ENUM:
                    raise ValueError(f"Expected IN_ENUM mode, got mode {mode} in {api_file}, line: {linenum}")
                words = re.split('[^-a-zA-Z0-9_]+', line)
                m = closebrace_pat.match(line)
                if m:
                    name = words[1]
                    if name not in DeprecatedEnums:
                        z3consts.write('  /// <summary>%s</summary>\n' % name)
                        z3consts.write('  public enum %s {\n' % name)
                        z3consts.write
                        # Iterate over key-value pairs ordered by value
                        for k, v in sorted(decls.items(), key=lambda pair: pair[1]):
                            z3consts.write('  %s = %s,\n' % (k, v))
                        z3consts.write('  }\n\n')
                    mode = SEARCHING
                elif len(words) <= 2:
                    raise ValueError("Invalid %s, line: %s" % (api_file, linenum))
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
    z3consts.write('}\n');
    z3consts.close()
    return z3consts_output_path


def mk_z3consts_java_internal(api_files, package_name, output_dir):
    """
        Generate "com.microsoft.z3.enumerations" package from the list of API
        header files in ``api_files`` and write the package directory into
        the ``output_dir`` directory

        Returns a list of the generated java source files.
    """
    blank_pat      = re.compile("^ *$")
    comment_pat    = re.compile("^ *//.*$")
    typedef_pat    = re.compile("typedef enum *")
    typedef2_pat   = re.compile("typedef enum { *")
    openbrace_pat  = re.compile("{ *")
    closebrace_pat = re.compile("}.*;")

    DeprecatedEnums = [ 'Z3_search_failure' ]
    gendir = os.path.join(output_dir, "enumerations")
    if not os.path.exists(gendir):
        os.mkdir(gendir)

    generated_enumeration_files = []
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
                    raise ValueError("Invalid %s, line: %s" % (api_file, linenum))
            else:
                if mode != IN_ENUM:
                    raise ValueError(f"Expected IN_ENUM mode, got mode {mode} in {api_file}, line: {linenum}")
                words = re.split('[^-a-zA-Z0-9_]+', line)
                m = closebrace_pat.match(line)
                if m:
                    name = words[1]
                    if name not in DeprecatedEnums:
                        efile  = open('%s.java' % os.path.join(gendir, name), 'w')
                        generated_enumeration_files.append(efile.name)
                        efile.write('/**\n *  Automatically generated file\n **/\n\n')
                        efile.write('package %s.enumerations;\n\n' % package_name)
                        efile.write('import java.util.HashMap;\n')
                        efile.write('import java.util.Map;\n')
                        efile.write('\n')

                        efile.write('/**\n')
                        efile.write(' * %s\n' % name)
                        efile.write(' **/\n')
                        efile.write('public enum %s {\n' % name)
                        efile.write
                        first = True
                        # Iterate over key-value pairs ordered by value
                        for k, v in sorted(decls.items(), key=lambda pair: pair[1]):
                            if first:
                                first = False
                            else:
                                efile.write(',\n')
                            efile.write('    %s (%s)' % (k, v))
                        efile.write(";\n")
                        efile.write('\n    private final int intValue;\n\n')
                        efile.write('    %s(int v) {\n' % name)
                        efile.write('        this.intValue = v;\n')
                        efile.write('    }\n\n')
                        efile.write('    // Cannot initialize map in constructor, so need to do it lazily.\n')
                        efile.write('    // Easiest thread-safe way is the initialization-on-demand holder pattern.\n')
                        efile.write('    private static class %s_MappingHolder {\n' % name)
                        efile.write('        private static final Map<Integer, %s> intMapping = new HashMap<>();\n' % name)
                        efile.write('        static {\n')
                        efile.write('            for (%s k : %s.values())\n' % (name, name))
                        efile.write('                intMapping.put(k.toInt(), k);\n')
                        efile.write('        }\n')
                        efile.write('    }\n\n')
                        efile.write('    public static final %s fromInt(int v) {\n' % name)
                        efile.write('        %s k = %s_MappingHolder.intMapping.get(v);\n' % (name, name))
                        efile.write('        if (k != null) return k;\n')
                        efile.write('        throw new IllegalArgumentException("Illegal value " + v + " for %s");\n' % name)
                        efile.write('    }\n\n')
                        efile.write('    public final int toInt() { return this.intValue; }\n')
                        #  efile.write(';\n  %s(int v) {}\n' % name)
                        efile.write('}\n\n')
                        efile.close()
                    mode = SEARCHING
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
    return generated_enumeration_files

# Extract enumeration types from z3_api.h, and add ML definitions
def mk_z3consts_ml_internal(api_files, output_dir):
    """
        Generate ``z3enums.ml`` from the list of API header files
        in ``api_files`` and write the output file into
        the ``output_dir`` directory

        Returns the path to the generated file.
    """
    assert os.path.isdir(output_dir)
    assert isinstance(api_files, list)
    blank_pat      = re.compile("^ *$")
    comment_pat    = re.compile("^ *//.*$")
    typedef_pat    = re.compile("typedef enum *")
    typedef2_pat   = re.compile("typedef enum { *")
    openbrace_pat  = re.compile("{ *")
    closebrace_pat = re.compile("}.*;")


    DeprecatedEnums = [ 'Z3_search_failure' ]
    if not os.path.exists(output_dir):
        os.mkdir(output_dir)

    efile  = open('%s.ml' % os.path.join(output_dir, "z3enums"), 'w')
    z3consts_output_path = efile.name
    efile.write('(* Automatically generated file *)\n\n')
    efile.write('(** The enumeration types of Z3. *)\n\n')
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
                    raise ValueError("Invalid %s, line: %s" % (api_file, linenum))
            else:
                if mode != IN_ENUM:
                    raise ValueError(f"Expected IN_ENUM mode, got mode {mode} in {api_file}, line: {linenum}")
                words = re.split('[^-a-zA-Z0-9_]+', line)
                m = closebrace_pat.match(line)
                if m:
                    name = words[1]
                    if name not in DeprecatedEnums:
                        sorted_decls = sorted(decls.items(), key=lambda pair: pair[1])
                        efile.write('(** %s *)\n' % name[3:])
                        efile.write('type %s =\n' % name[3:]) # strip Z3_
                        for k, i in sorted_decls:
                            efile.write('  | %s \n' % k[3:]) # strip Z3_
                        efile.write('\n')
                        efile.write('(** Convert %s to int*)\n' % name[3:])
                        efile.write('let int_of_%s x : int =\n' % (name[3:])) # strip Z3_
                        efile.write('  match x with\n')
                        for k, i in sorted_decls:
                            efile.write('  | %s -> %d\n' % (k[3:], i))
                        efile.write('\n')
                        efile.write('(** Convert int to %s*)\n' % name[3:])
                        efile.write('let %s_of_int x : %s =\n' % (name[3:],name[3:])) # strip Z3_
                        efile.write('  match x with\n')
                        for k, i in sorted_decls:
                            efile.write('  | %d -> %s\n' % (i, k[3:]))
                        # use Z3.Exception?
                        efile.write('  | _ -> raise (Failure "undefined enum value")\n\n')
                    mode = SEARCHING
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
    efile.close()
    return z3consts_output_path
    # efile  = open('%s.mli' % os.path.join(gendir, "z3enums"), 'w')
    # efile.write('(* Automatically generated file *)\n\n')
    # efile.write('(** The enumeration types of Z3. *)\n\n')
    # for api_file in api_files:
    #     api_file_c = ml.find_file(api_file, ml.name)
    #     api_file   = os.path.join(api_file_c.src_dir, api_file)

    #     api = open(api_file, 'r')

    #     SEARCHING  = 0
    #     FOUND_ENUM = 1
    #     IN_ENUM    = 2

    #     mode    = SEARCHING
    #     decls   = {}
    #     idx     = 0

    #     linenum = 1
    #     for line in api:
    #         m1 = blank_pat.match(line)
    #         m2 = comment_pat.match(line)
    #         if m1 or m2:
    #             # skip blank lines and comments
    #             linenum = linenum + 1
    #         elif mode == SEARCHING:
    #             m = typedef_pat.match(line)
    #             if m:
    #                 mode = FOUND_ENUM
    #             m = typedef2_pat.match(line)
    #             if m:
    #                 mode = IN_ENUM
    #                 decls = {}
    #                 idx   = 0
    #         elif mode == FOUND_ENUM:
    #             m = openbrace_pat.match(line)
    #             if m:
    #                 mode  = IN_ENUM
    #                 decls = {}
    #                 idx   = 0
    #             else:
    #                 raise ValueError("Invalid %s, line: %s" % (api_file, linenum))
    #         else:
    #             if mode != IN_ENUM:
    #                 raise ValueError(f"Expected IN_ENUM mode, got mode {mode} in {api_file}, line: {linenum}")
    #             words = re.split('[^\-a-zA-Z0-9_]+', line)
    #             m = closebrace_pat.match(line)
    #             if m:
    #                 name = words[1]
    #                 if name not in DeprecatedEnums:
    #                     efile.write('(** %s *)\n' % name[3:])
    #                     efile.write('type %s =\n' % name[3:]) # strip Z3_
    #                     for k, i in sorted(decls.items(), key=lambda pair: pair[1]):
    #                         efile.write('  | %s \n' % k[3:]) # strip Z3_
    #                     efile.write('\n')
    #                     efile.write('(** Convert %s to int*)\n' % name[3:])
    #                     efile.write('val int_of_%s : %s -> int\n' % (name[3:], name[3:])) # strip Z3_
    #                     efile.write('(** Convert int to %s*)\n' % name[3:])
    #                     efile.write('val %s_of_int : int -> %s\n' % (name[3:],name[3:])) # strip Z3_
    #                     efile.write('\n')
    #                 mode = SEARCHING
    #             else:
    #                 if words[2] != '':
    #                     if len(words[2]) > 1 and words[2][1] == 'x':
    #                         idx = int(words[2], 16)
    #                     else:
    #                         idx = int(words[2])
    #                 decls[words[1]] = idx
    #                 idx = idx + 1
    #         linenum = linenum + 1
    #     api.close()
    # efile.close()
    # if VERBOSE:
    #     print ('Generated "%s/z3enums.mli"' % ('%s' % gendir))


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
                words = re.split(r'\W+', line)
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

