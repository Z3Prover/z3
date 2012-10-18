############################################
# Copyright (c) 2012 Microsoft Corporation
# 
# Scripts for generate API bindings and definitions
#
# Author: Leonardo de Moura (leonardo)
############################################
import re
import sys
import os
from sets import Set

API_FILES = []

def add_api_file(dir, file):
    API_FILES.append("%s%s%s" % (dir, os.sep, file))

add_api_file('lib', 'z3_api.h')

# Extract enumeration types from z3_api.h, and add .Net definitions
def mk_z3consts_donet():
    blank_pat      = re.compile("^ *$")
    comment_pat    = re.compile("^ *//.*$")
    typedef_pat    = re.compile("typedef enum *")
    typedef2_pat   = re.compile("typedef enum { *")
    openbrace_pat  = re.compile("{ *")
    closebrace_pat = re.compile("}.*;")

    DeprecatedEnums = { 'Z3_search_failure' }
    z3consts  = open('Microsoft.Z3%sEnumerations.cs' % os.sep, 'w')
    z3consts.write('// Automatically generated file, generator: update_api.py\n\n')
    z3consts.write('using System;\n\n'
                   '#pragma warning disable 1591\n\n'
                   'namespace Microsoft.Z3\n'
                   '{\n');

    for api_file in API_FILES:
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
                    if name not in DeprecatedEnums:
                        z3consts.write('  /// <summary>%s</summary>\n' % name)
                        z3consts.write('  public enum %s {\n' % name)
                        z3consts.write
                        for k, i in decls.iteritems():
                            z3consts.write('  %s = %s,\n' % (k, i))
                        z3consts.write('  }\n\n')
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
    z3consts.write('}\n');


# Extract enumeration types from z3_api.h, and add python definitions.
def mk_z3consts_py():
    blank_pat      = re.compile("^ *$")
    comment_pat    = re.compile("^ *//.*$")
    typedef_pat    = re.compile("typedef enum *")
    typedef2_pat   = re.compile("typedef enum { *")
    openbrace_pat  = re.compile("{ *")
    closebrace_pat = re.compile("}.*;")

    z3consts  = open('python%sz3consts.py' % (os.sep), 'w')
    z3consts.write('# Automatically generated file, generator: update_api.py\n\n')

    for api_file in API_FILES:
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
                    for k, i in decls.iteritems():
                        z3consts.write('%s = %s\n' % (k, i))
                    z3consts.write('\n')
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

# Extract tactic and probe definitions from lib\install_tactics.cpp, and
# Add python function definitions for them.
def mk_z3tactics_py():
    tactic_pat  = re.compile("^[ \t]*ADD_TACTIC_CMD")
    probe_pat   = re.compile("^[ \t]*ADD_PROBE")

    cppfile = open('lib%sinstall_tactics.cpp' % os.sep, 'r')
    z3tactics  = open('python%sz3tactics.py' % os.sep, 'w')

    z3tactics.write('# Automatically generated file, generator: update_api.py\n')
    z3tactics.write('import z3core\n')
    z3tactics.write('import z3\n\n')

    for line in cppfile:
        m1 = tactic_pat.match(line)
        m2 = probe_pat.match(line)
        if m1:
            words     = re.split('[^\-a-zA-Z0-9_]+', line)
            tactic    = words[2]
            py_tactic = tactic.replace('-', '_')
            z3tactics.write('def %s_tactic(ctx=None):\n' % py_tactic)
            z3tactics.write('  ctx = z3._get_ctx(ctx)\n')
            z3tactics.write('  return z3.Tactic(z3core.Z3_mk_tactic(ctx.ref(), \'%s\'), ctx)\n\n' % tactic)
        elif m2:
            words = re.split('[^\-a-zA-Z0-9_]+', line)
            probe     = words[2]
            py_probe  = probe.replace('-', '_')
            z3tactics.write('def %s_probe(ctx=None):\n' % py_probe)
            z3tactics.write('  ctx = z3._get_ctx(ctx)\n')
            z3tactics.write('  return z3.Probe(z3core.Z3_mk_probe(ctx.ref(), \'%s\'), ctx)\n\n' % probe)

# Create .def files for DLL generation
def mk_dll_defs():
    pat1 = re.compile(".*Z3_API.*")
    z3def = open('dll%sz3.def' % os.sep, 'w')
    z3dbgdef = open('dll%sz3_dbg.def' % os.sep, 'w')
    z3def.write('LIBRARY "Z3"\nEXPORTS\n')
    z3dbgdef.write('LIBRARY "Z3_DBG"\nEXPORTS\n')
    for api_file in API_FILES:
        api = open(api_file, 'r')
        num = 1
        for line in api:
            m = pat1.match(line)
            if m:
                words = re.split('\W+', line)
                i = 0
                for w in words:
                    if w == 'Z3_API':
                        f = words[i+1]
                        z3def.write('\t%s @%s\n' % (f, num))
                        z3dbgdef.write('\t%s @%s\n' % (f, num))
                    i = i + 1
                num = num + 1

#
# Generate logging support and bindings
#

log_h   = open('lib%sapi_log_macros.h' % os.sep, 'w')
log_c   = open('lib%sapi_log_macros.cpp' % os.sep, 'w')
exe_c   = open('lib%sapi_commands.cpp' % os.sep, 'w')
core_py = open('python%sz3core.py' % os.sep, 'w')
dotnet_fileout = 'Microsoft.Z3%sNative.cs' % os.sep
##
log_h.write('// Automatically generated file, generator: update_api.py\n')
log_h.write('#include\"z3.h\"\n')
##
log_c.write('// Automatically generated file, generator: update_api.py\n')
log_c.write('#include<iostream>\n')
log_c.write('#include\"z3.h\"\n')
log_c.write('#include\"api_log_macros.h\"\n')
log_c.write('#include\"z3_logger.h\"\n')
##
exe_c.write('// Automatically generated file, generator: update_api.py\n')
exe_c.write('#include\"z3.h\"\n')
exe_c.write('#include\"z3_replayer.h\"\n')
##
log_h.write('extern std::ostream * g_z3_log;\n')
log_h.write('extern bool           g_z3_log_enabled;\n')
log_h.write('class z3_log_ctx { bool m_prev; public: z3_log_ctx():m_prev(g_z3_log_enabled) { g_z3_log_enabled = false; } ~z3_log_ctx() { g_z3_log_enabled = m_prev; } bool enabled() const { return m_prev; } };\n')
log_h.write('inline void SetR(void * obj) { *g_z3_log << "= " << obj << "\\n"; }\ninline void SetO(void * obj, unsigned pos) { *g_z3_log << "* " << obj << " " << pos << "\\n"; } \ninline void SetAO(void * obj, unsigned pos, unsigned idx) { *g_z3_log << "@ " << obj << " " << pos << " " << idx << "\\n"; }\n')
log_h.write('#define RETURN_Z3(Z3RES) if (_LOG_CTX.enabled()) { SetR(Z3RES); } return Z3RES\n')
log_h.write('void _Z3_append_log(char const * msg);\n')
##
exe_c.write('void Z3_replacer_error_handler(Z3_context ctx, Z3_error_code c) { printf("[REPLAYER ERROR HANDLER]: %s\\n", Z3_get_error_msg_ex(ctx, c)); }\n')
##
core_py.write('# Automatically generated file, generator: update_api.py\n')
core_py.write('import sys, os\n')
core_py.write('import ctypes\n')
core_py.write('from z3types import *\n')
core_py.write('from z3consts import *\n')
core_py.write("""
def _find_lib():
  _dir = os.path.dirname(os.path.abspath(__file__))
  libs = ['z3.dll', 'libz3.so', 'libz3.dylib']
  if sys.maxsize > 2**32:
    locs = [_dir, '%s%s..%sx64%sexternal' % (_dir, os.sep, os.sep, os.sep), '%s%s..%sbin%sexternal' % (_dir, os.sep, os.sep, os.sep)]
  else:
    locs = [_dir, '%s%s..%sexternal' % (_dir, os.sep, os.sep), '%s%s..%sbin%sexternal' % (_dir, os.sep, os.sep, os.sep)]
  for loc in locs:
    for lib in libs:
      f = '%s%s%s' % (loc, os.sep, lib)
      if os.path.exists(f):
        return f
  return None

_lib = None
def lib():
  if _lib == None:
    l = _find_lib()
    if l == None:
      raise Z3Exception("init(Z3_LIBRARY_PATH) must be invoked before using Z3-python")
    init(l)
    assert _lib != None
  return _lib

def init(PATH):
  global _lib
  _lib = ctypes.CDLL(PATH)
""")

IN          = 0
OUT         = 1
INOUT       = 2
IN_ARRAY    = 3
OUT_ARRAY   = 4
INOUT_ARRAY = 5

# Primitive Types
VOID       = 0
VOID_PTR   = 1
INT        = 2
UINT       = 3
INT64      = 4
UINT64     = 5
STRING     = 6
STRING_PTR = 7
BOOL       = 8
SYMBOL     = 9
PRINT_MODE = 10
ERROR_CODE = 11
DOUBLE     = 12

FIRST_OBJ_ID = 100

def is_obj(ty):
    return ty >= FIRST_OBJ_ID

Type2Str = { VOID : 'void', VOID_PTR : 'void*', INT : 'int', UINT : 'unsigned', INT64 : '__int64', UINT64 : '__uint64', DOUBLE : 'double',
             STRING : 'Z3_string', STRING_PTR : 'Z3_string_ptr', BOOL : 'Z3_bool', SYMBOL : 'Z3_symbol',
             PRINT_MODE : 'Z3_ast_print_mode', ERROR_CODE : 'Z3_error_code',
             }

Type2PyStr = { VOID_PTR : 'ctypes.c_void_p', INT : 'ctypes.c_int', UINT : 'ctypes.c_uint', INT64 : 'ctypes.c_longlong',
               UINT64 : 'ctypes.c_ulonglong', DOUBLE : 'ctypes.c_double',
               STRING : 'ctypes.c_char_p', STRING_PTR : 'ctypes.POINTER(ctypes.c_char_p)', BOOL : 'ctypes.c_bool', SYMBOL : 'Symbol',
               PRINT_MODE : 'ctypes.c_uint', ERROR_CODE : 'ctypes.c_uint', 
               }

# Mapping to .NET types
Type2Dotnet = { VOID : 'void', VOID_PTR : 'IntPtr', INT : 'int', UINT : 'uint', INT64 : 'Int64', UINT64 : 'UInt64', DOUBLE : 'double',
                STRING : 'string', STRING_PTR : 'byte**', BOOL : 'int', SYMBOL : 'IntPtr',
                PRINT_MODE : 'uint', ERROR_CODE : 'uint' }

next_type_id = FIRST_OBJ_ID

def def_Type(var, c_type, py_type):
    global next_type_id
    exec ('%s = %s' % (var, next_type_id)) in globals()
    Type2Str[next_type_id]   = c_type
    Type2PyStr[next_type_id] = py_type
    next_type_id    = next_type_id + 1

def def_Types():
    pat1 = re.compile(" *def_Type.*")
    for api_file in API_FILES:
        api = open(api_file, 'r')
        for line in api:
            m = pat1.match(line)
            if m:
                print line.strip()
                eval(line)
    for k, v in Type2Str.iteritems():
        if is_obj(k):
            Type2Dotnet[k] = v

def type2str(ty):
    global Type2Str
    return Type2Str[ty]

def type2pystr(ty):
    global Type2PyStr
    return Type2PyStr[ty]

def type2dotnet(ty):
    global Type2Dotnet
    return Type2Dotnet[ty]

def _in(ty):
    return (IN, ty);

def _in_array(sz, ty):
    return (IN_ARRAY, ty, sz);

def _out(ty):
    return (OUT, ty);

def _out_array(sz, ty):
    return (OUT_ARRAY, ty, sz, sz);

# cap contains the position of the argument that stores the capacity of the array
# sz  contains the position of the output argument that stores the (real) size of the array
def _out_array2(cap, sz, ty):
    return (OUT_ARRAY, ty, cap, sz)

def _inout_array(sz, ty):
    return (INOUT_ARRAY, ty, sz, sz);

def param_kind(p):
    return p[0]

def param_type(p):
    return p[1]

def param_array_capacity_pos(p):
    return p[2]

def param_array_size_pos(p):
    return p[3]

def param2str(p):
    if param_kind(p) == IN_ARRAY:
        return "%s const *" % type2str(param_type(p))
    elif param_kind(p) == OUT_ARRAY or param_kind(p) == IN_ARRAY or param_kind(p) == INOUT_ARRAY:
        return "%s*" % type2str(param_type(p))
    elif param_kind(p) == OUT:
        return "%s*" % type2str(param_type(p))
    else:
        return type2str(param_type(p))


def param2dotnet(p):
    k = param_kind(p)
    if k == OUT:
        if param_type(p) == STRING:
            return "out IntPtr"
        else:
            return "[In, Out] ref %s" % type2dotnet(param_type(p))
    if k == IN_ARRAY:
        return "[In] %s[]" % type2dotnet(param_type(p))
    if k == INOUT_ARRAY:
        return "[In, Out] %s[]" % type2dotnet(param_type(p))
    if k == OUT_ARRAY:
        return "[Out] %s[]" % type2dotnet(param_type(p))
    else:
        return type2dotnet(param_type(p))

def param2pystr(p):
    if param_kind(p) == IN_ARRAY or param_kind(p) == OUT_ARRAY or param_kind(p) == IN_ARRAY or param_kind(p) == INOUT_ARRAY or param_kind(p) == OUT:
        return "ctypes.POINTER(%s)" % type2pystr(param_type(p))
    else:
        return type2pystr(param_type(p))

# Save name, result, params to generate wrapper
_API2PY = []

def mk_py_binding(name, result, params):
    global core_py
    global _API2PY
    _API2PY.append((name, result, params))
    if result != VOID:
        core_py.write("  _lib.%s.restype = %s\n" % (name, type2pystr(result)))
    core_py.write("  _lib.%s.argtypes = [" % name)
    first = True
    for p in params:
        if first:
            first = False
        else:
            core_py.write(", ")
        core_py.write(param2pystr(p))
    core_py.write("]\n")

def extra_API(name, result, params):
    mk_py_binding(name, result, params)
    reg_dotnet(name, result, params)

def display_args(num):
    for i in range(num):
        if i > 0:
            core_py.write(", ")
        core_py.write("a%s" % i)

def mk_py_wrappers():
    core_py.write("\n")
    for sig in _API2PY:
        name   = sig[0]
        result = sig[1]
        params = sig[2]
        num    = len(params)
        core_py.write("def %s(" % name)
        display_args(num)
        core_py.write("):\n")
        if result != VOID:
            core_py.write("  r = lib().%s(" % name)
        else:
            core_py.write("  lib().%s(" % name)
        display_args(num)
        core_py.write(")\n")
        if len(params) > 0 and param_type(params[0]) == CONTEXT:
            core_py.write("  err = lib().Z3_get_error_code(a0)\n")
            core_py.write("  if err != Z3_OK:\n")
            core_py.write("    raise Z3Exception(lib().Z3_get_error_msg_ex(a0, err))\n")
        if result != VOID:
            core_py.write("  return r\n")
        core_py.write("\n")


## .NET API native interface
_dotnet_decls = []
def reg_dotnet(name, result, params):
    global _dotnet_decls
    _dotnet_decls.append((name, result, params))

def mk_dotnet():
    global Type2Str
    global dotnet_fileout
    dotnet = open(dotnet_fileout, 'w')
    dotnet.write('// Automatically generated file, generator: api.py\n')
    dotnet.write('using System;\n')
    dotnet.write('using System.Collections.Generic;\n')
    dotnet.write('using System.Text;\n')
    dotnet.write('using System.Runtime.InteropServices;\n\n')
    dotnet.write('#pragma warning disable 1591\n\n');
    dotnet.write('namespace Microsoft.Z3\n')
    dotnet.write('{\n')
    for k, v in Type2Str.iteritems():
        if is_obj(k):
            dotnet.write('    using %s = System.IntPtr;\n' % v)
    dotnet.write('\n');
    dotnet.write('    public class Native\n')
    dotnet.write('    {\n\n')
    dotnet.write('        [UnmanagedFunctionPointer(CallingConvention.Cdecl)]\n')
    dotnet.write('        public delegate void Z3_error_handler(Z3_context c, Z3_error_code e);\n\n')
    dotnet.write('        public unsafe class LIB\n')
    dotnet.write('        {\n')
    dotnet.write('            #if DEBUG\n'
                 '            const string Z3_DLL_NAME = \"z3_dbg.dll\";\n'
                 '            #else\n'
                 '            const string Z3_DLL_NAME = \"z3.dll\";\n'
                 '            #endif\n\n');
    dotnet.write('            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]\n')
    dotnet.write('            public extern static void Z3_set_error_handler(Z3_context a0, Z3_error_handler a1);\n\n')
    for name, result, params in _dotnet_decls:
        dotnet.write('            [DllImport(Z3_DLL_NAME, CallingConvention = CallingConvention.Cdecl, CharSet = CharSet.Ansi)]\n')
        dotnet.write('            ')
        if result == STRING:
            dotnet.write('public extern static IntPtr %s(' % (name))
        else:
            dotnet.write('public extern static %s %s(' % (type2dotnet(result), name))
        first = True
        i = 0;
        for param in params:
            if first:
                first = False
            else:
                dotnet.write(', ')
            dotnet.write('%s a%d' % (param2dotnet(param), i))
            i = i + 1
        dotnet.write(');\n\n')
    dotnet.write('        }\n')


DotnetUnwrapped = { 'Z3_del_context' }

def mk_dotnet_wrappers():
    global Type2Str
    global dotnet_fileout
    dotnet = open(dotnet_fileout, 'a')
    dotnet.write("\n")
    dotnet.write("        public static void Z3_set_error_handler(Z3_context a0, Z3_error_handler a1) {\n")
    dotnet.write("            LIB.Z3_set_error_handler(a0, a1);\n")
    dotnet.write("            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);\n")
    dotnet.write("            if (err != Z3_error_code.Z3_OK)\n")
    dotnet.write("                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));\n")
    dotnet.write("        }\n\n")
    for name, result, params in _dotnet_decls:
        if result == STRING:
            dotnet.write('        public static string %s(' % (name))
        else:
            dotnet.write('        public static %s %s(' % (type2dotnet(result), name))
        first = True
        i = 0;
        for param in params:
            if first:
                first = False
            else:
                dotnet.write(', ')
            dotnet.write('%s a%d' % (param2dotnet(param), i))
            i = i + 1
        dotnet.write(') {\n')
        dotnet.write('            ')
        if result == STRING:
            dotnet.write('IntPtr r = ');
        elif result != VOID:
            dotnet.write('%s r = ' % type2dotnet(result));
        dotnet.write('LIB.%s(' % (name))
        first = True
        i = 0
        for param in params:
            if first:
                first = False
            else:
                dotnet.write(', ')
            if param_kind(param) == OUT:
                if param_type(param) == STRING:
                    dotnet.write('out ');
                else:
                    dotnet.write('ref ')
            dotnet.write('a%d' % i)
            i = i + 1
        dotnet.write(');\n');
        if name not in DotnetUnwrapped:
            if len(params) > 0 and param_type(params[0]) == CONTEXT:
                dotnet.write("            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);\n")
                dotnet.write("            if (err != Z3_error_code.Z3_OK)\n")
                dotnet.write("                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg_ex(a0, (uint)err)));\n")
        if result == STRING:
            dotnet.write("            return Marshal.PtrToStringAnsi(r);\n")
        elif result != VOID:
            dotnet.write("            return r;\n")
        dotnet.write("        }\n\n")
    dotnet.write("    }\n\n")
    dotnet.write("}\n\n")

def mk_log_header(file, name, params):
    file.write("void log_%s(" % name)
    i = 0
    for p in params:
        if i > 0:
            file.write(", ");
	file.write("%s a%s" % (param2str(p), i))
        i = i + 1
    file.write(")");

def log_param(p):
    kind = param_kind(p)
    ty   = param_type(p)
    return is_obj(ty) and (kind == OUT or kind == INOUT or kind == OUT_ARRAY or kind == INOUT_ARRAY)

def log_result(result, params):
    for p in params:
        if log_param(p):
            return True
    return False

def mk_log_macro(file, name, params):
    file.write("#define LOG_%s(" % name)
    i = 0
    for p in params:
        if i > 0:
            file.write(", ")
        file.write("_ARG%s" % i)
        i = i + 1
    file.write(") z3_log_ctx _LOG_CTX; ")
    auxs = Set([])
    i = 0
    for p in params:
        if log_param(p):
            kind = param_kind(p)
            if kind == OUT_ARRAY or kind == INOUT_ARRAY:
                cap = param_array_capacity_pos(p)
                if cap not in auxs:
                    auxs.add(cap)
                    file.write("unsigned Z3ARG%s; " % cap)
                sz  = param_array_size_pos(p)
                if sz not in auxs:
                    auxs.add(sz)
                    file.write("unsigned * Z3ARG%s; " % sz)
            file.write("%s Z3ARG%s; " % (param2str(p), i))
        i = i + 1
    file.write("if (_LOG_CTX.enabled()) { log_%s(" % name)
    i = 0
    for p in params:
        if (i > 0):
            file.write(', ')
        file.write("_ARG%s" %i)
        i = i + 1
    file.write("); ")
    auxs = Set([])
    i = 0
    for p in params:
        if log_param(p):
            kind = param_kind(p)
            if kind == OUT_ARRAY or kind == INOUT_ARRAY:
                cap = param_array_capacity_pos(p)
                if cap not in auxs:
                    auxs.add(cap)
                    file.write("Z3ARG%s = _ARG%s; " % (cap, cap))
                sz = param_array_size_pos(p)
                if sz not in auxs:
                    auxs.add(sz)
                    file.write("Z3ARG%s = _ARG%s; " % (sz, sz))
            file.write("Z3ARG%s = _ARG%s; " % (i, i))
        i = i + 1
    file.write("}\n")

def mk_log_result_macro(file, name, result, params):
    file.write("#define RETURN_%s" % name)
    if is_obj(result):
        file.write("(Z3RES)")
    file.write(" ")
    file.write("if (_LOG_CTX.enabled()) { ")
    if is_obj(result):
        file.write("SetR(Z3RES); ")
    i = 0
    for p in params:
        if log_param(p):
            kind = param_kind(p)
            if kind == OUT_ARRAY or kind == INOUT_ARRAY:
                cap = param_array_capacity_pos(p)
                sz  = param_array_size_pos(p)
                if cap == sz:
                    file.write("for (unsigned i = 0; i < Z3ARG%s; i++) { SetAO(Z3ARG%s[i], %s, i); } " % (sz, i, i))
                else:
                    file.write("for (unsigned i = 0; Z3ARG%s && i < *Z3ARG%s; i++) { SetAO(Z3ARG%s[i], %s, i); } " % (sz, sz, i, i))
            if kind == OUT or kind == INOUT:
                file.write("SetO((Z3ARG%s == 0 ? 0 : *Z3ARG%s), %s); " % (i, i, i))
        i = i + 1
    file.write("} ")
    if is_obj(result):
        file.write("return Z3RES\n")
    else:
        file.write("return\n")

def mk_exec_header(file, name):
    file.write("void exec_%s(z3_replayer & in)" % name)

def error(msg):
    sys.stderr.write(msg)
    exit(-1)

next_id = 0
API2Id = {}

def def_API(name, result, params):
    global API2Id, next_id
    global log_h, log_c
    print 'def_API(%s)' % name
    # print "generating ", name
    mk_py_binding(name, result, params)
    reg_dotnet(name, result, params)
    API2Id[next_id] = name
    mk_log_header(log_h, name, params)
    log_h.write(';\n')
    mk_log_header(log_c, name, params)
    log_c.write(' {\n  R();\n')
    mk_exec_header(exe_c, name)
    exe_c.write(' {\n')
    # Create Log function & Function call
    i   = 0
    exe_c.write("  ")
    if is_obj(result):
        exe_c.write("%s result = " % type2str(result))
    exe_c.write("%s(\n    " % name)
    for p in params:
        kind = param_kind(p)
        ty   = param_type(p)
        if (i > 0):
            exe_c.write(",\n    ")
        if kind == IN:
            if is_obj(ty):
                log_c.write("  P(a%s);\n" % i)
                exe_c.write("reinterpret_cast<%s>(in.get_obj(%s))" % (param2str(p), i))
            elif ty == STRING:
                log_c.write("  S(a%s);\n" % i)
                exe_c.write("in.get_str(%s)" % i)
            elif ty == SYMBOL:
                log_c.write("  Sy(a%s);\n" % i)
                exe_c.write("in.get_symbol(%s)" % i)
            elif ty == UINT:
                log_c.write("  U(a%s);\n" % i)
                exe_c.write("in.get_uint(%s)" % i)
            elif ty == UINT64:
                log_c.write("  U(a%s);\n" % i)
                exe_c.write("in.get_uint64(%s)" % i)
            elif ty == INT:
                log_c.write("  I(a%s);\n" % i)
                exe_c.write("in.get_int(%s)" % i)
            elif ty == INT64:
                log_c.write("  I(a%s);\n" % i)
                exe_c.write("in.get_int64(%s)" % i)
            elif ty == DOUBLE:
                log_c.write("  D(a%s);\n" % i)
                exe_c.write("in.get_double(%s)" % i)
            elif ty == BOOL:
                log_c.write("  I(a%s);\n" % i)
                exe_c.write("in.get_bool(%s)" % i)
            elif ty == PRINT_MODE or ty == ERROR_CODE:
                log_c.write("  U(static_cast<unsigned>(a%s));\n" % i);
                exe_c.write("static_cast<%s>(in.get_uint(%s))" % (type2str(ty), i))
            else:
                error("unsupported parameter for %s, %s" % (name, p))
        elif kind == INOUT:
            error("unsupported parameter for %s, %s" % (name, p))
        elif kind == OUT:
            if is_obj(ty):
                log_c.write("  P(0);\n")
                exe_c.write("reinterpret_cast<%s>(in.get_obj_addr(%s))" % (param2str(p), i))
            elif ty == STRING:
                log_c.write("  S(\"\");\n")
                exe_c.write("in.get_str_addr(%s)" % i)
            elif ty == UINT:
                log_c.write("  U(0);\n")
                exe_c.write("in.get_uint_addr(%s)" % i)
            elif ty == UINT64:
                log_c.write("  U(0);\n")
                exe_c.write("in.get_uint64_addr(%s)" % i)
            elif ty == INT:
                log_c.write("  I(0);\n")
                exe_c.write("in.get_int_addr(%s)" % i)
            elif ty == INT64:
                log_c.write("  I(0);\n")
                exe_c.write("in.get_int64_addr(%s)" % i)
            else:
                error("unsupported parameter for %s, %s" % (name, p))
        elif kind == IN_ARRAY or kind == INOUT_ARRAY:
            sz   = param_array_capacity_pos(p)
            log_c.write("  for (unsigned i = 0; i < a%s; i++) { " % sz)
            if is_obj(ty):
                log_c.write("P(a%s[i]);" % i)
                log_c.write(" }\n")
                log_c.write("  Ap(a%s);\n" % sz)
                exe_c.write("reinterpret_cast<%s*>(in.get_obj_array(%s))" % (type2str(ty), i))
            elif ty == SYMBOL:
                log_c.write("Sy(a%s[i]);" % i)
                log_c.write(" }\n")
                log_c.write("  Asy(a%s);\n" % sz)
                exe_c.write("in.get_symbol_array(%s)" % i)
            elif ty == UINT:
                log_c.write("U(a%s[i]);" % i)
                log_c.write(" }\n")
                log_c.write("  Au(a%s);\n" % sz)
                exe_c.write("in.get_uint_array(%s)" % i)
            else:
                error ("unsupported parameter for %s, %s" % (name, p))
        elif kind == OUT_ARRAY:
            sz   = param_array_capacity_pos(p)
            log_c.write("  for (unsigned i = 0; i < a%s; i++) { " % sz)
            if is_obj(ty):
                log_c.write("P(0);")
                log_c.write(" }\n")
                log_c.write("  Ap(a%s);\n" % sz)
                exe_c.write("reinterpret_cast<%s*>(in.get_obj_array(%s))" % (type2str(ty), i))
            elif ty == UINT:
                log_c.write("U(0);")
                log_c.write(" }\n")
                log_c.write("  Au(a%s);\n" % sz)
                exe_c.write("in.get_uint_array(%s)" % i)
            else:
                error ("unsupported parameter for %s, %s" % (name, p))
        else:
            error ("unsupported parameter for %s, %s" % (name, p))
        i = i + 1
    log_c.write("  C(%s);\n" % next_id)
    exe_c.write(");\n")
    if is_obj(result):
        exe_c.write("  in.store_result(result);\n")
        if name == 'Z3_mk_context' or name == 'Z3_mk_context_rc':
            exe_c.write("  Z3_set_error_handler(result, Z3_replacer_error_handler);")
    log_c.write('}\n')
    exe_c.write('}\n')
    mk_log_macro(log_h, name, params)
    if log_result(result, params):
        mk_log_result_macro(log_h, name, result, params)
    next_id = next_id + 1

def mk_bindings():
    exe_c.write("void register_z3_replayer_cmds(z3_replayer & in) {\n")
    for key, val in API2Id.items():
        exe_c.write("  in.register_cmd(%s, exec_%s);\n" % (key, val))
    exe_c.write("}\n")

# Collect API(...) commands from
def def_APIs():
    pat1 = re.compile(" *def_API.*")
    for api_file in API_FILES:
        api = open(api_file, 'r')
        for line in api:
            m = pat1.match(line)
            if m:
                eval(line)

mk_z3consts_donet()
mk_z3consts_py()
mk_z3tactics_py()
mk_dll_defs()
def_Types()
def_APIs()
mk_bindings()
mk_py_wrappers()
mk_dotnet()
mk_dotnet_wrappers()

