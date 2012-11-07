############################################
# Copyright (c) 2012 Microsoft Corporation
# 
# Scripts for generating Makefiles and Visual 
# Studio project files.
#
# Author: Leonardo de Moura (leonardo)
############################################
from mk_util import *
from mk_exception import *

##########################################################
# TODO: rewrite this file without using global variables.
# This file is a big HACK.
# It started as small simple script.
# Now, it is too big, and is invoked from mk_make.py
# The communication uses 
#
##########################################################

#
# Generate logging support and bindings
#
api_dir     = get_component('api').src_dir
dotnet_dir  = get_component('dotnet').src_dir

log_h   = open('%s/api_log_macros.h' % api_dir, 'w')
log_c   = open('%s/api_log_macros.cpp' % api_dir, 'w')
exe_c   = open('%s/api_commands.cpp' % api_dir, 'w')
core_py = open('%s/z3core.py' % get_z3py_dir(), 'w')
dotnet_fileout = '%s/Native.cs' % dotnet_dir
##
log_h.write('// Automatically generated file\n')
log_h.write('#include\"z3.h\"\n')
log_h.write('#ifdef __GNUC__\n')
log_h.write('#define _Z3_UNUSED __attribute__((unused))\n')
log_h.write('#else\n')
log_h.write('#define _Z3_UNUSED\n')
log_h.write('#endif\n')

##
log_c.write('// Automatically generated file\n')
log_c.write('#include<iostream>\n')
log_c.write('#include\"z3.h\"\n')
log_c.write('#include\"api_log_macros.h\"\n')
log_c.write('#include\"z3_logger.h\"\n')
##
exe_c.write('// Automatically generated file\n')
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
core_py.write('# Automatically generated file\n')
core_py.write('import sys, os\n')
core_py.write('import ctypes\n')
core_py.write('from z3types import *\n')
core_py.write('from z3consts import *\n')
core_py.write("""
_lib = None
def lib():
  global _lib
  if _lib == None:
    _dir = os.path.dirname(os.path.abspath(__file__))
    for ext in ['dll', 'so', 'dylib']:
      try:
        init('libz3.%s' % ext)
        break
      except:
        pass
      try:
        init(os.path.join(_dir, 'libz3.%s' % ext))
        break
      except:
        pass
    if _lib == None:
        raise Z3Exception("init(Z3_LIBRARY_PATH) must be invoked before using Z3-python")
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
    dotnet.write('// Automatically generated file\n')
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
    dotnet.write('           '
                 '            const string Z3_DLL_NAME = \"libz3.dll\";\n'
                 '            \n');
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


DotnetUnwrapped = [ 'Z3_del_context' ]

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
    auxs = set()
    i = 0
    for p in params:
        if log_param(p):
            kind = param_kind(p)
            if kind == OUT_ARRAY or kind == INOUT_ARRAY:
                cap = param_array_capacity_pos(p)
                if cap not in auxs:
                    auxs.add(cap)
                    file.write("unsigned _Z3_UNUSED Z3ARG%s; " % cap)
                sz  = param_array_size_pos(p)
                if sz not in auxs:
                    auxs.add(sz)
                    file.write("unsigned * _Z3_UNUSED Z3ARG%s; " % sz)
            file.write("%s _Z3_UNUSED Z3ARG%s; " % (param2str(p), i))
        i = i + 1
    file.write("if (_LOG_CTX.enabled()) { log_%s(" % name)
    i = 0
    for p in params:
        if (i > 0):
            file.write(', ')
        file.write("_ARG%s" %i)
        i = i + 1
    file.write("); ")
    auxs = set()
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
    pat2 = re.compile(" *extra_API.*")
    for api_file in API_FILES:
        api = open(api_file, 'r')
        for line in api:
            line = line.strip('\r\n\t ')
            try:
                m = pat1.match(line)
                if m:
                    eval(line)
                m = pat2.match(line)
                if m:
                    eval(line)
            except Exception:
                raise MKException("Failed to process API definition: %s" % line)
def_Types()
def_APIs()
mk_bindings()
mk_py_wrappers()
mk_dotnet()
mk_dotnet_wrappers()

log_h.close()
log_c.close()
exe_c.close()
core_py.close()

if is_verbose():
    print "Generated '%s'" % ('%s/api_log_macros.h' % api_dir)
    print "Generated '%s'" % ('%s/api_log_macros.cpp' % api_dir)
    print "Generated '%s'" % ('%s/api_commands.cpp' % api_dir)
    print "Generated '%s'" % ('%s/z3core.py' % get_z3py_dir())
    print "Generated '%s'" % ('%s/Native.cs' % dotnet_dir)
