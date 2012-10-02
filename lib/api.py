# Copyright (c) 2011 Microsoft Corporation
#
# Module Name:
#
#    api.py
#
# Abstract:
#
#    Generate code for logging Z3 APIs.
#    It also generate bindings for the z3_replayer interpreter.
#
#    Generated files:
#    - z3_api_log.h, z3_api_log.cpp: logging support for Z3 api.
#    - z3_api_commands.cpp: bindings for z3_replayer.
#
#  Author:
#
#    Leonardo de Moura (leonardo) 2011-09-23
import sys
import os
from sets import Set
log_h   = open('api_log_macros.h', 'w')
log_c   = open('api_log_macros.cpp', 'w')
exe_c   = open('api_commands.cpp', 'w')
core_py = open('..%spython%sz3core.py' % (os.sep, os.sep), 'w')
dotnet_fileout = '..%sMicrosoft.Z3%sNative.cs' % (os.sep, os.sep)
##
log_h.write('// Automatically generated file, generator: api.py\n')
log_h.write('#include\"z3.h\"\n')
##
log_c.write('// Automatically generated file, generator: api.py\n')
log_c.write('#include<iostream>\n')
log_c.write('#include\"z3.h\"\n')
log_c.write('#include\"api_log_macros.h\"\n')
log_c.write('#include\"z3_logger.h\"\n')
##
exe_c.write('// Automatically generated file, generator: api.py\n')
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
core_py.write('# Automatically generated file, generator: api.py\n')
core_py.write('import sys, os\n')
core_py.write('import ctypes\n')
core_py.write('from z3types import *\n')
core_py.write('from z3consts import *\n')
core_py.write("""
def _find_lib():
  _dir = os.path.dirname(os.path.abspath(__file__))
  libs = ['z3.dll', 'libz3.so', 'libz3.dylib']
  if sys.maxsize > 2**32:
     winlibdir = 'x64'
  else:
     winlibdir = 'bin'
  locs = [_dir, '%s%s..%s%s' % (_dir, os.sep, os.sep, winlibdir), '%s%s..%slib' % (_dir, os.sep, os.sep), '%s%s..%sexternal' % (_dir, os.sep, os.sep), '%s%s..%sbin%sexternal' % (_dir, os.sep, os.sep, os.sep)]
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

next_id = 0
API2Id = {}

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

CONFIG           = 100
CONTEXT          = 101
AST              = 102
APP              = 103
SORT             = 104
FUNC_DECL        = 105
PATTERN          = 106
MODEL            = 107
LITERALS         = 108
CONSTRUCTOR      = 109
CONSTRUCTOR_LIST = 110
THEORY           = 111
THEORY_DATA      = 112
SOLVER           = 113
GOAL             = 114
TACTIC           = 115
PARAMS           = 117
PROBE            = 118
STATS            = 119
AST_VECTOR       = 120
AST_MAP          = 121
APPLY_RESULT     = 122
FUNC_INTERP      = 123
FUNC_ENTRY       = 124
FIXEDPOINT       = 125
PARAM_DESCRS     = 126

def is_obj(ty):
    return ty >= 100

IN          = 0
OUT         = 1
INOUT       = 2
IN_ARRAY    = 3
OUT_ARRAY   = 4
INOUT_ARRAY = 5

Type2Str = { VOID : 'void', VOID_PTR : 'void*', INT : 'int', UINT : 'unsigned', INT64 : '__int64', UINT64 : '__uint64', DOUBLE : 'double',
             STRING : 'Z3_string', STRING_PTR : 'Z3_string_ptr', BOOL : 'Z3_bool', SYMBOL : 'Z3_symbol',
             PRINT_MODE : 'Z3_ast_print_mode', ERROR_CODE : 'Z3_error_code',
             CONFIG : 'Z3_config', CONTEXT : 'Z3_context', AST : 'Z3_ast', APP : 'Z3_app', SORT : 'Z3_sort',
             FUNC_DECL : 'Z3_func_decl', PATTERN : 'Z3_pattern', MODEL : 'Z3_model', LITERALS : 'Z3_literals',
             CONSTRUCTOR : 'Z3_constructor', CONSTRUCTOR_LIST : 'Z3_constructor_list', THEORY : 'Z3_theory',
             THEORY_DATA : 'Z3_theory_data', SOLVER : 'Z3_solver', GOAL : 'Z3_goal', TACTIC : 'Z3_tactic',
	     FIXEDPOINT : 'Z3_fixedpoint',
             PARAMS : 'Z3_params', PROBE : 'Z3_probe', STATS : 'Z3_stats', AST_VECTOR : 'Z3_ast_vector',
             AST_MAP : 'Z3_ast_map', APPLY_RESULT : 'Z3_apply_result', FUNC_INTERP : 'Z3_func_interp', FUNC_ENTRY : 'Z3_func_entry',
             PARAM_DESCRS : 'Z3_param_descrs'
             }

Type2PyStr = { VOID_PTR : 'ctypes.c_void_p', INT : 'ctypes.c_int', UINT : 'ctypes.c_uint', INT64 : 'ctypes.c_longlong',
               UINT64 : 'ctypes.c_ulonglong', DOUBLE : 'ctypes.c_double',
               STRING : 'ctypes.c_char_p', STRING_PTR : 'ctypes.POINTER(ctypes.c_char_p)', BOOL : 'ctypes.c_bool', SYMBOL : 'Symbol',
               PRINT_MODE : 'ctypes.c_uint', ERROR_CODE : 'ctypes.c_uint', CONFIG : 'Config', CONTEXT : 'ContextObj',
               AST : 'Ast', APP : 'Ast', SORT: 'Sort', FUNC_DECL : 'FuncDecl', PATTERN : 'Pattern',
               MODEL : 'Model', LITERALS : 'Literals', CONSTRUCTOR : 'Constructor', CONSTRUCTOR_LIST : 'ConstructorList',
               THEORY : 'ctypes.c_void_p', THEORY_DATA : 'ctypes.c_void_p', SOLVER : 'SolverObj', GOAL : 'GoalObj', TACTIC : 'TacticObj',
	       FIXEDPOINT : 'FixedpointObj',
               PARAMS : 'Params', PROBE : 'ProbeObj', STATS : 'StatsObj', AST_VECTOR : 'AstVectorObj', AST_MAP : 'AstMapObj',
               APPLY_RESULT : 'ApplyResultObj', FUNC_INTERP : 'FuncInterpObj', FUNC_ENTRY : 'FuncEntryObj',
               PARAM_DESCRS : 'ParamDescrs'
               }

# Mapping to .NET types
Type2Dotnet = { VOID : 'void', VOID_PTR : 'IntPtr', INT : 'int', UINT : 'uint', INT64 : 'Int64', UINT64 : 'UInt64', DOUBLE : 'double',
                STRING : 'string', STRING_PTR : 'byte**', BOOL : 'int', SYMBOL : 'IntPtr',
                PRINT_MODE : 'uint', ERROR_CODE : 'uint' }

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

def API(name, result, params):
    global API2Id, next_id
    global log_h, log_c
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

def mk_defs():
    z3_def = open('..\dll\z3.def', 'w')
    z3_dbg_def = open('..\dll\z3_dbg.def', 'w')
    z3_def.write('LIBRARY "Z3"\n')
    z3_def.write('EXPORTS\n')
    z3_dbg_def.write('LIBRARY "Z3_DBG"\n')
    z3_dbg_def.write('EXPORTS\n')
    i = 1
    for key, val in API2Id.items():
        z3_def.write("\t%s @%s\n" % (val, i))
        z3_dbg_def.write("\t%s @%s\n" % (val, i))
        i = i + 1

API('Z3_mk_config', CONFIG, ())
API('Z3_del_config', VOID, (_in(CONFIG),))
API('Z3_set_param_value', VOID, (_in(CONFIG), _in(STRING), _in(STRING)))
API('Z3_mk_context', CONTEXT, (_in(CONFIG),))
API('Z3_mk_context_rc', CONTEXT, (_in(CONFIG),))
API('Z3_set_logic', VOID, (_in(CONTEXT), _in(STRING)))
API('Z3_del_context', VOID, (_in(CONTEXT),))
API('Z3_inc_ref', VOID, (_in(CONTEXT), _in(AST)))
API('Z3_dec_ref', VOID, (_in(CONTEXT), _in(AST)))
API('Z3_toggle_warning_messages', VOID, (_in(BOOL),))
API('Z3_update_param_value', VOID, (_in(CONTEXT), _in(STRING), _in(STRING)))
API('Z3_get_param_value', BOOL, (_in(CONTEXT), _in(STRING), _out(STRING)))
API('Z3_mk_int_symbol', SYMBOL, (_in(CONTEXT), _in(INT)))
API('Z3_mk_string_symbol', SYMBOL, (_in(CONTEXT), _in(STRING)))
API('Z3_is_eq_sort', BOOL, (_in(CONTEXT), _in(SORT), _in(SORT)))
API('Z3_mk_uninterpreted_sort', SORT, (_in(CONTEXT), _in(SYMBOL)))
API('Z3_mk_bool_sort', SORT, (_in(CONTEXT), ))
API('Z3_mk_int_sort', SORT, (_in(CONTEXT), ))
API('Z3_mk_real_sort', SORT, (_in(CONTEXT), ))
API('Z3_mk_bv_sort', SORT, (_in(CONTEXT), _in(UINT)))
API('Z3_mk_array_sort', SORT, (_in(CONTEXT), _in(SORT), _in(SORT)))
API('Z3_mk_tuple_sort', SORT, (_in(CONTEXT), _in(SYMBOL), _in(UINT),
                               _in_array(2, SYMBOL),
                               _in_array(2, SORT),
                               _out(FUNC_DECL),
                               _out_array(2, FUNC_DECL)))

API('Z3_mk_enumeration_sort', SORT, (_in(CONTEXT), _in(SYMBOL), _in(UINT),
                                     _in_array(2, SYMBOL),
                                     _out_array(2, FUNC_DECL),
                                     _out_array(2, FUNC_DECL)))

API('Z3_mk_list_sort', SORT, (_in(CONTEXT), _in(SYMBOL), _in(SORT), _out(FUNC_DECL), _out(FUNC_DECL), _out(FUNC_DECL), _out(FUNC_DECL), _out(FUNC_DECL), _out(FUNC_DECL)))

API('Z3_mk_constructor', CONSTRUCTOR, (_in(CONTEXT), _in(SYMBOL), _in(SYMBOL), _in(UINT), _in_array(3, SYMBOL), _in_array(3, SORT), _in_array(3, UINT)))
API('Z3_query_constructor', VOID, (_in(CONTEXT), _in(CONSTRUCTOR), _in(UINT), _out(FUNC_DECL), _out(FUNC_DECL), _out_array(2, FUNC_DECL)))
API('Z3_del_constructor', VOID, (_in(CONTEXT), _in(CONSTRUCTOR)))
API('Z3_mk_datatype', SORT, (_in(CONTEXT), _in(SYMBOL), _in(UINT), _inout_array(2, CONSTRUCTOR)))
API('Z3_mk_constructor_list', CONSTRUCTOR_LIST, (_in(CONTEXT), _in(UINT), _in_array(1, CONSTRUCTOR)))
API('Z3_del_constructor_list', VOID, (_in(CONTEXT), _in(CONSTRUCTOR_LIST)))
API('Z3_mk_datatypes', VOID, (_in(CONTEXT), _in(UINT), _in_array(1, SYMBOL), _out_array(1, SORT), _inout_array(1, CONSTRUCTOR_LIST)))

API('Z3_is_eq_ast', BOOL, (_in(CONTEXT), _in(AST), _in(AST)))
API('Z3_is_eq_func_decl', BOOL, (_in(CONTEXT), _in(FUNC_DECL), _in(FUNC_DECL)))
API('Z3_mk_func_decl', FUNC_DECL, (_in(CONTEXT), _in(SYMBOL), _in(UINT), _in_array(2, SORT), _in(SORT)))
API('Z3_mk_app', AST, (_in(CONTEXT), _in(FUNC_DECL), _in(UINT), _in_array(2, AST)))
API('Z3_mk_const', AST, (_in(CONTEXT), _in(SYMBOL), _in(SORT)))
API('Z3_mk_label', AST, (_in(CONTEXT), _in(SYMBOL), _in(BOOL), _in(AST)))
API('Z3_mk_fresh_func_decl', FUNC_DECL, (_in(CONTEXT), _in(STRING), _in(UINT), _in_array(2, SORT), _in(SORT)))
API('Z3_mk_fresh_const', AST, (_in(CONTEXT), _in(STRING), _in(SORT)))
API('Z3_mk_true', AST, (_in(CONTEXT), ))
API('Z3_mk_false', AST, (_in(CONTEXT), ))
API('Z3_mk_eq', AST, (_in(CONTEXT), _in(AST), _in(AST)))
API('Z3_mk_distinct', AST, (_in(CONTEXT), _in(UINT), _in_array(1, AST)))
API('Z3_mk_not', AST, (_in(CONTEXT), _in(AST)))
API('Z3_mk_ite', AST, (_in(CONTEXT), _in(AST), _in(AST), _in(AST)))
API('Z3_mk_iff', AST, (_in(CONTEXT), _in(AST), _in(AST)))
API('Z3_mk_implies', AST, (_in(CONTEXT), _in(AST), _in(AST)))
API('Z3_mk_xor', AST, (_in(CONTEXT), _in(AST), _in(AST)))
API('Z3_mk_and', AST, (_in(CONTEXT), _in(UINT), _in_array(1, AST)))
API('Z3_mk_or', AST, (_in(CONTEXT), _in(UINT), _in_array(1, AST)))
API('Z3_mk_add', AST, (_in(CONTEXT), _in(UINT), _in_array(1, AST)))
API('Z3_mk_mul', AST, (_in(CONTEXT), _in(UINT), _in_array(1, AST)))
API('Z3_mk_sub', AST, (_in(CONTEXT), _in(UINT), _in_array(1, AST)))
API('Z3_mk_unary_minus', AST, (_in(CONTEXT), _in(AST)))
API('Z3_mk_div', AST, (_in(CONTEXT), _in(AST), _in(AST)))
API('Z3_mk_mod', AST, (_in(CONTEXT), _in(AST), _in(AST)))
API('Z3_mk_rem', AST, (_in(CONTEXT), _in(AST), _in(AST)))
API('Z3_mk_power', AST, (_in(CONTEXT), _in(AST), _in(AST)))
API('Z3_is_algebraic_number', BOOL, (_in(CONTEXT), _in(AST)))
API('Z3_get_algebraic_number_lower', AST, (_in(CONTEXT), _in(AST), _in(UINT)))
API('Z3_get_algebraic_number_upper', AST, (_in(CONTEXT), _in(AST), _in(UINT)))
API('Z3_mk_lt', AST, (_in(CONTEXT), _in(AST), _in(AST)))
API('Z3_mk_le', AST, (_in(CONTEXT), _in(AST), _in(AST)))
API('Z3_mk_gt', AST, (_in(CONTEXT), _in(AST), _in(AST)))
API('Z3_mk_ge', AST, (_in(CONTEXT), _in(AST), _in(AST)))
API('Z3_mk_int2real', AST, (_in(CONTEXT), _in(AST)))
API('Z3_mk_real2int', AST, (_in(CONTEXT), _in(AST)))
API('Z3_mk_is_int', AST, (_in(CONTEXT), _in(AST)))

API('Z3_mk_bvnot', AST, (_in(CONTEXT), _in(AST)))
API('Z3_mk_bvredand', AST, (_in(CONTEXT), _in(AST)))
API('Z3_mk_bvredor', AST, (_in(CONTEXT), _in(AST)))
API('Z3_mk_bvand', AST, (_in(CONTEXT), _in(AST), _in(AST)))
API('Z3_mk_bvor', AST, (_in(CONTEXT), _in(AST), _in(AST)))
API('Z3_mk_bvxor', AST, (_in(CONTEXT), _in(AST), _in(AST)))
API('Z3_mk_bvnand', AST, (_in(CONTEXT), _in(AST), _in(AST)))
API('Z3_mk_bvnor', AST, (_in(CONTEXT), _in(AST), _in(AST)))
API('Z3_mk_bvxnor', AST, (_in(CONTEXT), _in(AST), _in(AST)))
API('Z3_mk_bvneg', AST, (_in(CONTEXT), _in(AST)))
API('Z3_mk_bvadd', AST, (_in(CONTEXT), _in(AST), _in(AST)))
API('Z3_mk_bvsub', AST, (_in(CONTEXT), _in(AST), _in(AST)))
API('Z3_mk_bvmul', AST, (_in(CONTEXT), _in(AST), _in(AST)))
API('Z3_mk_bvudiv', AST, (_in(CONTEXT), _in(AST), _in(AST)))
API('Z3_mk_bvsdiv', AST, (_in(CONTEXT), _in(AST), _in(AST)))
API('Z3_mk_bvurem', AST, (_in(CONTEXT), _in(AST), _in(AST)))
API('Z3_mk_bvsrem', AST, (_in(CONTEXT), _in(AST), _in(AST)))
API('Z3_mk_bvsmod', AST, (_in(CONTEXT), _in(AST), _in(AST)))
API('Z3_mk_bvult', AST, (_in(CONTEXT), _in(AST), _in(AST)))
API('Z3_mk_bvslt', AST, (_in(CONTEXT), _in(AST), _in(AST)))
API('Z3_mk_bvule', AST, (_in(CONTEXT), _in(AST), _in(AST)))
API('Z3_mk_bvsle', AST, (_in(CONTEXT), _in(AST), _in(AST)))
API('Z3_mk_bvuge', AST, (_in(CONTEXT), _in(AST), _in(AST)))
API('Z3_mk_bvsge', AST, (_in(CONTEXT), _in(AST), _in(AST)))
API('Z3_mk_bvugt', AST, (_in(CONTEXT), _in(AST), _in(AST)))
API('Z3_mk_bvsgt', AST, (_in(CONTEXT), _in(AST), _in(AST)))
API('Z3_mk_concat', AST, (_in(CONTEXT), _in(AST), _in(AST)))
API('Z3_mk_extract', AST, (_in(CONTEXT), _in(UINT), _in(UINT), _in(AST)))
API('Z3_mk_sign_ext', AST, (_in(CONTEXT), _in(UINT), _in(AST)))
API('Z3_mk_zero_ext', AST, (_in(CONTEXT), _in(UINT), _in(AST)))
API('Z3_mk_repeat', AST, (_in(CONTEXT), _in(UINT), _in(AST)))
API('Z3_mk_bvshl', AST, (_in(CONTEXT), _in(AST), _in(AST)))
API('Z3_mk_bvlshr', AST, (_in(CONTEXT), _in(AST), _in(AST)))
API('Z3_mk_bvashr', AST, (_in(CONTEXT), _in(AST), _in(AST)))
API('Z3_mk_rotate_left', AST, (_in(CONTEXT), _in(UINT), _in(AST)))
API('Z3_mk_rotate_right', AST, (_in(CONTEXT), _in(UINT), _in(AST)))
API('Z3_mk_ext_rotate_left', AST, (_in(CONTEXT), _in(AST), _in(AST)))
API('Z3_mk_ext_rotate_right', AST, (_in(CONTEXT), _in(AST), _in(AST)))
API('Z3_mk_int2bv', AST, (_in(CONTEXT), _in(UINT), _in(AST)))
API('Z3_mk_bv2int', AST, (_in(CONTEXT), _in(AST), _in(BOOL)))
API('Z3_mk_bvadd_no_overflow', AST, (_in(CONTEXT), _in(AST), _in(AST), _in(BOOL)))
API('Z3_mk_bvadd_no_underflow', AST, (_in(CONTEXT), _in(AST), _in(AST)))
API('Z3_mk_bvsub_no_overflow', AST, (_in(CONTEXT), _in(AST), _in(AST)))
API('Z3_mk_bvsub_no_underflow', AST, (_in(CONTEXT), _in(AST), _in(AST), _in(BOOL)))
API('Z3_mk_bvsdiv_no_overflow', AST, (_in(CONTEXT), _in(AST), _in(AST)))
API('Z3_mk_bvneg_no_overflow', AST, (_in(CONTEXT), _in(AST)))
API('Z3_mk_bvmul_no_overflow', AST, (_in(CONTEXT), _in(AST), _in(AST), _in(BOOL)))
API('Z3_mk_bvmul_no_underflow', AST, (_in(CONTEXT), _in(AST), _in(AST)))

API('Z3_mk_select', AST, (_in(CONTEXT), _in(AST), _in(AST)))
API('Z3_mk_store', AST, (_in(CONTEXT), _in(AST), _in(AST), _in(AST)))
API('Z3_mk_const_array', AST, (_in(CONTEXT), _in(SORT), _in(AST)))
API('Z3_mk_map', AST, (_in(CONTEXT), _in(FUNC_DECL), _in(UINT), _in_array(2, AST)))
API('Z3_mk_array_default', AST, (_in(CONTEXT), _in(AST)))
API('Z3_mk_set_sort', SORT, (_in(CONTEXT), _in(SORT)))
API('Z3_mk_empty_set', AST, (_in(CONTEXT), _in(SORT)))
API('Z3_mk_full_set', AST, (_in(CONTEXT), _in(SORT)))
API('Z3_mk_set_add', AST, (_in(CONTEXT), _in(AST), _in(AST)))
API('Z3_mk_set_del', AST, (_in(CONTEXT), _in(AST), _in(AST)))
API('Z3_mk_set_union', AST, (_in(CONTEXT), _in(UINT), _in_array(1, AST)))
API('Z3_mk_set_intersect', AST, (_in(CONTEXT), _in(UINT), _in_array(1, AST)))
API('Z3_mk_set_difference', AST, (_in(CONTEXT), _in(AST), _in(AST)))
API('Z3_mk_set_complement', AST, (_in(CONTEXT), _in(AST)))
API('Z3_mk_set_member', AST, (_in(CONTEXT), _in(AST), _in(AST)))
API('Z3_mk_set_subset', AST, (_in(CONTEXT), _in(AST), _in(AST)))

API('Z3_mk_numeral', AST, (_in(CONTEXT), _in(STRING), _in(SORT)))
API('Z3_mk_real', AST, (_in(CONTEXT), _in(INT), _in(INT)))
API('Z3_mk_int', AST, (_in(CONTEXT), _in(INT), _in(SORT)))
API('Z3_mk_unsigned_int', AST, (_in(CONTEXT), _in(UINT), _in(SORT)))
API('Z3_mk_int64', AST, (_in(CONTEXT), _in(INT64), _in(SORT)))
API('Z3_mk_unsigned_int64', AST, (_in(CONTEXT), _in(UINT64), _in(SORT)))

API('Z3_mk_pattern', PATTERN, (_in(CONTEXT), _in(UINT), _in_array(1, AST)))
API('Z3_mk_bound', AST, (_in(CONTEXT), _in(UINT), _in(SORT)))
API('Z3_mk_forall', AST, (_in(CONTEXT), _in(UINT),
                          _in(UINT), _in_array(2, PATTERN),
                          _in(UINT), _in_array(4, SORT), _in_array(4, SYMBOL),
                          _in(AST)))
API('Z3_mk_exists', AST, (_in(CONTEXT), _in(UINT),
                          _in(UINT), _in_array(2, PATTERN),
                          _in(UINT), _in_array(4, SORT), _in_array(4, SYMBOL),
                          _in(AST)))
API('Z3_mk_quantifier', AST, (_in(CONTEXT), _in(BOOL), _in(UINT),
                              _in(UINT), _in_array(3, PATTERN),
                              _in(UINT), _in_array(5, SORT), _in_array(5, SYMBOL),
                              _in(AST)))
API('Z3_mk_quantifier_ex', AST, (_in(CONTEXT), _in(BOOL), _in(UINT), _in(SYMBOL), _in(SYMBOL),
                                 _in(UINT), _in_array(5, PATTERN),
                                 _in(UINT), _in_array(7, AST),
                                 _in(UINT), _in_array(9, SORT), _in_array(9, SYMBOL),
                                 _in(AST)))
API('Z3_mk_forall_const', AST, (_in(CONTEXT), _in(UINT), _in(UINT), _in_array(2, APP),
                                _in(UINT), _in_array(4, PATTERN),
                                _in(AST)))
API('Z3_mk_exists_const', AST, (_in(CONTEXT), _in(UINT), _in(UINT), _in_array(2, APP),
                                _in(UINT), _in_array(4, PATTERN),
                                _in(AST)))
API('Z3_mk_quantifier_const', AST, (_in(CONTEXT), _in(BOOL), _in(UINT), _in(UINT), _in_array(3, APP),
                                    _in(UINT), _in_array(5, PATTERN),
                                    _in(AST)))
API('Z3_mk_quantifier_const_ex', AST, (_in(CONTEXT), _in(BOOL), _in(UINT), _in(SYMBOL), _in(SYMBOL),
                                       _in(UINT), _in_array(5, APP),
                                       _in(UINT), _in_array(7, PATTERN),
                                       _in(UINT), _in_array(9, AST),
                                       _in(AST)))


API('Z3_get_ast_id', UINT, (_in(CONTEXT), _in(AST)))
API('Z3_get_func_decl_id', UINT, (_in(CONTEXT), _in(FUNC_DECL)))
API('Z3_get_sort_id', UINT, (_in(CONTEXT), _in(SORT)))
API('Z3_is_well_sorted', BOOL, (_in(CONTEXT), _in(AST)))
API('Z3_get_symbol_kind', UINT, (_in(CONTEXT), _in(SYMBOL)))
API('Z3_get_symbol_int', INT, (_in(CONTEXT), _in(SYMBOL)))
API('Z3_get_symbol_string', STRING, (_in(CONTEXT), _in(SYMBOL)))
API('Z3_get_ast_kind', UINT, (_in(CONTEXT), _in(AST)))
API('Z3_get_ast_hash', UINT, (_in(CONTEXT), _in(AST)))
API('Z3_get_numeral_string', STRING, (_in(CONTEXT), _in(AST)))
API('Z3_get_numeral_decimal_string', STRING, (_in(CONTEXT), _in(AST), _in(UINT)))
API('Z3_get_numerator', AST, (_in(CONTEXT), _in(AST)))
API('Z3_get_denominator', AST, (_in(CONTEXT), _in(AST)))
API('Z3_get_numeral_small', BOOL, (_in(CONTEXT), _in(AST), _out(INT64), _out(INT64)))
API('Z3_get_numeral_int', BOOL, (_in(CONTEXT), _in(AST), _out(INT)))
API('Z3_get_numeral_uint', BOOL, (_in(CONTEXT), _in(AST), _out(UINT)))
API('Z3_get_numeral_uint64', BOOL, (_in(CONTEXT), _in(AST), _out(UINT64)))
API('Z3_get_numeral_int64', BOOL, (_in(CONTEXT), _in(AST), _out(INT64)))
API('Z3_get_numeral_rational_int64', BOOL, (_in(CONTEXT), _in(AST), _out(INT64), _out(INT64)))
API('Z3_get_bool_value', UINT, (_in(CONTEXT), _in(AST)))
API('Z3_get_app_decl', FUNC_DECL, (_in(CONTEXT), _in(APP)))
API('Z3_get_app_num_args', UINT, (_in(CONTEXT), _in(APP)))
API('Z3_get_app_arg', AST, (_in(CONTEXT), _in(APP), _in(UINT)))
API('Z3_get_index_value', UINT, (_in(CONTEXT), _in(AST)))
API('Z3_is_quantifier_forall', BOOL, (_in(CONTEXT), _in(AST)))
API('Z3_get_quantifier_weight', UINT, (_in(CONTEXT), _in(AST)))
API('Z3_get_quantifier_num_patterns', UINT, (_in(CONTEXT), _in(AST)))
API('Z3_get_quantifier_pattern_ast', PATTERN, (_in(CONTEXT), _in(AST), _in(UINT)))
API('Z3_get_quantifier_num_no_patterns', UINT, (_in(CONTEXT), _in(AST)))
API('Z3_get_quantifier_no_pattern_ast', AST, (_in(CONTEXT), _in(AST), _in(UINT)))
API('Z3_get_quantifier_bound_name', SYMBOL, (_in(CONTEXT), _in(AST), _in(UINT)))
API('Z3_get_quantifier_bound_sort', SORT, (_in(CONTEXT), _in(AST), _in(UINT)))
API('Z3_get_quantifier_body', AST, (_in(CONTEXT), _in(AST)))
API('Z3_get_quantifier_num_bound', UINT, (_in(CONTEXT), _in(AST)))
API('Z3_get_decl_name', SYMBOL, (_in(CONTEXT), _in(FUNC_DECL)))
API('Z3_get_decl_num_parameters', UINT, (_in(CONTEXT), _in(FUNC_DECL)))
API('Z3_get_decl_parameter_kind', UINT, (_in(CONTEXT), _in(FUNC_DECL), _in(UINT)))
API('Z3_get_decl_int_parameter', INT, (_in(CONTEXT), _in(FUNC_DECL), _in(UINT)))
API('Z3_get_decl_double_parameter', DOUBLE, (_in(CONTEXT), _in(FUNC_DECL), _in(UINT)))
API('Z3_get_decl_symbol_parameter', SYMBOL, (_in(CONTEXT), _in(FUNC_DECL), _in(UINT)))
API('Z3_get_decl_sort_parameter', SORT, (_in(CONTEXT), _in(FUNC_DECL), _in(UINT)))
API('Z3_get_decl_ast_parameter', AST, (_in(CONTEXT), _in(FUNC_DECL), _in(UINT)))
API('Z3_get_decl_func_decl_parameter', FUNC_DECL, (_in(CONTEXT), _in(FUNC_DECL), _in(UINT)))
API('Z3_get_decl_rational_parameter', STRING, (_in(CONTEXT), _in(FUNC_DECL), _in(UINT)))
API('Z3_get_sort_name', SYMBOL, (_in(CONTEXT), _in(SORT)))
API('Z3_get_sort', SORT, (_in(CONTEXT), _in(AST)))
API('Z3_get_domain_size', UINT, (_in(CONTEXT), _in(FUNC_DECL)))
API('Z3_get_domain', SORT, (_in(CONTEXT), _in(FUNC_DECL), _in(UINT)))
API('Z3_get_range', SORT, (_in(CONTEXT), _in(FUNC_DECL)))
API('Z3_get_sort_kind', UINT, (_in(CONTEXT), _in(SORT)))
API('Z3_get_bv_sort_size', UINT, (_in(CONTEXT), _in(SORT)))
API('Z3_get_array_sort_domain', SORT, (_in(CONTEXT), _in(SORT)))
API('Z3_get_array_sort_range', SORT, (_in(CONTEXT), _in(SORT)))
API('Z3_get_tuple_sort_mk_decl', FUNC_DECL, (_in(CONTEXT), _in(SORT)))
API('Z3_get_decl_kind', UINT, (_in(CONTEXT), _in(FUNC_DECL)))
API('Z3_get_tuple_sort_num_fields', UINT, (_in(CONTEXT), _in(SORT)))
API('Z3_get_tuple_sort_field_decl', FUNC_DECL, (_in(CONTEXT), _in(SORT), _in(UINT)))
API('Z3_get_datatype_sort_num_constructors', UINT, (_in(CONTEXT), _in(SORT)))
API('Z3_get_datatype_sort_constructor', FUNC_DECL, (_in(CONTEXT), _in(SORT), _in(UINT)))
API('Z3_get_datatype_sort_recognizer', FUNC_DECL, (_in(CONTEXT), _in(SORT), _in(UINT)))
API('Z3_get_datatype_sort_constructor_accessor', FUNC_DECL, (_in(CONTEXT), _in(SORT), _in(UINT), _in(UINT)))
API('Z3_get_relation_arity', UINT, (_in(CONTEXT), _in(SORT)))
API('Z3_get_relation_column', SORT, (_in(CONTEXT), _in(SORT), _in(UINT)))
API('Z3_get_finite_domain_sort_size', BOOL, (_in(CONTEXT), _in(SORT), _out(UINT64)))
API('Z3_mk_finite_domain_sort', SORT, (_in(CONTEXT), _in(SYMBOL), _in(UINT64)))
API('Z3_get_pattern_num_terms', UINT, (_in(CONTEXT), _in(PATTERN)))
API('Z3_get_pattern', AST, (_in(CONTEXT), _in(PATTERN), _in(UINT)))

API('Z3_simplify', AST, (_in(CONTEXT), _in(AST)))
API('Z3_simplify_ex', AST, (_in(CONTEXT), _in(AST), _in(PARAMS)))
API('Z3_simplify_get_help', STRING, (_in(CONTEXT),))
API('Z3_simplify_get_param_descrs', PARAM_DESCRS, (_in(CONTEXT),))

API('Z3_update_term', AST, (_in(CONTEXT), _in(AST), _in(UINT), _in_array(2, AST)))
API('Z3_substitute', AST, (_in(CONTEXT), _in(AST), _in(UINT), _in_array(2, AST), _in_array(2, AST)))
API('Z3_substitute_vars', AST, (_in(CONTEXT), _in(AST), _in(UINT), _in_array(2, AST)))

API('Z3_sort_to_ast', AST, (_in(CONTEXT), _in(SORT)))
API('Z3_func_decl_to_ast', AST, (_in(CONTEXT), _in(FUNC_DECL)))
API('Z3_pattern_to_ast', AST, (_in(CONTEXT), _in(PATTERN)))
API('Z3_app_to_ast', AST, (_in(CONTEXT), _in(APP)))
API('Z3_to_app', APP, (_in(CONTEXT), _in(AST)))
API('Z3_to_func_decl', FUNC_DECL, (_in(CONTEXT), _in(AST)))

API('Z3_push', VOID, (_in(CONTEXT),))
API('Z3_pop', VOID, (_in(CONTEXT), _in(UINT)))
API('Z3_get_num_scopes', UINT, (_in(CONTEXT),))
API('Z3_persist_ast', VOID, (_in(CONTEXT), _in(AST), _in(UINT)))
API('Z3_assert_cnstr', VOID, (_in(CONTEXT), _in(AST)))
API('Z3_check_and_get_model', INT, (_in(CONTEXT), _out(MODEL)))
API('Z3_check', INT, (_in(CONTEXT),))
API('Z3_check_assumptions', INT, (_in(CONTEXT), _in(UINT), _in_array(1, AST), _out(MODEL), _out(AST), _out(UINT), _out_array2(1, 5, AST)))
API('Z3_get_implied_equalities', UINT, (_in(CONTEXT), _in(UINT), _in_array(1, AST), _out_array(1, UINT)))
API('Z3_del_model', VOID, (_in(CONTEXT), _in(MODEL)))

API('Z3_soft_check_cancel', VOID, (_in(CONTEXT), ))
API('Z3_get_search_failure', UINT, (_in(CONTEXT), ))

API('Z3_get_relevant_labels', LITERALS, (_in(CONTEXT), ))
API('Z3_get_relevant_literals', LITERALS, (_in(CONTEXT), ))
API('Z3_get_guessed_literals', LITERALS, (_in(CONTEXT), ))
API('Z3_del_literals', VOID, (_in(CONTEXT), _in(LITERALS)))
API('Z3_get_num_literals', UINT, (_in(CONTEXT), _in(LITERALS)))
API('Z3_get_label_symbol', SYMBOL, (_in(CONTEXT), _in(LITERALS), _in(UINT)))
API('Z3_get_literal', AST, (_in(CONTEXT), _in(LITERALS), _in(UINT)))
API('Z3_disable_literal', VOID, (_in(CONTEXT), _in(LITERALS), _in(UINT)))
API('Z3_block_literals', VOID, (_in(CONTEXT), _in(LITERALS)))

API('Z3_model_inc_ref', VOID, (_in(CONTEXT), _in(MODEL)))
API('Z3_model_dec_ref', VOID, (_in(CONTEXT), _in(MODEL)))
API('Z3_model_get_const_interp', AST, (_in(CONTEXT), _in(MODEL), _in(FUNC_DECL)))
API('Z3_model_get_func_interp', FUNC_INTERP, (_in(CONTEXT), _in(MODEL), _in(FUNC_DECL)))
API('Z3_model_get_num_consts', UINT, (_in(CONTEXT), _in(MODEL)))
API('Z3_model_get_const_decl', FUNC_DECL, (_in(CONTEXT), _in(MODEL), _in(UINT)))
API('Z3_model_get_num_funcs', UINT, (_in(CONTEXT), _in(MODEL)))
API('Z3_model_get_func_decl', FUNC_DECL, (_in(CONTEXT), _in(MODEL), _in(UINT)))
API('Z3_model_eval', BOOL, (_in(CONTEXT), _in(MODEL), _in(AST), _in(BOOL), _out(AST)))
API('Z3_model_get_num_sorts', UINT, (_in(CONTEXT), _in(MODEL)))
API('Z3_model_get_sort', SORT, (_in(CONTEXT), _in(MODEL), _in(UINT)))
API('Z3_model_get_sort_universe', AST_VECTOR, (_in(CONTEXT), _in(MODEL), _in(SORT)))
API('Z3_is_as_array', BOOL, (_in(CONTEXT), _in(AST)))
API('Z3_get_as_array_func_decl', FUNC_DECL, (_in(CONTEXT), _in(AST)))
API('Z3_func_interp_inc_ref', VOID, (_in(CONTEXT), _in(FUNC_INTERP)))
API('Z3_func_interp_dec_ref', VOID, (_in(CONTEXT), _in(FUNC_INTERP)))
API('Z3_func_interp_get_num_entries', UINT, (_in(CONTEXT), _in(FUNC_INTERP)))
API('Z3_func_interp_get_entry', FUNC_ENTRY, (_in(CONTEXT), _in(FUNC_INTERP), _in(UINT)))
API('Z3_func_interp_get_else', AST, (_in(CONTEXT), _in(FUNC_INTERP)))
API('Z3_func_interp_get_arity', UINT, (_in(CONTEXT), _in(FUNC_INTERP)))
API('Z3_func_entry_inc_ref', VOID, (_in(CONTEXT), _in(FUNC_ENTRY)))
API('Z3_func_entry_dec_ref', VOID, (_in(CONTEXT), _in(FUNC_ENTRY)))
API('Z3_func_entry_get_value', AST, (_in(CONTEXT), _in(FUNC_ENTRY)))
API('Z3_func_entry_get_num_args', UINT, (_in(CONTEXT), _in(FUNC_ENTRY)))
API('Z3_func_entry_get_arg', AST, (_in(CONTEXT), _in(FUNC_ENTRY), _in(UINT)))

API('Z3_get_model_num_constants', UINT, (_in(CONTEXT), _in(MODEL)))
API('Z3_get_model_constant', FUNC_DECL, (_in(CONTEXT), _in(MODEL), _in(UINT)))
API('Z3_eval_func_decl', BOOL, (_in(CONTEXT), _in(MODEL), _in(FUNC_DECL), _out(AST)))
API('Z3_is_array_value', BOOL, (_in(CONTEXT), _in(MODEL), _in(AST), _out(UINT)))
API('Z3_get_array_value', VOID, (_in(CONTEXT), _in(MODEL), _in(AST),
                                 _in(UINT), _out_array(3, AST), _out_array(3, AST),
                                 _out (AST)))
API('Z3_get_model_num_funcs', UINT, (_in(CONTEXT), _in(MODEL)))
API('Z3_get_model_func_decl', FUNC_DECL, (_in(CONTEXT), _in(MODEL), _in(UINT)))
API('Z3_get_model_func_else', AST, (_in(CONTEXT), _in(MODEL), _in(UINT)))
API('Z3_get_model_func_num_entries', UINT, (_in(CONTEXT), _in(MODEL), _in(UINT)))
API('Z3_get_model_func_entry_num_args', UINT, (_in(CONTEXT), _in(MODEL), _in(UINT), _in(UINT)))
API('Z3_get_model_func_entry_arg', AST, (_in(CONTEXT), _in(MODEL), _in(UINT), _in(UINT), _in(UINT)))
API('Z3_get_model_func_entry_value', AST, (_in(CONTEXT), _in(MODEL), _in(UINT), _in(UINT)))
API('Z3_eval', BOOL, (_in(CONTEXT), _in(MODEL), _in(AST), _out(AST)))
API('Z3_eval_decl', BOOL, (_in(CONTEXT), _in(MODEL), _in(FUNC_DECL), _in(UINT), _in_array(3, AST), _out(AST)))

API('Z3_set_ast_print_mode', VOID, (_in(CONTEXT), _in(PRINT_MODE)))
API('Z3_ast_to_string', STRING, (_in(CONTEXT), _in(AST)))
API('Z3_pattern_to_string', STRING, (_in(CONTEXT), _in(PATTERN)))
API('Z3_sort_to_string', STRING, (_in(CONTEXT), _in(SORT)))
API('Z3_func_decl_to_string', STRING, (_in(CONTEXT), _in(FUNC_DECL)))
API('Z3_model_to_string', STRING, (_in(CONTEXT), _in(MODEL)))
API('Z3_benchmark_to_smtlib_string', STRING, (_in(CONTEXT), _in(STRING), _in(STRING), _in(STRING), _in(STRING), _in(UINT), _in_array(5, AST), _in(AST)))
API('Z3_context_to_string', STRING, (_in(CONTEXT),))
API('Z3_statistics_to_string', STRING, (_in(CONTEXT),))

API('Z3_get_context_assignment', AST, (_in(CONTEXT),))

API('Z3_parse_smtlib_string', VOID, (_in(CONTEXT), _in(STRING), _in(UINT), _in_array(2, SYMBOL), _in_array(2, SORT),
                                     _in(UINT), _in_array(5, SYMBOL), _in_array(5, FUNC_DECL)))
API('Z3_parse_smtlib_file', VOID, (_in(CONTEXT), _in(STRING), _in(UINT), _in_array(2, SYMBOL), _in_array(2, SORT),
                                   _in(UINT), _in_array(5, SYMBOL), _in_array(5, FUNC_DECL)))
API('Z3_get_smtlib_num_formulas', UINT, (_in(CONTEXT), ))
API('Z3_get_smtlib_formula', AST, (_in(CONTEXT), _in(UINT)))
API('Z3_get_smtlib_num_assumptions', UINT, (_in(CONTEXT), ))
API('Z3_get_smtlib_assumption', AST, (_in(CONTEXT), _in(UINT)))
API('Z3_get_smtlib_num_decls', UINT, (_in(CONTEXT), ))
API('Z3_get_smtlib_decl', FUNC_DECL, (_in(CONTEXT), _in(UINT)))
API('Z3_get_smtlib_num_sorts', UINT, (_in(CONTEXT), ))
API('Z3_get_smtlib_sort', SORT, (_in(CONTEXT), _in(UINT)))
API('Z3_get_smtlib_error', STRING, (_in(CONTEXT), ))

API('Z3_parse_z3_string', AST, (_in(CONTEXT), _in(STRING)))
API('Z3_parse_z3_file', AST, (_in(CONTEXT), _in(STRING)))

API('Z3_parse_smtlib2_string', AST, (_in(CONTEXT), _in(STRING), _in(UINT), _in_array(2, SYMBOL), _in_array(2, SORT),
                                     _in(UINT), _in_array(5, SYMBOL), _in_array(5, FUNC_DECL)))
API('Z3_parse_smtlib2_file', AST, (_in(CONTEXT), _in(STRING), _in(UINT), _in_array(2, SYMBOL), _in_array(2, SORT),
                                   _in(UINT), _in_array(5, SYMBOL), _in_array(5, FUNC_DECL)))

API('Z3_get_error_code', UINT, (_in(CONTEXT), ))
API('Z3_set_error', VOID, (_in(CONTEXT), _in(ERROR_CODE)))
API('Z3_get_error_msg', STRING, (_in(ERROR_CODE),))

API('Z3_get_version', VOID, (_out(UINT), _out(UINT), _out(UINT), _out(UINT)))
API('Z3_reset_memory', VOID, ())
API('Z3_is_app', BOOL, (_in(CONTEXT), _in(AST)))
API('Z3_is_numeral_ast', BOOL, (_in(CONTEXT), _in(AST)))
API('Z3_get_arity', UINT, (_in(CONTEXT), _in(FUNC_DECL)))
API('Z3_mk_injective_function', FUNC_DECL, (_in(CONTEXT), _in(SYMBOL), _in(UINT), _in_array(2, SORT), _in(SORT)))

API('Z3_mk_fixedpoint', FIXEDPOINT, (_in(CONTEXT), ))
API('Z3_fixedpoint_inc_ref', VOID, (_in(CONTEXT), _in(FIXEDPOINT)))
API('Z3_fixedpoint_dec_ref', VOID, (_in(CONTEXT), _in(FIXEDPOINT)))
API('Z3_fixedpoint_push', VOID, (_in(CONTEXT), _in(FIXEDPOINT)))
API('Z3_fixedpoint_pop', VOID, (_in(CONTEXT), _in(FIXEDPOINT)))
API('Z3_fixedpoint_register_relation', VOID, (_in(CONTEXT), _in(FIXEDPOINT), _in(FUNC_DECL)))
API('Z3_fixedpoint_assert', VOID, (_in(CONTEXT), _in(FIXEDPOINT), _in(AST)))
API('Z3_fixedpoint_add_rule', VOID, (_in(CONTEXT), _in(FIXEDPOINT), _in(AST), _in(SYMBOL)))
API('Z3_fixedpoint_add_fact', VOID, (_in(CONTEXT), _in(FIXEDPOINT), _in(FUNC_DECL), _in(UINT), _in_array(3, UINT)))
API('Z3_fixedpoint_query', INT, (_in(CONTEXT), _in(FIXEDPOINT), _in(AST)))
API('Z3_fixedpoint_query_relations', INT, (_in(CONTEXT), _in(FIXEDPOINT), _in(UINT), _in_array(2, FUNC_DECL)))
API('Z3_fixedpoint_get_answer', AST, (_in(CONTEXT), _in(FIXEDPOINT)))
API('Z3_fixedpoint_update_rule', VOID, (_in(CONTEXT), _in(FIXEDPOINT), _in(AST), _in(SYMBOL)))
API('Z3_fixedpoint_get_num_levels', UINT, (_in(CONTEXT), _in(FIXEDPOINT), _in(FUNC_DECL)))
API('Z3_fixedpoint_get_cover_delta', AST, (_in(CONTEXT), _in(FIXEDPOINT), _in(INT), _in(FUNC_DECL)))
API('Z3_fixedpoint_add_cover', VOID, (_in(CONTEXT), _in(FIXEDPOINT), _in(INT), _in(FUNC_DECL), _in(AST)))
API('Z3_fixedpoint_get_statistics', STATS, (_in(CONTEXT), _in(FIXEDPOINT)))
API('Z3_fixedpoint_get_help', STRING, (_in(CONTEXT), _in(FIXEDPOINT)))
API('Z3_fixedpoint_get_param_descrs', PARAM_DESCRS, (_in(CONTEXT), _in(FIXEDPOINT)))
API('Z3_fixedpoint_set_params', VOID, (_in(CONTEXT), _in(FIXEDPOINT), _in(PARAMS)))
API('Z3_fixedpoint_to_string', STRING, (_in(CONTEXT), _in(FIXEDPOINT), _in(UINT), _in_array(2, AST)))
API('Z3_fixedpoint_get_reason_unknown', STRING, (_in(CONTEXT), _in(FIXEDPOINT) ))
API('Z3_fixedpoint_set_predicate_representation', VOID, (_in(CONTEXT), _in(FIXEDPOINT), _in(FUNC_DECL), _in(UINT), _in_array(3, SYMBOL)))
API('Z3_fixedpoint_simplify_rules', AST_VECTOR, (_in(CONTEXT), _in(FIXEDPOINT), _in(UINT), _in_array(2,AST), _in(UINT), _in_array(4,FUNC_DECL)))
# Parameter set support
API('Z3_mk_params', PARAMS, (_in(CONTEXT),))
API('Z3_params_inc_ref', VOID, (_in(CONTEXT), _in(PARAMS)))
API('Z3_params_dec_ref', VOID, (_in(CONTEXT), _in(PARAMS)))
API('Z3_params_set_bool', VOID, (_in(CONTEXT), _in(PARAMS), _in(SYMBOL), _in(BOOL)))
API('Z3_params_set_uint', VOID, (_in(CONTEXT), _in(PARAMS), _in(SYMBOL), _in(UINT)))
API('Z3_params_set_double', VOID, (_in(CONTEXT), _in(PARAMS), _in(SYMBOL), _in(DOUBLE)))
API('Z3_params_set_symbol', VOID, (_in(CONTEXT), _in(PARAMS), _in(SYMBOL), _in(SYMBOL)))
API('Z3_params_to_string', STRING, (_in(CONTEXT), _in(PARAMS)))
API('Z3_params_validate', VOID, (_in(CONTEXT), _in(PARAMS), _in(PARAM_DESCRS)))
# Parameter description
API('Z3_param_descrs_inc_ref', VOID, (_in(CONTEXT), _in(PARAM_DESCRS)))
API('Z3_param_descrs_dec_ref', VOID, (_in(CONTEXT), _in(PARAM_DESCRS)))
API('Z3_param_descrs_get_kind', UINT, (_in(CONTEXT), _in(PARAM_DESCRS), _in(SYMBOL)))
API('Z3_param_descrs_size', UINT, (_in(CONTEXT), _in(PARAM_DESCRS)))
API('Z3_param_descrs_get_name', SYMBOL, (_in(CONTEXT), _in(PARAM_DESCRS), _in(UINT)))
# New APIs
API('Z3_interrupt', VOID, (_in(CONTEXT),))
API('Z3_get_error_msg_ex', STRING, (_in(CONTEXT), _in(ERROR_CODE)))
API('Z3_translate', AST, (_in(CONTEXT), _in(AST), _in(CONTEXT)))
# Goal support
API('Z3_mk_goal', GOAL, (_in(CONTEXT), _in(BOOL), _in(BOOL), _in(BOOL)))
API('Z3_goal_inc_ref', VOID, (_in(CONTEXT), _in(GOAL)))
API('Z3_goal_dec_ref', VOID, (_in(CONTEXT), _in(GOAL)))
API('Z3_goal_precision', UINT, (_in(CONTEXT), _in(GOAL)))
API('Z3_goal_assert', VOID, (_in(CONTEXT), _in(GOAL), _in(AST)))
API('Z3_goal_inconsistent', BOOL, (_in(CONTEXT), _in(GOAL)))
API('Z3_goal_depth', UINT, (_in(CONTEXT), _in(GOAL)))
API('Z3_goal_reset', VOID, (_in(CONTEXT), _in(GOAL)))
API('Z3_goal_size', UINT, (_in(CONTEXT), _in(GOAL)))
API('Z3_goal_formula', AST, (_in(CONTEXT), _in(GOAL), _in(UINT)))
API('Z3_goal_num_exprs', UINT, (_in(CONTEXT), _in(GOAL)))
API('Z3_goal_is_decided_sat', BOOL, (_in(CONTEXT), _in(GOAL)))
API('Z3_goal_is_decided_unsat', BOOL, (_in(CONTEXT), _in(GOAL)))
API('Z3_goal_translate', GOAL, (_in(CONTEXT), _in(GOAL), _in(CONTEXT)))
API('Z3_goal_to_string', STRING, (_in(CONTEXT), _in(GOAL)))
# Tactics and Goals
API('Z3_mk_tactic', TACTIC, (_in(CONTEXT), _in(STRING)))
API('Z3_mk_probe', PROBE, (_in(CONTEXT), _in(STRING)))
API('Z3_tactic_inc_ref', VOID, (_in(CONTEXT), _in(TACTIC)))
API('Z3_tactic_dec_ref', VOID, (_in(CONTEXT), _in(TACTIC)))
API('Z3_probe_inc_ref', VOID, (_in(CONTEXT), _in(PROBE)))
API('Z3_probe_dec_ref', VOID, (_in(CONTEXT), _in(PROBE)))
API('Z3_tactic_and_then', TACTIC, (_in(CONTEXT), _in(TACTIC), _in(TACTIC)))
API('Z3_tactic_or_else', TACTIC, (_in(CONTEXT), _in(TACTIC), _in(TACTIC)))
API('Z3_tactic_par_or', TACTIC, (_in(CONTEXT), _in(UINT), _in_array(1, TACTIC)))
API('Z3_tactic_par_and_then', TACTIC, (_in(CONTEXT), _in(TACTIC), _in(TACTIC)))
API('Z3_tactic_try_for', TACTIC, (_in(CONTEXT), _in(TACTIC), _in(UINT)))
API('Z3_tactic_when', TACTIC, (_in(CONTEXT), _in(PROBE), _in(TACTIC)))
API('Z3_tactic_cond', TACTIC, (_in(CONTEXT), _in(PROBE), _in(TACTIC), _in(TACTIC)))
API('Z3_tactic_repeat', TACTIC, (_in(CONTEXT), _in(TACTIC), _in(UINT)))
API('Z3_tactic_skip', TACTIC, (_in(CONTEXT),))
API('Z3_tactic_fail', TACTIC, (_in(CONTEXT),))
API('Z3_tactic_fail_if', TACTIC, (_in(CONTEXT), _in(PROBE)))
API('Z3_tactic_fail_if_not_decided', TACTIC, (_in(CONTEXT),))
API('Z3_tactic_using_params', TACTIC, (_in(CONTEXT), _in(TACTIC), _in(PARAMS)))
API('Z3_probe_const', PROBE, (_in(CONTEXT), _in(DOUBLE)))
API('Z3_probe_lt', PROBE, (_in(CONTEXT), _in(PROBE), _in(PROBE)))
API('Z3_probe_le', PROBE, (_in(CONTEXT), _in(PROBE), _in(PROBE)))
API('Z3_probe_gt', PROBE, (_in(CONTEXT), _in(PROBE), _in(PROBE)))
API('Z3_probe_ge', PROBE, (_in(CONTEXT), _in(PROBE), _in(PROBE)))
API('Z3_probe_eq', PROBE, (_in(CONTEXT), _in(PROBE), _in(PROBE)))
API('Z3_probe_and', PROBE, (_in(CONTEXT), _in(PROBE), _in(PROBE)))
API('Z3_probe_or', PROBE, (_in(CONTEXT), _in(PROBE), _in(PROBE)))
API('Z3_probe_not', PROBE, (_in(CONTEXT), _in(PROBE)))
API('Z3_get_num_tactics', UINT, (_in(CONTEXT),))
API('Z3_get_tactic_name', STRING, (_in(CONTEXT), _in(UINT)))
API('Z3_get_num_probes', UINT, (_in(CONTEXT),))
API('Z3_get_probe_name', STRING, (_in(CONTEXT), _in(UINT)))
API('Z3_tactic_get_help', STRING, (_in(CONTEXT), _in(TACTIC)))
API('Z3_tactic_get_param_descrs', PARAM_DESCRS, (_in(CONTEXT), _in(TACTIC)))
API('Z3_tactic_get_descr', STRING, (_in(CONTEXT), _in(STRING)))
API('Z3_probe_get_descr', STRING, (_in(CONTEXT), _in(STRING)))
API('Z3_probe_apply', DOUBLE, (_in(CONTEXT), _in(PROBE), _in(GOAL)))
API('Z3_tactic_apply', APPLY_RESULT, (_in(CONTEXT), _in(TACTIC), _in(GOAL)))
API('Z3_tactic_apply_ex', APPLY_RESULT, (_in(CONTEXT), _in(TACTIC), _in(GOAL), _in(PARAMS)))
API('Z3_apply_result_inc_ref', VOID, (_in(CONTEXT), _in(APPLY_RESULT)))
API('Z3_apply_result_dec_ref', VOID, (_in(CONTEXT), _in(APPLY_RESULT)))
API('Z3_apply_result_to_string', STRING, (_in(CONTEXT), _in(APPLY_RESULT)))
API('Z3_apply_result_get_num_subgoals', UINT, (_in(CONTEXT), _in(APPLY_RESULT)))
API('Z3_apply_result_get_subgoal', GOAL, (_in(CONTEXT), _in(APPLY_RESULT), _in(UINT)))
API('Z3_apply_result_convert_model', MODEL, (_in(CONTEXT), _in(APPLY_RESULT), _in(UINT), _in(MODEL)))
# Solver API
API('Z3_mk_solver', SOLVER, (_in(CONTEXT),))
API('Z3_mk_simple_solver', SOLVER, (_in(CONTEXT),))
API('Z3_mk_solver_for_logic', SOLVER, (_in(CONTEXT), _in(SYMBOL)))
API('Z3_mk_solver_from_tactic', SOLVER, (_in(CONTEXT), _in(TACTIC)))
API('Z3_solver_get_help', STRING, (_in(CONTEXT), _in(SOLVER)))
API('Z3_solver_get_param_descrs', PARAM_DESCRS, (_in(CONTEXT), _in(SOLVER)))
API('Z3_solver_set_params', VOID, (_in(CONTEXT), _in(SOLVER), _in(PARAMS)))
API('Z3_solver_inc_ref', VOID, (_in(CONTEXT), _in(SOLVER)))
API('Z3_solver_dec_ref', VOID, (_in(CONTEXT), _in(SOLVER)))
API('Z3_solver_push', VOID, (_in(CONTEXT), _in(SOLVER)))
API('Z3_solver_pop', VOID, (_in(CONTEXT), _in(SOLVER), _in(UINT)))
API('Z3_solver_reset', VOID, (_in(CONTEXT), _in(SOLVER)))
API('Z3_solver_get_num_scopes', UINT, (_in(CONTEXT), _in(SOLVER)))
API('Z3_solver_assert', VOID, (_in(CONTEXT), _in(SOLVER), _in(AST)))
API('Z3_solver_get_assertions', AST_VECTOR, (_in(CONTEXT), _in(SOLVER)))
API('Z3_solver_check', INT, (_in(CONTEXT), _in(SOLVER)))
API('Z3_solver_check_assumptions', INT, (_in(CONTEXT), _in(SOLVER), _in(UINT), _in_array(2, AST)))
API('Z3_solver_get_model', MODEL, (_in(CONTEXT), _in(SOLVER)))
API('Z3_solver_get_proof', AST, (_in(CONTEXT), _in(SOLVER)))
API('Z3_solver_get_unsat_core', AST_VECTOR, (_in(CONTEXT), _in(SOLVER)))
API('Z3_solver_get_reason_unknown', STRING, (_in(CONTEXT), _in(SOLVER)))
API('Z3_solver_get_statistics', STATS, (_in(CONTEXT), _in(SOLVER)))
API('Z3_solver_to_string', STRING, (_in(CONTEXT), _in(SOLVER)))
# Statistics API
API('Z3_stats_to_string', STRING, (_in(CONTEXT), _in(STATS)))
API('Z3_stats_inc_ref', VOID, (_in(CONTEXT), _in(STATS)))
API('Z3_stats_dec_ref', VOID, (_in(CONTEXT), _in(STATS)))
API('Z3_stats_size', UINT, (_in(CONTEXT), _in(STATS)))
API('Z3_stats_get_key', STRING, (_in(CONTEXT), _in(STATS), _in(UINT)))
API('Z3_stats_is_uint', BOOL, (_in(CONTEXT), _in(STATS), _in(UINT)))
API('Z3_stats_is_double', BOOL, (_in(CONTEXT), _in(STATS), _in(UINT)))
API('Z3_stats_get_uint_value', UINT, (_in(CONTEXT), _in(STATS), _in(UINT)))
API('Z3_stats_get_double_value', DOUBLE, (_in(CONTEXT), _in(STATS), _in(UINT)))
# AST Vectors
API('Z3_mk_ast_vector', AST_VECTOR, (_in(CONTEXT),))
API('Z3_ast_vector_inc_ref', VOID, (_in(CONTEXT), _in(AST_VECTOR)))
API('Z3_ast_vector_dec_ref', VOID, (_in(CONTEXT), _in(AST_VECTOR)))
API('Z3_ast_vector_size', UINT, (_in(CONTEXT), _in(AST_VECTOR)))
API('Z3_ast_vector_get', AST, (_in(CONTEXT), _in(AST_VECTOR), _in(UINT)))
API('Z3_ast_vector_set', VOID, (_in(CONTEXT), _in(AST_VECTOR), _in(UINT), _in(AST)))
API('Z3_ast_vector_resize', VOID, (_in(CONTEXT), _in(AST_VECTOR), _in(UINT)))
API('Z3_ast_vector_push', VOID, (_in(CONTEXT), _in(AST_VECTOR), _in(AST)))
API('Z3_ast_vector_translate', AST_VECTOR, (_in(CONTEXT), _in(AST_VECTOR), _in(CONTEXT)))
API('Z3_ast_vector_to_string', STRING, (_in(CONTEXT), _in(AST_VECTOR)))
# AST Maps
API('Z3_mk_ast_map', AST_MAP, (_in(CONTEXT),))
API('Z3_ast_map_inc_ref', VOID, (_in(CONTEXT), _in(AST_MAP)))
API('Z3_ast_map_dec_ref', VOID, (_in(CONTEXT), _in(AST_MAP)))
API('Z3_ast_map_contains', BOOL, (_in(CONTEXT), _in(AST_MAP), _in(AST)))
API('Z3_ast_map_find', AST, (_in(CONTEXT), _in(AST_MAP), _in(AST)))
API('Z3_ast_map_insert', VOID, (_in(CONTEXT), _in(AST_MAP), _in(AST), _in(AST)))
API('Z3_ast_map_erase', VOID, (_in(CONTEXT), _in(AST_MAP), _in(AST)))
API('Z3_ast_map_size', UINT, (_in(CONTEXT), _in(AST_MAP)))
API('Z3_ast_map_reset', VOID, (_in(CONTEXT), _in(AST_MAP)))
API('Z3_ast_map_keys', AST_VECTOR, (_in(CONTEXT), _in(AST_MAP)))
API('Z3_ast_map_to_string', STRING, (_in(CONTEXT), _in(AST_MAP)))
# WARNING: we do not support logging for the theory plugin API
extra_API('Z3_open_log', INT, (_in(STRING),))
extra_API('Z3_append_log', VOID, (_in(STRING),))
extra_API('Z3_close_log', VOID, ())

mk_bindings()
mk_py_wrappers()
mk_dotnet()
mk_dotnet_wrappers()
# mk_defs()
