
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

log_h   = open(os.path.join(api_dir, 'api_log_macros.h'), 'w')
log_c   = open(os.path.join(api_dir, 'api_log_macros.cpp'), 'w')
exe_c   = open(os.path.join(api_dir, 'api_commands.cpp'), 'w')
core_py = open(os.path.join(get_z3py_dir(), 'z3core.py'), 'w')
dotnet_fileout = os.path.join(dotnet_dir, 'Native.cs')
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
exe_c.write('void Z3_replacer_error_handler(Z3_context ctx, Z3_error_code c) { printf("[REPLAYER ERROR HANDLER]: %s\\n", Z3_get_error_msg(ctx, c)); }\n')
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

def _to_ascii(s):
  if isinstance(s, str):
    return s.encode('ascii')
  else:
    return s

if sys.version < '3':
  def _to_pystr(s):
     return s
else:
  def _to_pystr(s):
     if s != None:
        enc = sys.stdout.encoding
        if enc != None: return s.decode(enc)
        else: return s.decode('ascii')
     else:
        return ""

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
OUT_MANAGED_ARRAY  = 6

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
FLOAT      = 13

FIRST_OBJ_ID = 100

def is_obj(ty):
    return ty >= FIRST_OBJ_ID

Type2Str = { VOID : 'void', VOID_PTR : 'void*', INT : 'int', UINT : 'unsigned', INT64 : '__int64', UINT64 : '__uint64', DOUBLE : 'double',
             FLOAT : 'float', STRING : 'Z3_string', STRING_PTR : 'Z3_string_ptr', BOOL : 'Z3_bool', SYMBOL : 'Z3_symbol',
             PRINT_MODE : 'Z3_ast_print_mode', ERROR_CODE : 'Z3_error_code'
             }

Type2PyStr = { VOID_PTR : 'ctypes.c_void_p', INT : 'ctypes.c_int', UINT : 'ctypes.c_uint', INT64 : 'ctypes.c_longlong',
               UINT64 : 'ctypes.c_ulonglong', DOUBLE : 'ctypes.c_double', FLOAT : 'ctypes.c_float',
               STRING : 'ctypes.c_char_p', STRING_PTR : 'ctypes.POINTER(ctypes.c_char_p)', BOOL : 'ctypes.c_bool', SYMBOL : 'Symbol',
               PRINT_MODE : 'ctypes.c_uint', ERROR_CODE : 'ctypes.c_uint'
               }

# Mapping to .NET types
Type2Dotnet = { VOID : 'void', VOID_PTR : 'IntPtr', INT : 'int', UINT : 'uint', INT64 : 'Int64', UINT64 : 'UInt64', DOUBLE : 'double',
                FLOAT : 'float', STRING : 'string', STRING_PTR : 'byte**', BOOL : 'int', SYMBOL : 'IntPtr',
                PRINT_MODE : 'uint', ERROR_CODE : 'uint' }

# Mapping to Java types
Type2Java = { VOID : 'void', VOID_PTR : 'long', INT : 'int', UINT : 'int', INT64 : 'long', UINT64 : 'long', DOUBLE : 'double',
              FLOAT : 'float', STRING : 'String', STRING_PTR : 'StringPtr', 
              BOOL : 'boolean', SYMBOL : 'long', PRINT_MODE : 'int', ERROR_CODE : 'int'}

Type2JavaW = { VOID : 'void', VOID_PTR : 'jlong', INT : 'jint', UINT : 'jint', INT64 : 'jlong', UINT64 : 'jlong', DOUBLE : 'jdouble',
               FLOAT : 'jfloat', STRING : 'jstring', STRING_PTR : 'jobject',
               BOOL : 'jboolean', SYMBOL : 'jlong', PRINT_MODE : 'jint', ERROR_CODE : 'jint'}

# Mapping to ML types
Type2ML = { VOID : 'unit', VOID_PTR : 'VOIDP', INT : 'int', UINT : 'int', INT64 : 'int', UINT64 : 'int', DOUBLE : 'float',
            FLOAT : 'float', STRING : 'string', STRING_PTR : 'char**', 
            BOOL : 'bool', SYMBOL : 'z3_symbol', PRINT_MODE : 'int', ERROR_CODE : 'int' }

next_type_id = FIRST_OBJ_ID

def def_Type(var, c_type, py_type):
    global next_type_id
    exec('%s = %s' % (var, next_type_id), globals())
    Type2Str[next_type_id]   = c_type
    Type2PyStr[next_type_id] = py_type
    next_type_id    = next_type_id + 1

def def_Types():
    import re
    pat1 = re.compile(" *def_Type\(\'(.*)\',[^\']*\'(.*)\',[^\']*\'(.*)\'\)[ \t]*")
    for api_file in API_FILES:
        api = open(api_file, 'r')
        for line in api:
            m = pat1.match(line)
            if m:
                def_Type(m.group(1), m.group(2), m.group(3))
    for k in Type2Str:
        v = Type2Str[k]
        if is_obj(k):
            Type2Dotnet[k] = v
            Type2ML[k] = v.lower()

def type2str(ty):
    global Type2Str
    return Type2Str[ty]

def type2pystr(ty):
    global Type2PyStr
    return Type2PyStr[ty]

def type2dotnet(ty):
    global Type2Dotnet
    return Type2Dotnet[ty]

def type2java(ty):
    global Type2Java
    if (ty >= FIRST_OBJ_ID):
        return 'long'
    else:
        return Type2Java[ty]

def type2javaw(ty):
    global Type2JavaW
    if (ty >= FIRST_OBJ_ID):
        return 'jlong'
    else:
        return Type2JavaW[ty]

def type2ml(ty):
    global Type2ML
    return Type2ML[ty]

def _in(ty):
    return (IN, ty)

def _in_array(sz, ty):
    return (IN_ARRAY, ty, sz)

def _out(ty):
    return (OUT, ty)

def _out_array(sz, ty):
    return (OUT_ARRAY, ty, sz, sz)

# cap contains the position of the argument that stores the capacity of the array
# sz  contains the position of the output argument that stores the (real) size of the array
def _out_array2(cap, sz, ty):
    return (OUT_ARRAY, ty, cap, sz)

def _inout_array(sz, ty):
    return (INOUT_ARRAY, ty, sz, sz)

def _out_managed_array(sz,ty):
    return (OUT_MANAGED_ARRAY, ty, 0, sz)


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
    elif k == IN_ARRAY:
        return "[In] %s[]" % type2dotnet(param_type(p))
    elif k == INOUT_ARRAY:
        return "[In, Out] %s[]" % type2dotnet(param_type(p))
    elif k == OUT_ARRAY:
        return "[Out] %s[]" % type2dotnet(param_type(p))
    elif k == OUT_MANAGED_ARRAY:
        return "[Out] out %s[]" % type2dotnet(param_type(p))
    else:
        return type2dotnet(param_type(p))

def param2java(p):
    k = param_kind(p)
    if k == OUT:
        if param_type(p) == INT or param_type(p) == UINT:
            return "IntPtr"
        elif param_type(p) == INT64 or param_type(p) == UINT64 or param_type(p) == VOID_PTR or param_type(p) >= FIRST_OBJ_ID:
            return "LongPtr"
        elif param_type(p) == STRING:
            return "StringPtr"
        else:
            print("ERROR: unreachable code")
            assert(False)
            exit(1)
    elif k == IN_ARRAY or k == INOUT_ARRAY or k == OUT_ARRAY:
        return "%s[]" % type2java(param_type(p))
    elif k == OUT_MANAGED_ARRAY:
        if param_type(p) == UINT:
            return "UIntArrayPtr"
        else:
            return "ObjArrayPtr"
    else:
        return type2java(param_type(p))

def param2javaw(p):
    k = param_kind(p)
    if k == OUT:
        return "jobject"
    elif k == IN_ARRAY or k == INOUT_ARRAY or k == OUT_ARRAY:
        if param_type(p) == INT or param_type(p) == UINT:
            return "jintArray"
        else:
            return "jlongArray"
    elif k == OUT_MANAGED_ARRAY:
        return "jlong"
    else:
        return type2javaw(param_type(p))

def param2pystr(p):
    if param_kind(p) == IN_ARRAY or param_kind(p) == OUT_ARRAY or param_kind(p) == IN_ARRAY or param_kind(p) == INOUT_ARRAY or param_kind(p) == OUT:
        return "ctypes.POINTER(%s)" % type2pystr(param_type(p))
    else:
        return type2pystr(param_type(p))

def param2ml(p):
    k = param_kind(p)
    if k == OUT:
        if param_type(p) == INT or param_type(p) == UINT or param_type(p) == INT64 or param_type(p) == UINT64:
            return "int"
        elif param_type(p) == STRING:
            return "string"
        else:
            return "ptr"
    elif k == IN_ARRAY or k == INOUT_ARRAY or k == OUT_ARRAY:
        return "%s array" % type2ml(param_type(p))
    elif k == OUT_MANAGED_ARRAY:
        return "%s array" % type2ml(param_type(p))
    else:
        return type2ml(param_type(p))

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

def display_args_to_z3(params):
    i = 0
    for p in params:
        if i > 0:
            core_py.write(", ")
        if param_type(p) == STRING:
            core_py.write("_to_ascii(a%s)" % i)
        else:
            core_py.write("a%s" % i)
        i = i + 1

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
        display_args_to_z3(params)
        core_py.write(")\n")
        if len(params) > 0 and param_type(params[0]) == CONTEXT:
            core_py.write("  err = lib().Z3_get_error_code(a0)\n")
            core_py.write("  if err != Z3_OK:\n")
            core_py.write("    raise Z3Exception(lib().Z3_get_error_msg(a0, err))\n")
        if result == STRING:
            core_py.write("  return _to_pystr(r)\n")
        elif result != VOID:
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
    dotnet.write('#pragma warning disable 1591\n\n')
    dotnet.write('namespace Microsoft.Z3\n')
    dotnet.write('{\n')
    for k in Type2Str:
        v = Type2Str[k]
        if is_obj(k):
            dotnet.write('    using %s = System.IntPtr;\n' % v)
    dotnet.write('\n')
    dotnet.write('    public class Native\n')
    dotnet.write('    {\n\n')
    dotnet.write('        [UnmanagedFunctionPointer(CallingConvention.Cdecl)]\n')
    dotnet.write('        public delegate void Z3_error_handler(Z3_context c, Z3_error_code e);\n\n')
    dotnet.write('        public unsafe class LIB\n')
    dotnet.write('        {\n')
    dotnet.write('            const string Z3_DLL_NAME = \"libz3.dll\";\n'
                 '            \n')
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
        i = 0
        for param in params:
            if first:
                first = False
            else:
                dotnet.write(', ')
            dotnet.write('%s a%d' % (param2dotnet(param), i))
            i = i + 1
        dotnet.write(');\n\n')
    dotnet.write('        }\n')


NULLWrapped = [ 'Z3_mk_context', 'Z3_mk_context_rc' ]
Unwrapped = [ 'Z3_del_context', 'Z3_get_error_code' ]

def mk_dotnet_wrappers():
    global Type2Str
    global dotnet_fileout
    dotnet = open(dotnet_fileout, 'a')
    dotnet.write("\n")
    dotnet.write("        public static void Z3_set_error_handler(Z3_context a0, Z3_error_handler a1) {\n")
    dotnet.write("            LIB.Z3_set_error_handler(a0, a1);\n")
    dotnet.write("            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);\n")
    dotnet.write("            if (err != Z3_error_code.Z3_OK)\n")
    dotnet.write("                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg(a0, (uint)err)));\n")
    dotnet.write("        }\n\n")
    for name, result, params in _dotnet_decls:
        if result == STRING:
            dotnet.write('        public static string %s(' % (name))
        else:
            dotnet.write('        public static %s %s(' % (type2dotnet(result), name))
        first = True
        i = 0
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
            dotnet.write('IntPtr r = ')
        elif result != VOID:
            dotnet.write('%s r = ' % type2dotnet(result))
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
                    dotnet.write('out ')
                else:
                    dotnet.write('ref ')
            elif param_kind(param) == OUT_MANAGED_ARRAY:
                dotnet.write('out ')
            dotnet.write('a%d' % i)
            i = i + 1
        dotnet.write(');\n')
        if name not in Unwrapped:
            if name in NULLWrapped:
                dotnet.write("            if (r == IntPtr.Zero)\n")
                dotnet.write("                throw new Z3Exception(\"Object allocation failed.\");\n")
            else:
                if len(params) > 0 and param_type(params[0]) == CONTEXT:
                    dotnet.write("            Z3_error_code err = (Z3_error_code)LIB.Z3_get_error_code(a0);\n")
                    dotnet.write("            if (err != Z3_error_code.Z3_OK)\n")
                    dotnet.write("                throw new Z3Exception(Marshal.PtrToStringAnsi(LIB.Z3_get_error_msg(a0, (uint)err)));\n")
        if result == STRING:
            dotnet.write("            return Marshal.PtrToStringAnsi(r);\n")
        elif result != VOID:
            dotnet.write("            return r;\n")
        dotnet.write("        }\n\n")
    dotnet.write("    }\n\n")
    dotnet.write("}\n\n")

def java_method_name(name):
    result = ''
    name = name[3:] # Remove Z3_
    n = len(name)
    i = 0
    while i < n:
        if name[i] == '_':
            i = i + 1
            if i < n:
                result += name[i].upper()
        else:
            result += name[i]
        i = i + 1
    return result

# Return the type of the java array elements
def java_array_element_type(p):
    if param_type(p) == INT or param_type(p) == UINT:
        return 'jint'
    else:
        return 'jlong'

def mk_java():
    if not is_java_enabled():
        return
    java_dir      = get_component('java').src_dir
    java_nativef  = os.path.join(java_dir, 'Native.java')
    java_wrapperf = os.path.join(java_dir, 'Native.cpp')
    java_native   = open(java_nativef, 'w')
    java_native.write('// Automatically generated file\n')
    java_native.write('package %s;\n' % get_component('java').package_name)
    java_native.write('import %s.enumerations.*;\n' % get_component('java').package_name)
    java_native.write('public final class Native {\n')
    java_native.write('  public static class IntPtr { public int value; }\n')
    java_native.write('  public static class LongPtr { public long value; }\n')
    java_native.write('  public static class StringPtr { public String value; }\n')
    java_native.write('  public static class ObjArrayPtr { public long[] value; }\n')
    java_native.write('  public static class UIntArrayPtr { public int[] value; }\n')
    java_native.write('  public static native void setInternalErrorHandler(long ctx);\n\n')

    java_native.write('  static {\n')
    java_native.write('    try { System.loadLibrary("z3java"); }\n')
    java_native.write('    catch (UnsatisfiedLinkError ex) { System.loadLibrary("libz3java"); }\n')
    java_native.write('  }\n')

    java_native.write('\n')
    for name, result, params in _dotnet_decls:
        java_native.write('  protected static native %s INTERNAL%s(' % (type2java(result), java_method_name(name)))
        first = True
        i = 0
        for param in params:
            if first:
                first = False
            else:
                java_native.write(', ')
            java_native.write('%s a%d' % (param2java(param), i))
            i = i + 1
        java_native.write(');\n')
    java_native.write('\n\n')
    # Exception wrappers
    for name, result, params in _dotnet_decls:
        java_native.write('  public static %s %s(' % (type2java(result), java_method_name(name)))
        first = True
        i = 0
        for param in params:
            if first:
                first = False
            else:
                java_native.write(', ')
            java_native.write('%s a%d' % (param2java(param), i))
            i = i + 1
        java_native.write(')')
        if (len(params) > 0 and param_type(params[0]) == CONTEXT) or name in NULLWrapped:
            java_native.write(' throws Z3Exception')
        java_native.write('\n')
        java_native.write('  {\n')
        java_native.write('      ')
        if result != VOID:
            java_native.write('%s res = ' % type2java(result))
        java_native.write('INTERNAL%s(' % (java_method_name(name)))
        first = True
        i = 0
        for param in params:
            if first:
                first = False
            else:
                java_native.write(', ')
            java_native.write('a%d' % i)
            i = i + 1
        java_native.write(');\n')
        if name not in Unwrapped:
            if name in NULLWrapped:
                java_native.write("      if (res == 0)\n")
                java_native.write("          throw new Z3Exception(\"Object allocation failed.\");\n")
            else:
                if len(params) > 0 and param_type(params[0]) == CONTEXT:
                    java_native.write('      Z3_error_code err = Z3_error_code.fromInt(INTERNALgetErrorCode(a0));\n')
                    java_native.write('      if (err != Z3_error_code.Z3_OK)\n')
                    java_native.write('          throw new Z3Exception(INTERNALgetErrorMsg(a0, err.toInt()));\n')
        if result != VOID:
            java_native.write('      return res;\n')
        java_native.write('  }\n\n')
    java_native.write('}\n')
    java_wrapper = open(java_wrapperf, 'w')
    pkg_str = get_component('java').package_name.replace('.', '_')
    java_wrapper.write('// Automatically generated file\n')
    java_wrapper.write('#ifdef _CYGWIN\n')
    java_wrapper.write('typedef long long __int64;\n')
    java_wrapper.write('#endif\n')
    java_wrapper.write('#include<jni.h>\n')
    java_wrapper.write('#include<stdlib.h>\n')
    java_wrapper.write('#include"z3.h"\n')
    java_wrapper.write('#ifdef __cplusplus\n')
    java_wrapper.write('extern "C" {\n')
    java_wrapper.write('#endif\n\n')
    java_wrapper.write('#ifdef __GNUC__\n#if __GNUC__ >= 4\n#define DLL_VIS __attribute__ ((visibility ("default")))\n#else\n#define DLL_VIS\n#endif\n#else\n#define DLL_VIS\n#endif\n\n')
    java_wrapper.write('#if defined(_M_X64) || defined(_AMD64_)\n\n')
    java_wrapper.write('#define GETLONGAELEMS(T,OLD,NEW)                                   \\\n')
    java_wrapper.write('  T * NEW = (OLD == 0) ? 0 : (T*) jenv->GetLongArrayElements(OLD, NULL);\n')
    java_wrapper.write('#define RELEASELONGAELEMS(OLD,NEW)                                 \\\n')
    java_wrapper.write('  if (OLD != 0) jenv->ReleaseLongArrayElements(OLD, (jlong *) NEW, JNI_ABORT);     \n\n')
    java_wrapper.write('#define GETLONGAREGION(T,OLD,Z,SZ,NEW)                               \\\n')
    java_wrapper.write('  jenv->GetLongArrayRegion(OLD,Z,(jsize)SZ,(jlong*)NEW);             \n')
    java_wrapper.write('#define SETLONGAREGION(OLD,Z,SZ,NEW)                               \\\n')
    java_wrapper.write('  jenv->SetLongArrayRegion(OLD,Z,(jsize)SZ,(jlong*)NEW)              \n\n')
    java_wrapper.write('#else\n\n')
    java_wrapper.write('#define GETLONGAELEMS(T,OLD,NEW)                                   \\\n')
    java_wrapper.write('  T * NEW = 0; {                                                   \\\n')
    java_wrapper.write('  jlong * temp = (OLD == 0) ? 0 : jenv->GetLongArrayElements(OLD, NULL); \\\n')
    java_wrapper.write('  unsigned int size = (OLD == 0) ? 0 :jenv->GetArrayLength(OLD);     \\\n')
    java_wrapper.write('  if (OLD != 0) {                                                    \\\n')
    java_wrapper.write('    NEW = (T*) (new int[size]);                                      \\\n')
    java_wrapper.write('    for (unsigned i=0; i < size; i++)                                \\\n')
    java_wrapper.write('      NEW[i] = reinterpret_cast<T>(temp[i]);                         \\\n')
    java_wrapper.write('    jenv->ReleaseLongArrayElements(OLD, temp, JNI_ABORT);            \\\n')
    java_wrapper.write('  }                                                                  \\\n')
    java_wrapper.write('  }                                                                    \n\n')
    java_wrapper.write('#define RELEASELONGAELEMS(OLD,NEW)                                   \\\n')
    java_wrapper.write('  delete [] NEW;                                                     \n\n')
    java_wrapper.write('#define GETLONGAREGION(T,OLD,Z,SZ,NEW)                              \\\n')
    java_wrapper.write('  {                                                                 \\\n')
    java_wrapper.write('    jlong * temp = new jlong[SZ];                                   \\\n')
    java_wrapper.write('    jenv->GetLongArrayRegion(OLD,Z,(jsize)SZ,(jlong*)temp);         \\\n')
    java_wrapper.write('    for (int i = 0; i < (SZ); i++)                                  \\\n')
    java_wrapper.write('      NEW[i] = reinterpret_cast<T>(temp[i]);                        \\\n')
    java_wrapper.write('    delete [] temp;                                                 \\\n')
    java_wrapper.write('  }\n\n')
    java_wrapper.write('#define SETLONGAREGION(OLD,Z,SZ,NEW)                                \\\n')
    java_wrapper.write('  {                                                                 \\\n')
    java_wrapper.write('    jlong * temp = new jlong[SZ];                                   \\\n')
    java_wrapper.write('    for (int i = 0; i < (SZ); i++)                                  \\\n')
    java_wrapper.write('      temp[i] = reinterpret_cast<jlong>(NEW[i]);                    \\\n')
    java_wrapper.write('    jenv->SetLongArrayRegion(OLD,Z,(jsize)SZ,temp);                 \\\n')
    java_wrapper.write('    delete [] temp;                                                 \\\n')
    java_wrapper.write('  }\n\n')
    java_wrapper.write('#endif\n\n')
    java_wrapper.write('void Z3JavaErrorHandler(Z3_context c, Z3_error_code e)\n')
    java_wrapper.write('{\n')
    java_wrapper.write('  // Internal do-nothing error handler. This is required to avoid that Z3 calls exit()\n')
    java_wrapper.write('  // upon errors, but the actual error handling is done by throwing exceptions in the\n')
    java_wrapper.write('  // wrappers below.\n')
    java_wrapper.write('}\n\n')
    java_wrapper.write('DLL_VIS JNIEXPORT void JNICALL Java_%s_Native_setInternalErrorHandler(JNIEnv * jenv, jclass cls, jlong a0)\n' % pkg_str)
    java_wrapper.write('{\n')
    java_wrapper.write('  Z3_set_error_handler((Z3_context)a0, Z3JavaErrorHandler);\n')
    java_wrapper.write('}\n\n')
    java_wrapper.write('')
    for name, result, params in _dotnet_decls:
        java_wrapper.write('DLL_VIS JNIEXPORT %s JNICALL Java_%s_Native_INTERNAL%s(JNIEnv * jenv, jclass cls' % (type2javaw(result), pkg_str, java_method_name(name)))
        i = 0
        for param in params:
            java_wrapper.write(', ')
            java_wrapper.write('%s a%d' % (param2javaw(param), i))
            i = i + 1
        java_wrapper.write(') {\n')
        # preprocess arrays, strings, in/out arguments
        i = 0
        for param in params:
            k = param_kind(param)
            if k == OUT or k == INOUT:
                java_wrapper.write('  %s _a%s;\n' % (type2str(param_type(param)), i))
            elif k == IN_ARRAY or k == INOUT_ARRAY:
                if param_type(param) == INT or param_type(param) == UINT:
                    java_wrapper.write('  %s * _a%s = (%s*) jenv->GetIntArrayElements(a%s, NULL);\n' % (type2str(param_type(param)), i, type2str(param_type(param)), i))
                else:                    
                    java_wrapper.write('  GETLONGAELEMS(%s, a%s, _a%s);\n' % (type2str(param_type(param)), i, i))
            elif k == OUT_ARRAY:
                java_wrapper.write('  %s * _a%s = (%s *) malloc(((unsigned)a%s) * sizeof(%s));\n' % (type2str(param_type(param)), 
                                                                                                     i, 
                                                                                                     type2str(param_type(param)), 
                                                                                                     param_array_capacity_pos(param), 
                                                                                                     type2str(param_type(param))))
                if param_type(param) == INT or param_type(param) == UINT:
                    java_wrapper.write('  jenv->GetIntArrayRegion(a%s, 0, (jsize)a%s, (jint*)_a%s);\n' % (i, param_array_capacity_pos(param), i))
                else:
                    java_wrapper.write('  GETLONGAREGION(%s, a%s, 0, a%s, _a%s);\n' % (type2str(param_type(param)), i, param_array_capacity_pos(param), i))    
            elif k == IN and param_type(param) == STRING:
                java_wrapper.write('  Z3_string _a%s = (Z3_string) jenv->GetStringUTFChars(a%s, NULL);\n' % (i, i))
            elif k == OUT_MANAGED_ARRAY:
                java_wrapper.write('  %s * _a%s = 0;\n' % (type2str(param_type(param)), i))
            i = i + 1
        # invoke procedure
        java_wrapper.write('  ')
        if result != VOID:
            java_wrapper.write('%s result = ' % type2str(result))
        java_wrapper.write('%s(' % name)
        i = 0
        first = True
        for param in params:
            if first:
                first = False
            else:
                java_wrapper.write(', ')
            k = param_kind(param)
            if k == OUT or k == INOUT:
                java_wrapper.write('&_a%s' % i)
            elif k == OUT_ARRAY or k == IN_ARRAY or k == INOUT_ARRAY:
                java_wrapper.write('_a%s' % i)
            elif k == OUT_MANAGED_ARRAY:
                java_wrapper.write('&_a%s' % i)
            elif k == IN and param_type(param) == STRING:
                java_wrapper.write('_a%s' % i)
            else:
                java_wrapper.write('(%s)a%i' % (param2str(param), i))
            i = i + 1
        java_wrapper.write(');\n')
        # cleanup 
        i = 0
        for param in params:
            k = param_kind(param)
            if k == OUT_ARRAY:
                if param_type(param) == INT or param_type(param) == UINT:
                    java_wrapper.write('  jenv->SetIntArrayRegion(a%s, 0, (jsize)a%s, (jint*)_a%s);\n' % (i, param_array_capacity_pos(param), i))
                else:
                    java_wrapper.write('  SETLONGAREGION(a%s, 0, a%s, _a%s);\n' % (i, param_array_capacity_pos(param), i))
                java_wrapper.write('  free(_a%s);\n' % i)
            elif k == IN_ARRAY or k == OUT_ARRAY:
                if param_type(param) == INT or param_type(param) == UINT:
                    java_wrapper.write('  jenv->ReleaseIntArrayElements(a%s, (jint*)_a%s, JNI_ABORT);\n' % (i, i))
                else:
                    java_wrapper.write('  RELEASELONGAELEMS(a%s, _a%s);\n' % (i, i))

            elif k == OUT or k == INOUT:
                if param_type(param) == INT or param_type(param) == UINT:
                    java_wrapper.write('  {\n')
                    java_wrapper.write('     jclass mc    = jenv->GetObjectClass(a%s);\n' % i)
                    java_wrapper.write('     jfieldID fid = jenv->GetFieldID(mc, "value", "I");\n')
                    java_wrapper.write('     jenv->SetIntField(a%s, fid, (jint) _a%s);\n' % (i, i))
                    java_wrapper.write('  }\n')
                else:
                    java_wrapper.write('  {\n')
                    java_wrapper.write('     jclass mc    = jenv->GetObjectClass(a%s);\n' % i)
                    java_wrapper.write('     jfieldID fid = jenv->GetFieldID(mc, "value", "J");\n')
                    java_wrapper.write('     jenv->SetLongField(a%s, fid, (jlong) _a%s);\n' % (i, i))
                    java_wrapper.write('  }\n')
            elif k == OUT_MANAGED_ARRAY:
                java_wrapper.write('  *(jlong**)a%s = (jlong*)_a%s;\n' % (i, i))
            i = i + 1
        # return
        if result == STRING:
            java_wrapper.write('  return jenv->NewStringUTF(result);\n')
        elif result != VOID:
            java_wrapper.write('  return (%s) result;\n' % type2javaw(result))        
        java_wrapper.write('}\n')
    java_wrapper.write('#ifdef __cplusplus\n')
    java_wrapper.write('}\n')
    java_wrapper.write('#endif\n')
    if is_verbose():
        print("Generated '%s'" % java_nativef)

def mk_log_header(file, name, params):
    file.write("void log_%s(" % name)
    i = 0
    for p in params:
        if i > 0:
            file.write(", ")
        file.write("%s a%s" % (param2str(p), i))
        i = i + 1
    file.write(")")

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
            elif ty == FLOAT:
                log_c.write("  D(a%s);\n" % i)
                exe_c.write("in.get_float(%s)" % i)
            elif ty == BOOL:
                log_c.write("  I(a%s);\n" % i)
                exe_c.write("in.get_bool(%s)" % i)
            elif ty == PRINT_MODE or ty == ERROR_CODE:
                log_c.write("  U(static_cast<unsigned>(a%s));\n" % i)
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
            elif ty == VOID_PTR:
                log_c.write("  P(0);\n")
                exe_c.write("in.get_obj_addr(%s)" % i)
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
            elif ty == INT:
                log_c.write("U(a%s[i]);" % i)
                log_c.write(" }\n")
                log_c.write("  Au(a%s);\n" % sz)
                exe_c.write("in.get_int_array(%s)" % i)
            else:
                error ("unsupported parameter for %s, %s" % (ty, name, p))
        elif kind == OUT_ARRAY:
            sz   = param_array_capacity_pos(p)
            sz_p = params[sz]            
            sz_p_k = param_kind(sz_p)
            tstr = type2str(ty)
            if sz_p_k == OUT or sz_p_k == INOUT:
                sz_e = ("(*a%s)" % sz)
            else:
                sz_e = ("a%s" % sz)
            log_c.write("  for (unsigned i = 0; i < %s; i++) { " % sz_e)
            if is_obj(ty):
                log_c.write("P(0);")
                log_c.write(" }\n")
                log_c.write("  Ap(%s);\n" % sz_e)
                exe_c.write("reinterpret_cast<%s*>(in.get_obj_array(%s))" % (tstr, i))
            elif ty == UINT:
                log_c.write("U(0);")
                log_c.write(" }\n")
                log_c.write("  Au(%s);\n" % sz_e)
                exe_c.write("in.get_uint_array(%s)" % i)
            else:
                error ("unsupported parameter for %s, %s" % (name, p))
        elif kind == OUT_MANAGED_ARRAY:
            sz   = param_array_size_pos(p)
            sz_p = params[sz]
            sz_p_k = param_kind(sz_p)
            tstr = type2str(ty)
            if sz_p_k == OUT or sz_p_k == INOUT:
                sz_e = ("(*a%s)" % sz)
            else:
                sz_e = ("a%s" % sz)
            log_c.write("  for (unsigned i = 0; i < %s; i++) { " % sz_e)
            log_c.write("P(0);")
            log_c.write(" }\n")
            log_c.write("  Ap(%s);\n" % sz_e)
            exe_c.write("reinterpret_cast<%s**>(in.get_obj_array(%s))" % (tstr, i))
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

def ml_method_name(name):
    return name[3:] # Remove Z3_

def is_out_param(p):
    if param_kind(p) == OUT or param_kind(p) == INOUT or param_kind(p) == OUT_ARRAY or param_kind(p) == INOUT_ARRAY or param_kind(p) == OUT_MANAGED_ARRAY:
        return True
    else:
        return False

def outparams(params):
    op = []
    for param in params:
        if is_out_param(param):
            op.append(param)
    return op

def is_in_param(p):
    if param_kind(p) == IN or param_kind(p) == INOUT or param_kind(p) == IN_ARRAY or param_kind(p) == INOUT_ARRAY:
        return True
    else:
        return False

def inparams(params):
    ip = []
    for param in params:
        if is_in_param(param):
            ip.append(param)
    return ip

def is_array_param(p):
    if param_kind(p) == IN_ARRAY or param_kind(p) == INOUT_ARRAY or param_kind(p) == OUT_ARRAY:
        return True
    else:
        return False

def arrayparams(params):
    op = []
    for param in params:
        if is_array_param(param):
            op.append(param)
    return op


def ml_unwrap(t, ts, s):
    if t == STRING:
        return '(' + ts + ') String_val(' + s + ')'
    elif t == BOOL:
        return '(' + ts + ') Bool_val(' + s + ')'
    elif t == INT or t == PRINT_MODE or t == ERROR_CODE:
        return '(' + ts + ') Int_val(' + s + ')'
    elif t == UINT:
        return '(' + ts + ') Unsigned_int_val(' + s + ')'
    elif t == INT64:
        return '(' + ts + ') Long_val(' + s + ')'
    elif t == UINT64:
        return '(' + ts + ') Unsigned_long_val(' + s + ')'
    elif t == DOUBLE:
        return '(' + ts + ') Double_val(' + s + ')'
    else:
        return '* (' + ts + '*) Data_custom_val(' + s + ')'

def ml_set_wrap(t, d, n):
    if t == VOID:
        return d + ' = Val_unit;'
    elif t == BOOL:
        return d + ' = Val_bool(' + n + ');'
    elif t == INT or t == UINT or t == PRINT_MODE or t == ERROR_CODE:
        return d + ' = Val_int(' + n + ');'
    elif t == INT64 or t == UINT64:
        return d + ' = Val_long(' + n + ');'
    elif t == DOUBLE:
        return 'Store_double_val(' + d + ', ' + n + ');'
    elif t == STRING:
        return d + ' = caml_copy_string((const char*) ' + n + ');'
    else:
        ts = type2str(t)
        return d + ' = caml_alloc_custom(&default_custom_ops, sizeof(' + ts + '), 0, 1); memcpy( Data_custom_val(' + d + '), &' + n + ', sizeof(' + ts + '));'

def mk_ml():
    global Type2Str
    if not is_ml_enabled():
        return
    ml_dir      = get_component('ml').src_dir
    ml_nativef  = os.path.join(ml_dir, 'z3native.ml')
    ml_nativefi = os.path.join(ml_dir, 'z3native.mli')
    ml_wrapperf = os.path.join(ml_dir, 'z3native_stubs.c')
    ml_native   = open(ml_nativef, 'w')
    ml_i        = open(ml_nativefi, 'w')
    ml_native.write('(* Automatically generated file *)\n\n')
    ml_native.write('(** The native (raw) interface to the dynamic Z3 library. *)\n\n')
    ml_i.write('(* Automatically generated file *)\n\n')
    ml_i.write('(** The native (raw) interface to the dynamic Z3 library. *)\n\n')
    ml_i.write('(**/**)\n\n')
    ml_native.write('open Z3enums\n\n')
    ml_native.write('(**/**)\n')
    ml_native.write('type ptr\n')
    ml_i.write('type ptr\n')
    ml_native.write('and z3_symbol = ptr\n')
    ml_i.write('and z3_symbol = ptr\n')
    for k, v in Type2Str.items():
        if is_obj(k):
            ml_native.write('and %s = ptr\n' % v.lower())
            ml_i.write('and %s = ptr\n' % v.lower())
    ml_native.write('\n')
    ml_i.write('\n')
    ml_native.write('external is_null : ptr -> bool\n  = "n_is_null"\n\n')
    ml_native.write('external mk_null : unit -> ptr\n  = "n_mk_null"\n\n')
    ml_native.write('external set_internal_error_handler : ptr -> unit\n  = "n_set_internal_error_handler"\n\n')
    ml_native.write('exception Exception of string\n\n')
    ml_i.write('val is_null : ptr -> bool\n')
    ml_i.write('val mk_null : unit -> ptr\n')
    ml_i.write('val set_internal_error_handler : ptr -> unit\n\n')
    ml_i.write('exception Exception of string\n\n')

    # ML declarations
    ml_native.write('module ML2C = struct\n\n')
    for name, result, params in _dotnet_decls:
        ml_native.write('    external n_%s : ' % ml_method_name(name))
        ml_i.write('val %s : ' % ml_method_name(name))
        ip = inparams(params)
        op = outparams(params)
        if len(ip) == 0:
            ml_native.write(' unit -> ')
            ml_i.write(' unit -> ')
        for p in ip:
            ml_native.write('%s -> ' % param2ml(p))
            ml_i.write('%s -> ' % param2ml(p))
        if len(op) > 0:
            ml_native.write('(')
            ml_i.write('(')
        first = True
        if result != VOID or len(op) == 0:
            ml_native.write('%s' % type2ml(result))
            ml_i.write('%s' % type2ml(result))
            first = False
        for p in op:
            if first:
                first = False
            else:
                ml_native.write(' * ')
                ml_i.write(' * ')
            ml_native.write('%s' % param2ml(p))
            ml_i.write('%s' % param2ml(p))
        if len(op) > 0:
            ml_native.write(')')
            ml_i.write(')')
        ml_native.write('\n')
        ml_i.write('\n')
        if len(ip) > 5:
            ml_native.write('      = "n_%s_bytecode"\n' % ml_method_name(name))
            ml_native.write('        "n_%s"\n' % ml_method_name(name))
        else:
            ml_native.write('      = "n_%s"\n' % ml_method_name(name))
        ml_native.write('\n')
    ml_native.write('  end\n\n')
    ml_i.write('\n(**/**)\n')

    # Exception wrappers
    for name, result, params in _dotnet_decls:
        ip = inparams(params)
        op = outparams(params)
        ml_native.write('  let %s ' % ml_method_name(name))

        first = True
        i = 0
        for p in params:
            if is_in_param(p):
                if first:
                    first = False
                else:
                    ml_native.write(' ')
                ml_native.write('a%d' % i)
            i = i + 1
        if len(ip) == 0:
            ml_native.write('()')
        ml_native.write(' = \n')
        ml_native.write('    ')
        if result == VOID and len(op) == 0:
            ml_native.write('let _ = ')
        else:
            ml_native.write('let res = ')
        ml_native.write('(ML2C.n_%s' % (ml_method_name(name)))
        if len(ip) == 0:
            ml_native.write(' ()')
        first = True
        i = 0
        for p in params:
            if is_in_param(p):
                ml_native.write(' a%d' % i)
            i = i + 1
        ml_native.write(') in\n')
        if name not in Unwrapped and len(params) > 0 and param_type(params[0]) == CONTEXT:
            ml_native.write('    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in \n')
            ml_native.write('      if err <> OK then\n')
            ml_native.write('        raise (Exception (ML2C.n_get_error_msg a0 (int_of_error_code err)))\n')
            ml_native.write('      else\n')
        if result == VOID and len(op) == 0:
            ml_native.write('        ()\n')
        else:
            ml_native.write('        res\n')
        ml_native.write('\n')
    ml_native.write('(**/**)\n')

    # C interface
    ml_wrapper = open(ml_wrapperf, 'w')
    ml_wrapper.write('// Automatically generated file\n\n')
    ml_wrapper.write('#include <stddef.h>\n')
    ml_wrapper.write('#include <string.h>\n\n')
    ml_wrapper.write('#ifdef __cplusplus\n')
    ml_wrapper.write('extern "C" {\n')
    ml_wrapper.write('#endif\n')
    ml_wrapper.write('#include <caml/mlvalues.h>\n')
    ml_wrapper.write('#include <caml/memory.h>\n')
    ml_wrapper.write('#include <caml/alloc.h>\n')
    ml_wrapper.write('#include <caml/fail.h>\n')
    ml_wrapper.write('#include <caml/callback.h>\n')
    ml_wrapper.write('#ifdef Custom_tag\n')
    ml_wrapper.write('#include <caml/custom.h>\n')
    ml_wrapper.write('#include <caml/bigarray.h>\n')
    ml_wrapper.write('#endif\n')
    ml_wrapper.write('#ifdef __cplusplus\n')
    ml_wrapper.write('}\n')
    ml_wrapper.write('#endif\n\n')
    ml_wrapper.write('#include <z3.h>\n')
    ml_wrapper.write('#include <z3native_stubs.h>\n\n')
    ml_wrapper.write('#define CAMLlocal6(X1,X2,X3,X4,X5,X6)                               \\\n')
    ml_wrapper.write('  CAMLlocal5(X1,X2,X3,X4,X5);                                       \\\n')
    ml_wrapper.write('  CAMLlocal1(X6)                                                      \n')
    ml_wrapper.write('#define CAMLlocal7(X1,X2,X3,X4,X5,X6,X7)                            \\\n')
    ml_wrapper.write('  CAMLlocal5(X1,X2,X3,X4,X5);                                       \\\n')
    ml_wrapper.write('  CAMLlocal2(X6,X7)                                                   \n')
    ml_wrapper.write('#define CAMLlocal8(X1,X2,X3,X4,X5,X6,X7,X8)                         \\\n')
    ml_wrapper.write('  CAMLlocal5(X1,X2,X3,X4,X5);                                       \\\n')
    ml_wrapper.write('  CAMLlocal3(X6,X7,X8)                                                \n')
    ml_wrapper.write('\n')
    ml_wrapper.write('#define CAMLparam7(X1,X2,X3,X4,X5,X6,X7)                            \\\n')
    ml_wrapper.write('  CAMLparam5(X1,X2,X3,X4,X5);                                       \\\n')
    ml_wrapper.write('  CAMLxparam2(X6,X7)                                                  \n')
    ml_wrapper.write('#define CAMLparam8(X1,X2,X3,X4,X5,X6,X7,X8)                         \\\n')
    ml_wrapper.write('  CAMLparam5(X1,X2,X3,X4,X5);                                       \\\n')
    ml_wrapper.write('  CAMLxparam3(X6,X7,X8)                                               \n')
    ml_wrapper.write('#define CAMLparam9(X1,X2,X3,X4,X5,X6,X7,X8,X9)                      \\\n')
    ml_wrapper.write('  CAMLparam5(X1,X2,X3,X4,X5);                                       \\\n')
    ml_wrapper.write('  CAMLxparam4(X6,X7,X8,X9)                                            \n')
    ml_wrapper.write('#define CAMLparam12(X1,X2,X3,X4,X5,X6,X7,X8,X9,X10,X11,X12)         \\\n')
    ml_wrapper.write('  CAMLparam5(X1,X2,X3,X4,X5);                                       \\\n')
    ml_wrapper.write('  CAMLxparam5(X6,X7,X8,X9,X10);                                     \\\n')
    ml_wrapper.write('  CAMLxparam2(X11,X12)                                                \n')
    ml_wrapper.write('#define CAMLparam13(X1,X2,X3,X4,X5,X6,X7,X8,X9,X10,X11,X12,X13)     \\\n')
    ml_wrapper.write('  CAMLparam5(X1,X2,X3,X4,X5);                                       \\\n')
    ml_wrapper.write('  CAMLxparam5(X6,X7,X8,X9,X10);                                     \\\n')
    ml_wrapper.write('  CAMLxparam3(X11,X12,X13)                                            \n')
    ml_wrapper.write('\n\n')
    ml_wrapper.write('static struct custom_operations default_custom_ops = {\n')
    ml_wrapper.write('  (char*) "default handling",\n')
    ml_wrapper.write('  custom_finalize_default,\n')
    ml_wrapper.write('  custom_compare_default,\n')
    ml_wrapper.write('  custom_hash_default,\n')
    ml_wrapper.write('  custom_serialize_default,\n')
    ml_wrapper.write('  custom_deserialize_default\n')
    ml_wrapper.write('};\n\n')
    ml_wrapper.write('#ifdef __cplusplus\n')
    ml_wrapper.write('extern "C" {\n')
    ml_wrapper.write('#endif\n\n')
    ml_wrapper.write('CAMLprim DLL_PUBLIC value n_is_null(value p) {\n')
    ml_wrapper.write('  void * t = * (void**) Data_custom_val(p);\n')
    ml_wrapper.write('  return Val_bool(t == 0);\n')
    ml_wrapper.write('}\n\n')
    ml_wrapper.write('CAMLprim DLL_PUBLIC value n_mk_null( void ) {\n')
    ml_wrapper.write('  CAMLparam0();\n')
    ml_wrapper.write('  CAMLlocal1(result);\n')
    ml_wrapper.write('  void * z3_result = 0;\n')
    ml_wrapper.write('  result = caml_alloc_custom(&default_custom_ops, sizeof(void*), 0, 1);\n')
    ml_wrapper.write('  memcpy( Data_custom_val(result), &z3_result, sizeof(void*));\n')
    ml_wrapper.write('  CAMLreturn (result);\n')
    ml_wrapper.write('}\n\n')
    ml_wrapper.write('void MLErrorHandler(Z3_context c, Z3_error_code e)\n')
    ml_wrapper.write('{\n')
    ml_wrapper.write('  // Internal do-nothing error handler. This is required to avoid that Z3 calls exit()\n')
    ml_wrapper.write('  // upon errors, but the actual error handling is done by throwing exceptions in the\n')
    ml_wrapper.write('  // wrappers below.\n')
    ml_wrapper.write('}\n\n')
    ml_wrapper.write('void DLL_PUBLIC n_set_internal_error_handler(value a0)\n')
    ml_wrapper.write('{\n')
    ml_wrapper.write('  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);\n')
    ml_wrapper.write('  Z3_set_error_handler(_a0, MLErrorHandler);\n')
    ml_wrapper.write('}\n\n')
    for name, result, params in _dotnet_decls:
        ip = inparams(params)
        op = outparams(params)
        ap = arrayparams(params)
        ret_size = len(op)
        if result != VOID:
            ret_size = ret_size + 1
            
        # Setup frame
        ml_wrapper.write('CAMLprim DLL_PUBLIC value n_%s(' % ml_method_name(name)) 
        first = True
        i = 0
        for p in params:
            if is_in_param(p):
                if first:
                    first = False
                else:                
                    ml_wrapper.write(', ')
                ml_wrapper.write('value a%d' % i)
            i = i + 1
        ml_wrapper.write(') {\n')
        ml_wrapper.write('  CAMLparam%d(' % len(ip))
        i = 0
        first = True
        for p in params:
            if is_in_param(p):
                if first:
                    first = False
                else:
                    ml_wrapper.write(', ')
                ml_wrapper.write('a%d' % i)
            i = i + 1
        ml_wrapper.write(');\n')
        i = 0
        if len(op) + len(ap) == 0:
            ml_wrapper.write('  CAMLlocal1(result);\n')
        else:
            c = 0
            for p in params:
                if is_out_param(p) or is_array_param(p):
                    c = c + 1
            ml_wrapper.write('  CAMLlocal%s(result, res_val' % (c+2))
            for p in params:
                if is_out_param(p) or is_array_param(p):
                    ml_wrapper.write(', _a%s_val' % i)
                i = i + 1
            ml_wrapper.write(');\n')

        if len(ap) != 0:
            ml_wrapper.write('  unsigned _i;\n')

        # declare locals, preprocess arrays, strings, in/out arguments
        i = 0
        for param in params:
            k = param_kind(param)
            if k == OUT_ARRAY:
                ml_wrapper.write('  %s * _a%s = (%s*) malloc(sizeof(%s) * (_a%s));\n' % (
                        type2str(param_type(param)),
                        i, 
                        type2str(param_type(param)),
                        type2str(param_type(param)),
                        param_array_capacity_pos(param)))
            elif k == OUT_MANAGED_ARRAY:
                ml_wrapper.write('  %s * _a%s = 0;\n' % (type2str(param_type(param)), i))
            elif k == IN_ARRAY or k == INOUT_ARRAY:
                t = param_type(param)
                ts = type2str(t)
                ml_wrapper.write('  %s * _a%s = (%s*) malloc(sizeof(%s) * _a%s);\n' % (ts, i, ts, ts, param_array_capacity_pos(param)))                
            elif k == IN:
                t = param_type(param)
                ml_wrapper.write('  %s _a%s = %s;\n' % (type2str(t), i, ml_unwrap(t, type2str(t), 'a' + str(i))))
            elif k == OUT:
                ml_wrapper.write('  %s _a%s;\n' % (type2str(param_type(param)), i))
            elif k == INOUT:
                ml_wrapper.write('  %s _a%s = a%s;\n' % (type2str(param_type(param)), i, i))                
            i = i + 1

        if result != VOID:
            ml_wrapper.write('  %s z3_result;\n' % type2str(result))

        i = 0
        for param in params:
            k = param_kind(param)
            if k == IN_ARRAY or k == INOUT_ARRAY:
                t = param_type(param)
                ts = type2str(t)
                ml_wrapper.write('  for (_i = 0; _i < _a%s; _i++) { _a%s[_i] = %s; }\n' % (param_array_capacity_pos(param), i, ml_unwrap(t, ts, 'Field(a' + str(i) + ', _i)')))
            i = i + 1

        # invoke procedure
        ml_wrapper.write('  ')
        if result != VOID:
            ml_wrapper.write('z3_result = ')
        ml_wrapper.write('%s(' % name)
        i = 0
        first = True
        for param in params:
            if first:
                first = False
            else:
                ml_wrapper.write(', ')
            k = param_kind(param)
            if k == OUT or k == INOUT or k == OUT_MANAGED_ARRAY:
                ml_wrapper.write('&_a%s' %  i)
            else:
                ml_wrapper.write('_a%i' % i)
            i = i + 1
        ml_wrapper.write(');\n')

        # convert output params
        if len(op) > 0:
            if result != VOID:
                ml_wrapper.write('  %s\n' % ml_set_wrap(result, "res_val", "z3_result"))
            i = 0
            for p in params:
                if param_kind(p) == OUT_ARRAY or param_kind(p) == INOUT_ARRAY:
                    ml_wrapper.write('  _a%s_val = caml_alloc(_a%s, 0);\n' % (i, param_array_capacity_pos(p)))
                    ml_wrapper.write('  for (_i = 0; _i < _a%s; _i++) { value t; %s Store_field(_a%s_val, _i, t); }\n' % (param_array_capacity_pos(p), ml_set_wrap(param_type(p), 't', '_a' + str(i) + '[_i]'), i))
                elif param_kind(p) == OUT_MANAGED_ARRAY:
                    ml_wrapper.write('  %s\n' % ml_set_wrap(param_type(p), "_a" + str(i) + "_val", "_a"  + str(i) ))
                elif is_out_param(p):
                    ml_wrapper.write('  %s\n' % ml_set_wrap(param_type(p), "_a" + str(i) + "_val", "_a"  + str(i) ))
                i = i + 1

        # return tuples                
        if len(op) == 0:
            ml_wrapper.write('  %s\n' % ml_set_wrap(result, "result", "z3_result"))
        else:
            ml_wrapper.write('  result = caml_alloc(%s, 0);\n' % ret_size)
            i = j = 0
            if result != VOID:
                ml_wrapper.write('  Store_field(result, 0, res_val);\n')
                j = j + 1
            for p in params:
                if is_out_param(p):
                    ml_wrapper.write('  Store_field(result, %s, _a%s_val);\n' % (j, i))
                    j = j + 1
                i = i + 1

        # local array cleanup
        i = 0
        for p in params:
            k = param_kind(p)
            if k == OUT_ARRAY or k == IN_ARRAY or k == INOUT_ARRAY:
                ml_wrapper.write('  free(_a%s);\n' % i)
            i = i + 1

        # return
        ml_wrapper.write('  CAMLreturn(result);\n')
        ml_wrapper.write('}\n\n')
        if len(ip) > 5:
            ml_wrapper.write('CAMLprim DLL_PUBLIC value n_%s_bytecode(value * argv, int argn) {\n' % ml_method_name(name)) 
            ml_wrapper.write('  return n_%s(' % ml_method_name(name))
            i = 0
            while i < len(ip):
                if i == 0:
                    ml_wrapper.write('argv[0]')
                else:
                    ml_wrapper.write(', argv[%s]' % i)
                i = i + 1
            ml_wrapper.write(');\n}\n')
            ml_wrapper.write('\n\n')
    ml_wrapper.write('#ifdef __cplusplus\n')
    ml_wrapper.write('}\n')
    ml_wrapper.write('#endif\n')
    if is_verbose():
        print ('Generated "%s"' % ml_nativef)

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
mk_java()
mk_ml()

log_h.close()
log_c.close()
exe_c.close()
core_py.close()

if is_verbose():
    print("Generated '%s'" % os.path.join(api_dir, 'api_log_macros.h'))
    print("Generated '%s'" % os.path.join(api_dir, 'api_log_macros.cpp'))
    print("Generated '%s'" % os.path.join(api_dir, 'api_commands.cpp'))
    print("Generated '%s'" % os.path.join(get_z3py_dir(), 'z3core.py'))
    print("Generated '%s'" % os.path.join(dotnet_dir, 'Native.cs'))
