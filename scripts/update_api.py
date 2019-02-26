#!/usr/bin/env python
############################################
# Copyright (c) 2012 Microsoft Corporation
#
# Scripts for generating Makefiles and Visual
# Studio project files.
#
# Author: Leonardo de Moura (leonardo)
############################################
"""
This script generates the ``api_log_macros.h``,
``api_log_macros.cpp`` and ``api_commands.cpp``
files for the "api" module based on parsing
several API header files. It can also optionally
emit some of the files required for Z3's different
language bindings.
"""
import mk_util
import mk_exception
import argparse
import logging
import re
import os
import sys

##########################################################
# TODO: rewrite this file without using global variables.
# This file is a big HACK.
# It started as small simple script.
# Now, it is too big, and is invoked from mk_make.py
#
##########################################################

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

Type2Str = { VOID : 'void', VOID_PTR : 'void*', INT : 'int', UINT : 'unsigned', INT64 : 'int64_t', UINT64 : 'uint64_t', DOUBLE : 'double',
             FLOAT : 'float', STRING : 'Z3_string', STRING_PTR : 'Z3_string_ptr', BOOL : 'bool', SYMBOL : 'Z3_symbol',
             PRINT_MODE : 'Z3_ast_print_mode', ERROR_CODE : 'Z3_error_code'
             }

Type2PyStr = { VOID_PTR : 'ctypes.c_void_p', INT : 'ctypes.c_int', UINT : 'ctypes.c_uint', INT64 : 'ctypes.c_longlong',
               UINT64 : 'ctypes.c_ulonglong', DOUBLE : 'ctypes.c_double', FLOAT : 'ctypes.c_float',
               STRING : 'ctypes.c_char_p', STRING_PTR : 'ctypes.POINTER(ctypes.c_char_p)', BOOL : 'ctypes.c_bool', SYMBOL : 'Symbol',
               PRINT_MODE : 'ctypes.c_uint', ERROR_CODE : 'ctypes.c_uint'
               }

# Mapping to .NET types
Type2Dotnet = { VOID : 'void', VOID_PTR : 'IntPtr', INT : 'int', UINT : 'uint', INT64 : 'Int64', UINT64 : 'UInt64', DOUBLE : 'double',
                FLOAT : 'float', STRING : 'string', STRING_PTR : 'byte**', BOOL : 'byte', SYMBOL : 'IntPtr',
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
    Type2Str[next_type_id] = c_type
    Type2PyStr[next_type_id] = py_type
    next_type_id    = next_type_id + 1

def def_Types(api_files):
    pat1 = re.compile(" *def_Type\(\'(.*)\',[^\']*\'(.*)\',[^\']*\'(.*)\'\)[ \t]*")
    for api_file in api_files:
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
    q = Type2ML[ty]
    if q[0:3] == 'z3_':
        return q[3:]
    else:
        return q;

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
        if param_type(p) == INT or param_type(p) == UINT or param_type(p) == BOOL:
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
        if param_type(p) == INT or param_type(p) == UINT or param_type(p) == BOOL or param_type(p) == INT64 or param_type(p) == UINT64:
            return "int"
        elif param_type(p) == STRING:
            return "string"
        else:
            return "ptr"
    elif k == IN_ARRAY or k == INOUT_ARRAY or k == OUT_ARRAY:
        return "%s list" % type2ml(param_type(p))
    elif k == OUT_MANAGED_ARRAY:
        return "%s list" % type2ml(param_type(p))
    else:
        return type2ml(param_type(p))

# Save name, result, params to generate wrapper
_API2PY = []

def mk_py_binding(name, result, params):
    global core_py
    global _API2PY
    _API2PY.append((name, result, params))
    if result != VOID:
        core_py.write("_lib.%s.restype = %s\n" % (name, type2pystr(result)))
    core_py.write("_lib.%s.argtypes = [" % name)
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

NULLWrapped = [ 'Z3_mk_context', 'Z3_mk_context_rc' ]
Unwrapped = [ 'Z3_del_context', 'Z3_get_error_code' ]

def mk_py_wrappers():
    core_py.write("""
class Elementaries:
  def __init__(self, f):
    self.f = f
    self.get_error_code = _lib.Z3_get_error_code
    self.get_error_message = _lib.Z3_get_error_msg
    self.OK = Z3_OK
    self.Exception = Z3Exception

  def Check(self, ctx):
    err = self.get_error_code(ctx)
    if err != self.OK:
        raise self.Exception(self.get_error_message(ctx, err))

def Z3_set_error_handler(ctx, hndlr, _elems=Elementaries(_lib.Z3_set_error_handler)):
  ceh = _error_handler_type(hndlr)
  _elems.f(ctx, ceh)
  _elems.Check(ctx)
  return ceh

""")

    for sig in _API2PY:
        mk_py_wrapper_single(sig)
        if sig[1] == STRING:
            mk_py_wrapper_single(sig, decode_string=False)

def mk_py_wrapper_single(sig, decode_string=True):
    name    = sig[0]
    result  = sig[1]
    params  = sig[2]
    num     = len(params)
    def_name = name
    if not decode_string:
        def_name += '_bytes'
    core_py.write("def %s(" % def_name)
    display_args(num)
    comma = ", " if num != 0 else ""
    core_py.write("%s_elems=Elementaries(_lib.%s)):\n" % (comma, name))
    lval = "r = " if result != VOID else ""
    core_py.write("  %s_elems.f(" % lval)
    display_args_to_z3(params)
    core_py.write(")\n")
    if len(params) > 0 and param_type(params[0]) == CONTEXT and not name in Unwrapped:
        core_py.write("  _elems.Check(a0)\n")
    if result == STRING and decode_string:
        core_py.write("  return _to_pystr(r)\n")
    elif result != VOID:
        core_py.write("  return r\n")
    core_py.write("\n")


## .NET API native interface
_dotnet_decls = []
def reg_dotnet(name, result, params):
    global _dotnet_decls
    _dotnet_decls.append((name, result, params))

def mk_dotnet(dotnet):
    global Type2Str
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
    dotnet.write('        public class LIB\n')
    dotnet.write('        {\n')
    dotnet.write('            const string Z3_DLL_NAME = \"libz3\";\n'
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

def mk_dotnet_wrappers(dotnet):
    global Type2Str
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
    if param_type(p) == INT or param_type(p) == UINT or param_type(p) == BOOL:
        return 'jint'
    else:
        return 'jlong'

def mk_java(java_dir, package_name):
    java_nativef  = os.path.join(java_dir, 'Native.java')
    java_wrapperf = os.path.join(java_dir, 'Native.cpp')
    java_native   = open(java_nativef, 'w')
    java_native.write('// Automatically generated file\n')
    java_native.write('package %s;\n' % package_name)
    java_native.write('import %s.enumerations.*;\n' % package_name)
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
    pkg_str = package_name.replace('.', '_')
    java_wrapper.write('// Automatically generated file\n')
    java_wrapper.write('#include<jni.h>\n')
    java_wrapper.write('#include<stdlib.h>\n')
    java_wrapper.write('#include"z3.h"\n')
    java_wrapper.write('#ifdef __cplusplus\n')
    java_wrapper.write('extern "C" {\n')
    java_wrapper.write('#endif\n\n')
    java_wrapper.write('#ifdef __GNUC__\n#if __GNUC__ >= 4\n#define DLL_VIS __attribute__ ((visibility ("default")))\n#else\n#define DLL_VIS\n#endif\n#else\n#define DLL_VIS\n#endif\n\n')
    java_wrapper.write('#if defined(__LP64__) || defined(_WIN64)\n\n')
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
                if param_type(param) == INT or param_type(param) == UINT or param_type(param) == BOOL:
                    java_wrapper.write('  %s * _a%s = (%s*) jenv->GetIntArrayElements(a%s, NULL);\n' % (type2str(param_type(param)), i, type2str(param_type(param)), i))
                else:
                    java_wrapper.write('  GETLONGAELEMS(%s, a%s, _a%s);\n' % (type2str(param_type(param)), i, i))
            elif k == OUT_ARRAY:
                java_wrapper.write('  %s * _a%s = (%s *) malloc(((unsigned)a%s) * sizeof(%s));\n' % (type2str(param_type(param)),
                                                                                                     i,
                                                                                                     type2str(param_type(param)),
                                                                                                     param_array_capacity_pos(param),
                                                                                                     type2str(param_type(param))))
                if param_type(param) == INT or param_type(param) == UINT or param_type(param) == BOOL:
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
                if param_type(param) == INT or param_type(param) == UINT or param_type(param) == BOOL:
                    java_wrapper.write('  jenv->SetIntArrayRegion(a%s, 0, (jsize)a%s, (jint*)_a%s);\n' % (i, param_array_capacity_pos(param), i))
                else:
                    java_wrapper.write('  SETLONGAREGION(a%s, 0, a%s, _a%s);\n' % (i, param_array_capacity_pos(param), i))
                java_wrapper.write('  free(_a%s);\n' % i)
            elif k == IN_ARRAY or k == OUT_ARRAY:
                if param_type(param) == INT or param_type(param) == UINT or param_type(param) == BOOL:
                    java_wrapper.write('  jenv->ReleaseIntArrayElements(a%s, (jint*)_a%s, JNI_ABORT);\n' % (i, i))
                else:
                    java_wrapper.write('  RELEASELONGAELEMS(a%s, _a%s);\n' % (i, i))

            elif k == OUT or k == INOUT:
                if param_type(param) == INT or param_type(param) == UINT or param_type(param) == BOOL:
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

            elif k == IN and param_type(param) == STRING:
                java_wrapper.write('  jenv->ReleaseStringUTFChars(a%s, _a%s);\n' % (i, i));
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
    if mk_util.is_verbose():
        print("Generated '%s'" % java_nativef)


Type2Napi = { VOID : '', VOID_PTR : '', INT : 'number', UINT : 'number', INT64 : 'number', UINT64 : 'number', DOUBLE : 'number',
            FLOAT : 'number', STRING : 'string', STRING_PTR : 'array',
            BOOL : 'number', SYMBOL : 'external', PRINT_MODE : 'number', ERROR_CODE : 'number' }

def type2napi(t):
    try:
       return Type2Napi[t]
    except:
       return "external"

Type2NapiBuilder = { VOID : '', VOID_PTR : '', INT : 'int32', UINT : 'uint32', INT64 : 'int64', UINT64 : 'uint64', DOUBLE : 'double',
            FLOAT : 'float', STRING : 'string', STRING_PTR : 'array',
            BOOL : 'bool', SYMBOL : 'external', PRINT_MODE : 'int32', ERROR_CODE : 'int32' }

def type2napibuilder(t):
    try:
       return Type2NapiBuilder[t]
    except:
       return "external"


def mk_js(js_output_dir):
    with open(os.path.join(js_output_dir, "z3.json"), 'w') as ous:
       ous.write("{\n")
       ous.write("  \"api\": [\n")
       for name, result, params in _dotnet_decls:
           ous.write("    {\n")
           ous.write("       \"name\": \"%s\",\n" % name)
           ous.write("       \"c_type\": \"%s\",\n" % Type2Str[result])
           ous.write("       \"napi_type\": \"%s\",\n" % type2napi(result))                       
           ous.write("       \"arg_list\": [")
           first = True
           for p in params:
               if first:
                  first = False
                  ous.write("\n         {\n")
               else:
                  ous.write(",\n         {\n")
               t = param_type(p)
               k = t
               ous.write("            \"name\": \"%s\",\n" % "")                        # TBD
               ous.write("            \"c_type\": \"%s\",\n" % type2str(t))
               ous.write("            \"napi_type\": \"%s\",\n" % type2napi(t))        
               ous.write("            \"napi_builder\": \"%s\"\n" % type2napibuilder(t))
               ous.write(  "         }")
           ous.write("],\n")
           ous.write("       \"napi_builder\": \"%s\"\n" % type2napibuilder(result))
           ous.write("    },\n")
       ous.write("  ]\n")
       ous.write("}\n")


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
                    file.write("unsigned _Z3_UNUSED Z3ARG%s = 0; " % cap)
                sz  = param_array_size_pos(p)
                if sz not in auxs:
                    auxs.add(sz)
                    file.write("unsigned * _Z3_UNUSED Z3ARG%s = 0; " % sz)
            file.write("%s _Z3_UNUSED Z3ARG%s = 0; " % (param2str(p), i))
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
                log_c.write("I(a%s[i]);" % i)
                log_c.write(" }\n")
                log_c.write("  Ai(a%s);\n" % sz)
                exe_c.write("in.get_int_array(%s)" % i)
            elif ty == BOOL:
                log_c.write("U(a%s[i]);" % i)
                log_c.write(" }\n")
                log_c.write("  Au(a%s);\n" % sz)
                exe_c.write("in.get_bool_array(%s)" % i)
            else:
                error ("unsupported parameter for %s, %s, %s" % (ty, name, p))
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
            exe_c.write("  Z3_set_error_handler(result, Z3_replayer_error_handler);")
    log_c.write('}\n')
    exe_c.write('}\n')
    mk_log_macro(log_h, name, params)
    if log_result(result, params):
        mk_log_result_macro(log_h, name, result, params)
    next_id = next_id + 1

def mk_bindings(exe_c):
    exe_c.write("void register_z3_replayer_cmds(z3_replayer & in) {\n")
    for key, val in API2Id.items():
        exe_c.write("  in.register_cmd(%s, exec_%s, \"%s\");\n" % (key, val, val))
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

def ml_plus_type(ts):
    if ts == 'Z3_context':
        return 'Z3_context_plus'
    elif ts == 'Z3_ast' or ts == 'Z3_sort' or ts == 'Z3_func_decl' or ts == 'Z3_app' or ts == 'Z3_pattern':
        return 'Z3_ast_plus'
    elif ts == 'Z3_symbol':
        return 'Z3_symbol_plus'
    elif ts == 'Z3_constructor':
        return 'Z3_constructor_plus'
    elif ts == 'Z3_constructor_list':
        return 'Z3_constructor_list_plus'
    elif ts == 'Z3_rcf_num':
        return 'Z3_rcf_num_plus'
    elif ts == 'Z3_params':
        return 'Z3_params_plus'
    elif ts == 'Z3_param_descrs':
        return 'Z3_param_descrs_plus'
    elif ts == 'Z3_model':
        return 'Z3_model_plus'
    elif ts == 'Z3_func_interp':
        return 'Z3_func_interp_plus'
    elif ts == 'Z3_func_entry':
        return 'Z3_func_entry_plus'
    elif ts == 'Z3_goal':
        return 'Z3_goal_plus'
    elif ts == 'Z3_tactic':
        return 'Z3_tactic_plus'
    elif ts == 'Z3_probe':
        return 'Z3_probe_plus'
    elif ts == 'Z3_apply_result':
        return 'Z3_apply_result_plus'
    elif ts == 'Z3_solver':
        return 'Z3_solver_plus'
    elif ts == 'Z3_stats':
        return 'Z3_stats_plus'
    elif ts == 'Z3_ast_vector':
        return 'Z3_ast_vector_plus'
    elif ts == 'Z3_ast_map':
        return 'Z3_ast_map_plus'
    elif ts == 'Z3_fixedpoint':
        return 'Z3_fixedpoint_plus'
    elif ts == 'Z3_optimize':
        return 'Z3_optimize_plus'
    else:
        return ts

def ml_minus_type(ts):
    if ts == 'Z3_ast' or ts == 'Z3_sort' or ts == 'Z3_func_decl' or ts == 'Z3_app' or ts == 'Z3_pattern':
        return 'Z3_ast'
    if ts == 'Z3_ast_plus' or ts == 'Z3_sort_plus' or ts == 'Z3_func_decl_plus' or ts == 'Z3_app_plus' or ts == 'Z3_pattern_plus':
        return 'Z3_ast'
    elif ts == 'Z3_constructor_plus':
        return 'Z3_constructor'
    elif ts == 'Z3_constructor_list_plus':
        return 'Z3_constructor_list'
    elif ts == 'Z3_rcf_num_plus':
        return 'Z3_rcf_num'
    elif ts == 'Z3_params_plus':
        return 'Z3_params'
    elif ts == 'Z3_param_descrs_plus':
        return 'Z3_param_descrs'
    elif ts == 'Z3_model_plus':
        return 'Z3_model'
    elif ts == 'Z3_func_interp_plus':
        return 'Z3_func_interp'
    elif ts == 'Z3_func_entry_plus':
        return 'Z3_func_entry'
    elif ts == 'Z3_goal_plus':
        return 'Z3_goal'
    elif ts == 'Z3_tactic_plus':
        return 'Z3_tactic'
    elif ts == 'Z3_probe_plus':
        return 'Z3_probe'
    elif ts == 'Z3_apply_result_plus':
        return 'Z3_apply_result'
    elif ts == 'Z3_solver_plus':
        return 'Z3_solver'
    elif ts == 'Z3_stats_plus':
        return 'Z3_stats'
    elif ts == 'Z3_ast_vector_plus':
        return 'Z3_ast_vector'
    elif ts == 'Z3_ast_map_plus':
        return 'Z3_ast_map'
    elif ts == 'Z3_fixedpoint_plus':
        return 'Z3_fixedpoint'
    elif ts == 'Z3_optimize_plus':
        return 'Z3_optimize'
    else:
        return ts

def ml_plus_type_raw(ts):
    if ml_has_plus_type(ts):
        return ml_plus_type(ts) + '_raw';
    else:
        return ts

def ml_plus_ops_type(ts):
    if ml_has_plus_type(ts):
        return ml_plus_type(ts) + '_custom_ops'
    else:
        return 'default_custom_ops'

def ml_has_plus_type(ts):
    return ts != ml_plus_type(ts)

def ml_unwrap(t, ts, s):
    if t == STRING:
        return '(' + ts + ') String_val(' + s + ')'
    elif t == BOOL or (type2str(t) == 'bool'):
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
    elif ml_has_plus_type(ts):
        pts = ml_plus_type(ts)
        return '(' + ts + ') ' + ml_plus_type_raw(ts) + '((' + pts + '*) Data_custom_val(' + s + '))'
    else:
        return '* ((' + ts + '*) Data_custom_val(' + s + '))'

def ml_set_wrap(t, d, n):
    if t == VOID:
        return d + ' = Val_unit;'
    elif t == BOOL or (type2str(t) == 'bool'):
        return d + ' = Val_bool(' + n + ');'
    elif t == INT or t == UINT or t == PRINT_MODE or t == ERROR_CODE:
        return d + ' = Val_int(' + n + ');'
    elif t == INT64 or t == UINT64:
        return d + ' = Val_long(' + n + ');'
    elif t == DOUBLE:
        return d + '= caml_copy_double(' + n + ');'
    elif t == STRING:
        return d + ' = caml_copy_string((const char*) ' + n + ');'
    else:
        pts = ml_plus_type(type2str(t))
        return '*(' + pts + '*)Data_custom_val(' + d + ') = ' + n + ';'

def ml_alloc_and_store(t, lhs, rhs):
    if t == VOID or t == BOOL or t == INT or t == UINT or t == PRINT_MODE or t == ERROR_CODE or t == INT64 or t == UINT64 or t == DOUBLE or t == STRING or (type2str(t) == 'bool'):
        return ml_set_wrap(t, lhs, rhs)
    else:
        pts = ml_plus_type(type2str(t))
        pops = ml_plus_ops_type(type2str(t))
        alloc_str = '%s = caml_alloc_custom(&%s, sizeof(%s), 0, 1); ' % (lhs, pops, pts)
        return alloc_str + ml_set_wrap(t, lhs, rhs)

def mk_ml(ml_src_dir, ml_output_dir):
    global Type2Str
    ml_nativef  = os.path.join(ml_output_dir, 'z3native.ml')
    ml_native   = open(ml_nativef, 'w')
    ml_native.write('(* Automatically generated file *)\n\n')

    ml_pref = open(os.path.join(ml_src_dir, 'z3native.ml.pre'), 'r')
    for s in ml_pref:
        ml_native.write(s);
    ml_pref.close()

    ml_native.write('\n')
    for name, result, params in _dotnet_decls:
        ml_native.write('external %s : ' % ml_method_name(name))
        ip = inparams(params)
        op = outparams(params)
        if len(ip) == 0:
            ml_native.write(' unit -> ')
        for p in ip:
            ml_native.write('%s -> ' % param2ml(p))
        if len(op) > 0:
            ml_native.write('(')
        first = True
        if result != VOID or len(op) == 0:
            ml_native.write('%s' % type2ml(result))
            first = False
        for p in op:
            if first:
                first = False
            else:
                ml_native.write(' * ')
            ml_native.write('%s' % param2ml(p))
        if len(op) > 0:
            ml_native.write(')')
        if len(ip) > 5:
            ml_native.write('  = "n_%s_bytecode" "n_%s"\n' % (ml_method_name(name), ml_method_name(name)))
        else:
            ml_native.write('  = "n_%s"\n' % ml_method_name(name))
        ml_native.write('\n')

    # null pointer helpers
    for type_id in Type2Str:
        type_name = Type2Str[type_id]
        if ml_has_plus_type(type_name) and not type_name in ['Z3_context', 'Z3_sort', 'Z3_func_decl', 'Z3_app', 'Z3_pattern']:
            ml_name = type2ml(type_id)
            ml_native.write('external context_of_%s : %s -> context = "n_context_of_%s"\n' % (ml_name, ml_name, ml_name))
            ml_native.write('external is_null_%s : %s -> bool = "n_is_null_%s"\n' % (ml_name, ml_name, ml_name))
            ml_native.write('external mk_null_%s : context -> %s = "n_mk_null_%s"\n\n' % (ml_name, ml_name, ml_name))

    ml_native.write('(**/**)\n')
    ml_native.close()

    if mk_util.is_verbose():
        print ('Generated "%s"' % ml_nativef)

    mk_z3native_stubs_c(ml_src_dir, ml_output_dir)

z3_long_funs = frozenset([
    'Z3_solver_check',
    'Z3_solver_check_assumptions',
    'Z3_simplify',
    'Z3_simplify_ex',
    ])

z3_ml_overrides = frozenset([
    'Z3_mk_config'
    ])

def mk_z3native_stubs_c(ml_src_dir, ml_output_dir): # C interface
    ml_wrapperf = os.path.join(ml_output_dir, 'z3native_stubs.c')
    ml_wrapper = open(ml_wrapperf, 'w')
    ml_wrapper.write('// Automatically generated file\n\n')

    ml_pref = open(os.path.join(ml_src_dir, 'z3native_stubs.c.pre'), 'r')
    for s in ml_pref:
        ml_wrapper.write(s);
    ml_pref.close()

    for name, result, params in _dotnet_decls:

        if name in z3_ml_overrides:
            continue

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
            needs_tmp_value = False
            for p in params:
                if is_out_param(p) or is_array_param(p):
                    c = c + 1
                    needs_tmp_value = needs_tmp_value or param_kind(p) == OUT_ARRAY or param_kind(p) == INOUT_ARRAY
            if needs_tmp_value:
                c = c + 1
            if len(ap) > 0:
                c = c + 1
            ml_wrapper.write('  CAMLlocal%s(result, z3rv_val' % (c+2))
            for p in params:
                if is_out_param(p) or is_array_param(p):
                    ml_wrapper.write(', _a%s_val' % i)
                i = i + 1
            if needs_tmp_value:
                ml_wrapper.write(', tmp_val')
            if len(ap) != 0:
                ml_wrapper.write(', _iter');

            ml_wrapper.write(');\n')

        if len(ap) > 0:
            ml_wrapper.write('  unsigned _i;\n')

        # determine if the function has a context as parameter.
        have_context = (len(params) > 0) and (param_type(params[0]) == CONTEXT)

        if have_context and name not in Unwrapped:
            ml_wrapper.write('  Z3_error_code ec;\n')

        if result != VOID:
            ts = type2str(result)
            if ml_has_plus_type(ts):
                pts = ml_plus_type(ts)
                ml_wrapper.write('  %s z3rv_m;\n' % ts)
                ml_wrapper.write('  %s z3rv;\n' % pts)
            else:
                ml_wrapper.write('  %s z3rv;\n' % ts)

        # declare all required local variables
        # To comply with C89, we need to first declare the variables and initialize them
        # only afterwards.
        i = 0
        for param in params:
            if param_type(param) == CONTEXT and i == 0:
                ml_wrapper.write('  Z3_context_plus ctx_p;\n')
                ml_wrapper.write('  Z3_context _a0;\n')
            else:
                k = param_kind(param)
                if k == OUT_ARRAY:
                    ml_wrapper.write('  %s * _a%s;\n' % (type2str(param_type(param)), i))
                elif k == OUT_MANAGED_ARRAY:
                    ml_wrapper.write('  %s * _a%s;\n' % (type2str(param_type(param)), i))
                elif k == IN_ARRAY or k == INOUT_ARRAY:
                    t = param_type(param)
                    ts = type2str(t)
                    ml_wrapper.write('  %s * _a%s;\n' % (ts, i))
                elif k == IN:
                    t = param_type(param)
                    ml_wrapper.write('  %s _a%s;\n' % (type2str(t), i))
                elif k == OUT or k == INOUT:
                    t = param_type(param)
                    ml_wrapper.write('  %s _a%s;\n' % (type2str(t), i))
                    ts = type2str(t)
                    if ml_has_plus_type(ts):
                        pts = ml_plus_type(ts)
                        ml_wrapper.write('  %s _a%dp;\n' % (pts, i))
            i = i + 1


        # End of variable declarations in outermost block:
        # To comply with C89, no variable declarations may occur in the outermost block
        # from that point onwards (breaks builds with at least VC 2012 and prior)
        ml_wrapper.write('\n')

        # Declare locals, preprocess arrays, strings, in/out arguments
        i = 0
        for param in params:
            if param_type(param) == CONTEXT and i == 0:
                ml_wrapper.write('  ctx_p = *(Z3_context_plus*) Data_custom_val(a' + str(i) + ');\n')
                ml_wrapper.write('  _a0 = ctx_p->ctx;\n')
            else:
                k = param_kind(param)
                if k == OUT_ARRAY:
                    ml_wrapper.write('  _a%s = (%s*) malloc(sizeof(%s) * (_a%s));\n' % (
                        i,
                        type2str(param_type(param)),
                        type2str(param_type(param)),
                        param_array_capacity_pos(param)))
                elif k == OUT_MANAGED_ARRAY:
                    ml_wrapper.write('  _a%s = 0;\n' % i)
                elif k == IN_ARRAY or k == INOUT_ARRAY:
                    t = param_type(param)
                    ts = type2str(t)
                    ml_wrapper.write('  _a%s = (%s*) malloc(sizeof(%s) * _a%s);\n' % (i, ts, ts, param_array_capacity_pos(param)))
                elif k == IN:
                    t = param_type(param)
                    ml_wrapper.write('  _a%s = %s;\n' % (i, ml_unwrap(t, type2str(t), 'a' + str(i))))
            i = i + 1

        i = 0
        for param in params:
            k = param_kind(param)
            if k == IN_ARRAY or k == INOUT_ARRAY:
                t = param_type(param)
                ts = type2str(t)
                ml_wrapper.write('  _iter = a' + str(i) + ';\n')
                ml_wrapper.write('  for (_i = 0; _i < _a%s; _i++) {\n' % param_array_capacity_pos(param))
                ml_wrapper.write('    assert(_iter != Val_emptylist);\n')
                ml_wrapper.write('    _a%s[_i] = %s;\n' % (i, ml_unwrap(t, ts, 'Field(_iter, 0)')))
                ml_wrapper.write('    _iter = Field(_iter, 1);\n')
                ml_wrapper.write('  }\n')
                ml_wrapper.write('  assert(_iter == Val_emptylist);\n\n')
            i = i + 1

        release_caml_gc= name in z3_long_funs
        if release_caml_gc:
            ml_wrapper.write('\n  caml_release_runtime_system();\n')

        ml_wrapper.write('\n  /* invoke Z3 function */\n  ')
        if result != VOID:
            ts = type2str(result)
            if ml_has_plus_type(ts):
                ml_wrapper.write('z3rv_m = ')
            else:
                ml_wrapper.write('z3rv = ')


        # invoke procedure
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

        if name in NULLWrapped:
            ml_wrapper.write('  if (z3rv_m == NULL) {\n')
            ml_wrapper.write('    caml_raise_with_string(*caml_named_value("Z3EXCEPTION"), "Object allocation failed");\n')
            ml_wrapper.write('  }\n')

        if release_caml_gc:
            ml_wrapper.write('\n  caml_acquire_runtime_system();\n')

        if have_context and name not in Unwrapped:
            ml_wrapper.write('  ec = Z3_get_error_code(ctx_p->ctx);\n')
            ml_wrapper.write('  if (ec != Z3_OK) {\n')
            ml_wrapper.write('    const char * msg = Z3_get_error_msg(ctx_p->ctx, ec);\n')
            ml_wrapper.write('    caml_raise_with_string(*caml_named_value("Z3EXCEPTION"), msg);\n')
            ml_wrapper.write('  }\n')

        if result != VOID:
            ts = type2str(result)
            if ml_has_plus_type(ts):
                pts = ml_plus_type(ts)
                if name in NULLWrapped:
                    ml_wrapper.write('  z3rv = %s_mk(z3rv_m);\n' % pts)
                else:
                    ml_wrapper.write('  z3rv = %s_mk(ctx_p, (%s) z3rv_m);\n' % (pts, ml_minus_type(ts)))

        # convert output params
        if len(op) > 0:
            # we have output parameters (i.e. call-by-reference arguments to the Z3 native
            # code function). Hence, the value returned by the OCaml native wrapper is a tuple
            # which contains the Z3 native function's return value (if it is non-void) in its
            # first and the output parameters in the following components.

            ml_wrapper.write('\n  /* construct return tuple */\n')
            ml_wrapper.write('  result = caml_alloc(%s, 0);\n' % ret_size)

            i = 0
            for p in params:
                pt = param_type(p)
                ts = type2str(pt)
                if param_kind(p) == OUT_ARRAY or param_kind(p) == INOUT_ARRAY:
                    # convert a C-array into an OCaml list and return it
                    ml_wrapper.write('\n  _a%s_val = Val_emptylist;\n' % i)
                    ml_wrapper.write('  for (_i = _a%s; _i > 0; _i--) {\n' % param_array_capacity_pos(p))
                    pts = ml_plus_type(ts)
                    pops = ml_plus_ops_type(ts)
                    if ml_has_plus_type(ts):
                        ml_wrapper.write('    %s _a%dp = %s_mk(ctx_p, (%s) _a%d[_i - 1]);\n' % (pts, i, pts, ml_minus_type(ts), i))
                        ml_wrapper.write('    %s\n' % ml_alloc_and_store(pt, 'tmp_val', '_a%dp' % i))
                    else:
                        ml_wrapper.write('    %s\n' % ml_alloc_and_store(pt, 'tmp_val', '_a%d[_i - 1]' % i))
                    ml_wrapper.write('    _iter = caml_alloc(2,0);\n')
                    ml_wrapper.write('    Store_field(_iter, 0, tmp_val);\n')
                    ml_wrapper.write('    Store_field(_iter, 1, _a%s_val);\n' % i)
                    ml_wrapper.write('    _a%s_val = _iter;\n' % i)
                    ml_wrapper.write('  }\n\n')
                elif param_kind(p) == OUT_MANAGED_ARRAY:
                    wrp = ml_set_wrap(pt, '_a%d_val' % i, '_a%d' % i)
                    wrp = wrp.replace('*)', '**)')
                    wrp = wrp.replace('_plus', '')
                    ml_wrapper.write('  %s\n' % wrp)
                elif is_out_param(p):
                    if ml_has_plus_type(ts):
                        pts = ml_plus_type(ts)
                        ml_wrapper.write('  _a%dp = %s_mk(ctx_p, (%s) _a%d);\n' % (i, pts, ml_minus_type(ts), i))
                        ml_wrapper.write('  %s\n' % ml_alloc_and_store(pt, '_a%d_val' % i, '_a%dp' % i))
                    else:
                        ml_wrapper.write('  %s\n' % ml_alloc_and_store(pt, '_a%d_val' % i, '_a%d' % i))
                i = i + 1

            # return tuples
            i = j = 0
            if result != VOID:
                ml_wrapper.write('  %s' % ml_alloc_and_store(result, 'z3rv_val', 'z3rv'))
                ml_wrapper.write('  Store_field(result, 0, z3rv_val);\n')
                j = j + 1
            for p in params:
                if is_out_param(p):
                    ml_wrapper.write('  Store_field(result, %s, _a%s_val);\n' % (j, i))
                    j = j + 1
                i = i + 1
        else:
            # As we have no output parameters, we simply return the result
            ml_wrapper.write('\n  /* construct simple return value */\n')
            ml_wrapper.write('  %s' % ml_alloc_and_store(result, "result", "z3rv"))

        # local array cleanup
        ml_wrapper.write('\n  /* cleanup and return */\n')
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

    if mk_util.is_verbose():
        print ('Generated "%s"' % ml_wrapperf)

# Collect API(...) commands from
def def_APIs(api_files):
    pat1 = re.compile(" *def_API.*")
    pat2 = re.compile(" *extra_API.*")
    for api_file in api_files:
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
                raise mk_exec_header.MKException("Failed to process API definition: %s" % line)

def write_log_h_preamble(log_h):
  log_h.write('// Automatically generated file\n')
  log_h.write('#include\"api/z3.h\"\n')
  log_h.write('#ifdef __GNUC__\n')
  log_h.write('#define _Z3_UNUSED __attribute__((unused))\n')
  log_h.write('#else\n')
  log_h.write('#define _Z3_UNUSED\n')
  log_h.write('#endif\n')
  #
  log_h.write('#include<iostream>\n')
  log_h.write('extern std::ostream * g_z3_log;\n')
  log_h.write('extern bool           g_z3_log_enabled;\n')
  log_h.write('class z3_log_ctx { bool m_prev; public: z3_log_ctx():m_prev(g_z3_log_enabled) { g_z3_log_enabled = false; } ~z3_log_ctx() { g_z3_log_enabled = m_prev; } bool enabled() const { return m_prev; } };\n')
  log_h.write('inline void SetR(void * obj) { *g_z3_log << "= " << obj << "\\n"; }\ninline void SetO(void * obj, unsigned pos) { *g_z3_log << "* " << obj << " " << pos << "\\n"; } \ninline void SetAO(void * obj, unsigned pos, unsigned idx) { *g_z3_log << "@ " << obj << " " << pos << " " << idx << "\\n"; }\n')
  log_h.write('#define RETURN_Z3(Z3RES) if (_LOG_CTX.enabled()) { SetR(Z3RES); } return Z3RES\n')
  log_h.write('void _Z3_append_log(char const * msg);\n')


def write_log_c_preamble(log_c):
  log_c.write('// Automatically generated file\n')
  log_c.write('#include<iostream>\n')
  log_c.write('#include\"api/z3.h\"\n')
  log_c.write('#include\"api/api_log_macros.h\"\n')
  log_c.write('#include\"api/z3_logger.h\"\n')

def write_exe_c_preamble(exe_c):
  exe_c.write('// Automatically generated file\n')
  exe_c.write('#include\"api/z3.h\"\n')
  exe_c.write('#include\"api/z3_replayer.h\"\n')
  #
  exe_c.write('void Z3_replayer_error_handler(Z3_context ctx, Z3_error_code c) { printf("[REPLAYER ERROR HANDLER]: %s\\n", Z3_get_error_msg(ctx, c)); }\n')

def write_core_py_post(core_py):
  core_py.write("""
# Clean up
del _lib
del _default_dirs
del _all_dirs
del _ext
""")
    
def write_core_py_preamble(core_py):
  core_py.write(
"""
# Automatically generated file
import sys, os
import ctypes
import pkg_resources
from .z3types import *
from .z3consts import *

_ext = 'dll' if sys.platform in ('win32', 'cygwin') else 'dylib' if sys.platform == 'darwin' else 'so'
_lib = None
_default_dirs = ['.',
                 os.path.dirname(os.path.abspath(__file__)),
                 pkg_resources.resource_filename('z3', 'lib'),
                 os.path.join(sys.prefix, 'lib'),
                 None]
_all_dirs = []

if sys.version < '3':
  import __builtin__
  if hasattr(__builtin__, "Z3_LIB_DIRS"):
    _all_dirs = __builtin__.Z3_LIB_DIRS
else:
  import builtins
  if hasattr(builtins, "Z3_LIB_DIRS"):
    _all_dirs = builtins.Z3_LIB_DIRS

for v in ('Z3_LIBRARY_PATH', 'PATH', 'PYTHONPATH'):
  if v in os.environ:
    lp = os.environ[v];
    lds = lp.split(';') if sys.platform in ('win32') else lp.split(':')
    _all_dirs.extend(lds)

_all_dirs.extend(_default_dirs)

_failures = []
for d in _all_dirs:
  try:
    d = os.path.realpath(d)
    if os.path.isdir(d):
      d = os.path.join(d, 'libz3.%s' % _ext)
      if os.path.isfile(d):
        _lib = ctypes.CDLL(d)
        break
  except Exception as e:
    _failures += [e]
    pass

if _lib is None:
  # If all else failed, ask the system to find it.
  try:
    _lib = ctypes.CDLL('libz3.%s' % _ext)
  except Exception as e:
    _failures += [e]
    pass

if _lib is None:
  print("Could not find libz3.%s; consider adding the directory containing it to" % _ext)
  print("  - your system's PATH environment variable,")
  print("  - the Z3_LIBRARY_PATH environment variable, or ")
  print("  - to the custom Z3_LIBRARY_DIRS Python-builtin before importing the z3 module, e.g. via")
  if sys.version < '3':
    print("    import __builtin__")
    print("    __builtin__.Z3_LIB_DIRS = [ '/path/to/libz3.%s' ] " % _ext)
  else:
    print("    import builtins")
    print("    builtins.Z3_LIB_DIRS = [ '/path/to/libz3.%s' ] " % _ext)
  raise Z3Exception("libz3.%s not found." % _ext)

def _to_ascii(s):
  if isinstance(s, str):
    try: 
      return s.encode('ascii')
    except:
      # kick the bucket down the road.  :-J
      return s
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

_error_handler_type  = ctypes.CFUNCTYPE(None, ctypes.c_void_p, ctypes.c_uint)

_lib.Z3_set_error_handler.restype  = None
_lib.Z3_set_error_handler.argtypes = [ContextObj, _error_handler_type]

"""
  )

log_h = None
log_c = None
exe_c = None
core_py = None

# FIXME: This can only be called once from this module
# due to its use of global state!
def generate_files(api_files,
                   api_output_dir=None,
                   z3py_output_dir=None,
                   dotnet_output_dir=None,
                   java_output_dir=None,
                   java_package_name=None,
                   js_output_dir=None,
                   ml_output_dir=None,
                   ml_src_dir=None):
  """
    Scan the api files in ``api_files`` and emit the relevant API files into
    the output directories specified. If an output directory is set to ``None``
    then the files for that language binding or module are not emitted.

    The reason for this function interface is:

    * The CMake build system needs to control where
      files are emitted.
    * The CMake build system needs to be able to choose
      which API files are emitted.
    * This function should be as decoupled from the Python
      build system as much as possible but it must be possible
      for the Python build system code to use this function.

    Therefore we:

    * Do not use the ``mk_util.is_*_enabled()`` functions
    to determine if certain files should be or should not be emitted.

    * Do not use the components declared in the Python build system
    to determine the output directory paths.
  """
  # FIXME: These should not be global
  global log_h, log_c, exe_c, core_py
  assert isinstance(api_files, list)

  # Hack: Avoid emitting files when we don't want them
  # by writing to temporary files that get deleted when
  # closed. This allows us to work around the fact that
  # existing code is designed to always emit these files.
  def mk_file_or_temp(output_dir, file_name, mode='w'):
    if output_dir != None:
      assert os.path.exists(output_dir) and os.path.isdir(output_dir)
      return open(os.path.join(output_dir, file_name), mode)
    else:
      # Return a file that we can write to without caring
      print("Faking emission of '{}'".format(file_name))
      import tempfile
      return tempfile.TemporaryFile(mode=mode)

  with mk_file_or_temp(api_output_dir, 'api_log_macros.h') as log_h:
    with mk_file_or_temp(api_output_dir, 'api_log_macros.cpp') as log_c:
      with mk_file_or_temp(api_output_dir, 'api_commands.cpp') as exe_c:
        with mk_file_or_temp(z3py_output_dir, os.path.join('z3', 'z3core.py')) as core_py:
          # Write preambles
          write_log_h_preamble(log_h)
          write_log_c_preamble(log_c)
          write_exe_c_preamble(exe_c)
          write_core_py_preamble(core_py)

          # FIXME: these functions are awful
          def_Types(api_files)
          def_APIs(api_files)
          mk_bindings(exe_c)
          mk_py_wrappers()
          write_core_py_post(core_py)

          if mk_util.is_verbose():
            print("Generated '{}'".format(log_h.name))
            print("Generated '{}'".format(log_c.name))
            print("Generated '{}'".format(exe_c.name))
            print("Generated '{}'".format(core_py.name))

  if dotnet_output_dir:
    with open(os.path.join(dotnet_output_dir, 'Native.cs'), 'w') as dotnet_file:
      mk_dotnet(dotnet_file)
      mk_dotnet_wrappers(dotnet_file)
      if mk_util.is_verbose():
        print("Generated '{}'".format(dotnet_file.name))
        
  if java_output_dir:
    mk_java(java_output_dir, java_package_name)

  if ml_output_dir:
    assert not ml_src_dir is None
    mk_ml(ml_src_dir, ml_output_dir)

  if js_output_dir:
    mk_js(js_output_dir)

def main(args):
  logging.basicConfig(level=logging.INFO)
  parser = argparse.ArgumentParser(description=__doc__)
  parser.add_argument("api_files",
                      nargs="+",
                      help="API header files to generate files from")
  parser.add_argument("--api_output_dir",
                      default=None,
                      help="Directory to emit files for api module. If not specified no files are emitted.")
  parser.add_argument("--z3py-output-dir",
                      dest="z3py_output_dir",
                      default=None,
                      help="Directory to emit z3py files. If not specified no files are emitted.")
  parser.add_argument("--dotnet-output-dir",
                      dest="dotnet_output_dir",
                      default=None,
                      help="Directory to emit dotnet files. If not specified no files are emitted.")
  parser.add_argument("--java-output-dir",
                      dest="java_output_dir",
                      default=None,
                      help="Directory to emit Java files. If not specified no files are emitted.")
  parser.add_argument("--java-package-name",
                      dest="java_package_name",
                      default=None,
                      help="Name to give the Java package (e.g. ``com.microsoft.z3``).")
  parser.add_argument("--ml-src-dir",
                      dest="ml_src_dir",
                      default=None,
                      help="Directory containing OCaml source files. If not specified no files are emitted")
  parser.add_argument("--ml-output-dir",
                      dest="ml_output_dir",
                      default=None,
                      help="Directory to emit OCaml files. If not specified no files are emitted.")
  parser.add_argument("--js_output_dir",
                      dest="js_output_dir",
                      default=None,
                      help="Directory to emit js bindings. If not specified no files are emitted.")
  pargs = parser.parse_args(args)

  if pargs.java_output_dir:
    if pargs.java_package_name == None:
      logging.error('--java-package-name must be specified')
      return 1

  if pargs.ml_output_dir:
    if pargs.ml_src_dir is None:
      logging.error('--ml-src-dir must be specified')
      return 1

  for api_file in pargs.api_files:
    if not os.path.exists(api_file):
      logging.error('"{}" does not exist'.format(api_file))
      return 1

  generate_files(api_files=pargs.api_files,
                 api_output_dir=pargs.api_output_dir,
                 z3py_output_dir=pargs.z3py_output_dir,
                 dotnet_output_dir=pargs.dotnet_output_dir,
                 java_output_dir=pargs.java_output_dir,
                 java_package_name=pargs.java_package_name,
                 js_output_dir=pargs.js_output_dir,
                 ml_output_dir=pargs.ml_output_dir,
                 ml_src_dir=pargs.ml_src_dir)
  return 0

if __name__ == '__main__':
  sys.exit(main(sys.argv[1:]))
