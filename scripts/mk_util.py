############################################
# Copyright (c) 2012 Microsoft Corporation
#
# Auxiliary scripts for generating Makefiles
# and Visual Studio project files.
#
# Author: Leonardo de Moura (leonardo)
############################################
import io
import sys
import os
import re
import getopt
import shutil
from mk_exception import *
import mk_genfile_common
from fnmatch import fnmatch
import distutils.sysconfig
import compileall
import subprocess

def getenv(name, default):
    try:
        return os.environ[name].strip(' "\'')
    except:
        return default

CXX=getenv("CXX", None)
CC=getenv("CC", None)
CPPFLAGS=getenv("CPPFLAGS", "")
CXXFLAGS=getenv("CXXFLAGS", "")
AR=getenv("AR", "ar")
EXAMP_DEBUG_FLAG=''
LDFLAGS=getenv("LDFLAGS", "")
JNI_HOME=getenv("JNI_HOME", None)
OCAMLC=getenv("OCAMLC", "ocamlc")
OCAMLOPT=getenv("OCAMLOPT", "ocamlopt")
OCAML_LIB=getenv("OCAML_LIB", None)
OCAMLFIND=getenv("OCAMLFIND", "ocamlfind")
DOTNET="dotnet"
# Standard install directories relative to PREFIX
INSTALL_BIN_DIR=getenv("Z3_INSTALL_BIN_DIR", "bin")
INSTALL_LIB_DIR=getenv("Z3_INSTALL_LIB_DIR", "lib")
INSTALL_INCLUDE_DIR=getenv("Z3_INSTALL_INCLUDE_DIR", "include")
INSTALL_PKGCONFIG_DIR=getenv("Z3_INSTALL_PKGCONFIG_DIR", os.path.join(INSTALL_LIB_DIR, 'pkgconfig'))

CXX_COMPILERS=['g++', 'clang++']
C_COMPILERS=['gcc', 'clang']
JAVAC=None
JAR=None
PYTHON_PACKAGE_DIR=distutils.sysconfig.get_python_lib(prefix=getenv("PREFIX", None))
BUILD_DIR='build'
REV_BUILD_DIR='..'
SRC_DIR='src'
EXAMPLE_DIR='examples'
# Required Components
Z3_DLL_COMPONENT='api_dll'
PATTERN_COMPONENT='pattern'
UTIL_COMPONENT='util'
API_COMPONENT='api'
DOTNET_COMPONENT='dotnet'
DOTNET_CORE_COMPONENT='dotnet'
JAVA_COMPONENT='java'
ML_COMPONENT='ml'
CPP_COMPONENT='cpp'
PYTHON_COMPONENT='python'
#####################
IS_WINDOWS=False
IS_LINUX=False
IS_HURD=False
IS_OSX=False
IS_FREEBSD=False
IS_NETBSD=False
IS_OPENBSD=False
IS_SUNOS=False
IS_CYGWIN=False
IS_CYGWIN_MINGW=False
IS_MSYS2=False
VERBOSE=True
DEBUG_MODE=False
SHOW_CPPS = True
VS_X64 = False
VS_ARM = False
LINUX_X64 = True
ONLY_MAKEFILES = False
Z3PY_SRC_DIR=None
Z3JS_SRC_DIR=None
VS_PROJ = False
TRACE = False
PYTHON_ENABLED=False
DOTNET_CORE_ENABLED=False
DOTNET_KEY_FILE=getenv("Z3_DOTNET_KEY_FILE", None)
JAVA_ENABLED=False
ML_ENABLED=False
JS_ENABLED=False
PYTHON_INSTALL_ENABLED=False
STATIC_LIB=False
STATIC_BIN=False
VER_MAJOR=None
VER_MINOR=None
VER_BUILD=None
VER_TWEAK=None
PREFIX=sys.prefix
GMP=False
VS_PAR=False
VS_PAR_NUM=8
GPROF=False
GIT_HASH=False
GIT_DESCRIBE=False
SLOW_OPTIMIZE=False
LOG_SYNC=False
SINGLE_THREADED=False
GUARD_CF=False
ALWAYS_DYNAMIC_BASE=False

FPMATH="Default"
FPMATH_FLAGS="-mfpmath=sse -msse -msse2"


def check_output(cmd):
    out = subprocess.Popen(cmd, stdout=subprocess.PIPE).communicate()[0]
    if out != None:
        enc = sys.stdout.encoding
        if enc != None: return out.decode(enc).rstrip('\r\n')
        else: return out.rstrip('\r\n')
    else:
        return ""

def git_hash():
    try:
        branch = check_output(['git', 'rev-parse', '--abbrev-ref', 'HEAD'])
        r = check_output(['git', 'show-ref', '--abbrev=12', 'refs/heads/%s' % branch])
    except:
        raise MKException("Failed to retrieve git hash")
    ls = r.split(' ')
    if len(ls) != 2:
        raise MKException("Unexpected git output " + r)
    return ls[0]

def is_windows():
    return IS_WINDOWS

def is_linux():
    return IS_LINUX

def is_hurd():
    return IS_HURD

def is_freebsd():
    return IS_FREEBSD

def is_netbsd():
    return IS_NETBSD

def is_openbsd():
    return IS_OPENBSD

def is_sunos():
    return IS_SUNOS

def is_osx():
    return IS_OSX

def is_cygwin():
    return IS_CYGWIN

def is_cygwin_mingw():
    return IS_CYGWIN_MINGW

def is_msys2():
    return IS_MSYS2

def norm_path(p):
    return os.path.expanduser(os.path.normpath(p))

def which(program):
    import os
    def is_exe(fpath):
        return os.path.isfile(fpath) and os.access(fpath, os.X_OK)

    fpath, fname = os.path.split(program)
    if fpath:
        if is_exe(program):
            return program
    else:
        for path in getenv("PATH", "").split(os.pathsep):
            exe_file = os.path.join(path, program)
            if is_exe(exe_file):
                return exe_file
    return None

class TempFile:
    def __init__(self, name):
        try:
            self.name  = name
            self.fname = open(name, 'w')
        except:
            raise MKException("Failed to create temporary file '%s'" % self.name)

    def add(self, s):
        self.fname.write(s)

    def commit(self):
        self.fname.close()

    def __del__(self):
        self.fname.close()
        try:
            os.remove(self.name)
        except:
            pass

def exec_cmd(cmd):
    if isinstance(cmd, str):
        cmd = cmd.split(' ')
    new_cmd = []
    first = True
    for e in cmd:
        if first:
            first = False
            new_cmd.append(e)
        else:
            if e != "":
                se = e.split(' ')
                if len(se) > 1:
                    for e2 in se:
                        if e2 != "":
                            new_cmd.append(e2)
                else:
                    new_cmd.append(e)
    cmd = new_cmd
    null = open(os.devnull, 'wb')
    try:
        return subprocess.call(cmd, stdout=null, stderr=null)
    except:
        # Failed to create process
        return 1
    finally:
        null.close()

# rm -f fname
def rmf(fname):
    if os.path.exists(fname):
        os.remove(fname)

def exec_compiler_cmd(cmd):
    r = exec_cmd(cmd)
    if is_windows() or is_cygwin_mingw() or is_cygwin() or is_msys2():
        rmf('a.exe')
    else:
        rmf('a.out')
    return r

def test_cxx_compiler(cc):
    if is_verbose():
        print("Testing %s..." % cc)
    t = TempFile('tst.cpp')
    t.add('#include<iostream>\nint main() { return 0; }\n')
    t.commit()
    return exec_compiler_cmd([cc, CPPFLAGS, CXXFLAGS, 'tst.cpp', LDFLAGS]) == 0

def test_c_compiler(cc):
    if is_verbose():
        print("Testing %s..." % cc)
    t = TempFile('tst.c')
    t.add('#include<stdio.h>\nint main() { return 0; }\n')
    t.commit()
    return exec_compiler_cmd([cc, CPPFLAGS, 'tst.c', LDFLAGS]) == 0

def test_gmp(cc):
    if is_verbose():
        print("Testing GMP...")
    t = TempFile('tstgmp.cpp')
    t.add('#include<gmp.h>\nint main() { mpz_t t; mpz_init(t); mpz_clear(t); return 0; }\n')
    t.commit()
    return exec_compiler_cmd([cc, CPPFLAGS, 'tstgmp.cpp', LDFLAGS, '-lgmp']) == 0



def test_fpmath(cc):
    global FPMATH_FLAGS
    if is_verbose():
        print("Testing floating point support...")
    t = TempFile('tstsse.cpp')
    t.add('int main() { return 42; }\n')
    t.commit()
    # -Werror is needed because some versions of clang warn about unrecognized
    # -m flags.
    if exec_compiler_cmd([cc, CPPFLAGS, '-Werror', 'tstsse.cpp', LDFLAGS, '-mfpmath=sse -msse -msse2']) == 0:
        FPMATH_FLAGS="-mfpmath=sse -msse -msse2"
        return "SSE2-GCC"
    elif exec_compiler_cmd([cc, CPPFLAGS, '-Werror', 'tstsse.cpp', LDFLAGS, '-msse -msse2']) == 0:
        FPMATH_FLAGS="-msse -msse2"
        return "SSE2-CLANG"
    elif exec_compiler_cmd([cc, CPPFLAGS, '-Werror', 'tstsse.cpp', LDFLAGS, '-mfpu=vfp -mfloat-abi=hard']) == 0:
        FPMATH_FLAGS="-mfpu=vfp -mfloat-abi=hard"
        return "ARM-VFP"
    else:
        FPMATH_FLAGS=""
        return "UNKNOWN"


def find_jni_h(path):
    for root, dirs, files in os.walk(path):
        for f in files:
            if f == 'jni.h':
                return root
    return False

def check_java():
    global JNI_HOME
    global JAVAC
    global JAR

    JDK_HOME = getenv('JDK_HOME', None) # we only need to check this locally.

    if is_verbose():
        print("Finding javac ...")

    if JDK_HOME is not None:
        if IS_WINDOWS:
            JAVAC = os.path.join(JDK_HOME, 'bin', 'javac.exe')
        else:
            JAVAC = os.path.join(JDK_HOME, 'bin', 'javac')

        if not os.path.exists(JAVAC):
            raise MKException("Failed to detect javac at '%s/bin'; the environment variable JDK_HOME is probably set to the wrong path." % os.path.join(JDK_HOME))
    else:
        # Search for javac in the path.
        ind = 'javac'
        if IS_WINDOWS:
            ind = ind + '.exe'
        paths = os.getenv('PATH', None)
        if paths:
            spaths = paths.split(os.pathsep)
            for i in range(0, len(spaths)):
                cmb = os.path.join(spaths[i], ind)
                if os.path.exists(cmb):
                    JAVAC = cmb
                    break

    if JAVAC is None:
        raise MKException('No java compiler in the path, please adjust your PATH or set JDK_HOME to the location of the JDK.')

    if is_verbose():
        print("Finding jar ...")

    if IS_WINDOWS:
        JAR = os.path.join(os.path.dirname(JAVAC), 'jar.exe')
    else:
        JAR = os.path.join(os.path.dirname(JAVAC), 'jar')

    if not os.path.exists(JAR):
        raise MKException("Failed to detect jar at '%s'; the environment variable JDK_HOME is probably set to the wrong path." % os.path.join(JDK_HOME))

    if is_verbose():
        print("Testing %s..." % JAVAC)

    t = TempFile('Hello.java')
    t.add('public class Hello { public static void main(String[] args) { System.out.println("Hello, World"); }}\n')
    t.commit()

    oo = TempFile('output')
    eo = TempFile('errout')
    try:
        subprocess.call([JAVAC, 'Hello.java', '-verbose', '-source', '1.8', '-target', '1.8' ], stdout=oo.fname, stderr=eo.fname)
        oo.commit()
        eo.commit()
    except:
        raise MKException('Found, but failed to run Java compiler at %s' % (JAVAC))

    os.remove('Hello.class')

    if is_verbose():
        print("Finding jni.h...")

    if JNI_HOME is not None:
        if not os.path.exists(os.path.join(JNI_HOME, 'jni.h')):
            raise MKException("Failed to detect jni.h '%s'; the environment variable JNI_HOME is probably set to the wrong path." % os.path.join(JNI_HOME))
    else:
        # Search for jni.h in the library directories...
        t = open('errout', 'r')
        open_pat = re.compile("\[search path for class files: (.*)\]")
        cdirs = []
        for line in t:
            m = open_pat.match(line)
            if m:
                libdirs = m.group(1).split(',')
                for libdir in libdirs:
                    q = os.path.dirname(libdir)
                    if cdirs.count(q) == 0 and len(q) > 0:
                        cdirs.append(q)
        t.close()

        # ... plus some heuristic ones.
        extra_dirs = []

        # For the libraries, even the JDK usually uses a JRE that comes with it. To find the
        # headers we have to go a little bit higher up.
        for dir in cdirs:
            extra_dirs.append(os.path.abspath(os.path.join(dir, '..')))

        if IS_OSX: # Apparently Apple knows best where to put stuff...
            extra_dirs.append('/System/Library/Frameworks/JavaVM.framework/Headers/')

        cdirs[len(cdirs):] = extra_dirs

        for dir in cdirs:
            q = find_jni_h(dir)
            if q is not False:
                JNI_HOME = q

        if JNI_HOME is None:
            raise MKException("Failed to detect jni.h. Possible solution: set JNI_HOME with the path to JDK.")

def test_csc_compiler(c):
    t = TempFile('hello.cs')
    t.add('public class hello { public static void Main() {} }')
    t.commit()
    if is_verbose():
        print ('Testing %s...' % c)
    r = exec_cmd([c, 'hello.cs'])
    try:
        rmf('hello.cs')
        rmf('hello.exe')
    except:
        pass
    return r == 0

def check_dotnet_core():
    if not IS_WINDOWS:
        return
    r = exec_cmd([DOTNET, '--help'])
    if r != 0:
        raise MKException('Failed testing dotnet. Make sure to install and configure dotnet core utilities')

def check_ml():
    t = TempFile('hello.ml')
    t.add('print_string "Hello world!\n";;')
    t.commit()
    if is_verbose():
        print ('Testing %s...' % OCAMLC)
    r = exec_cmd([OCAMLC, '-o', 'a.out', 'hello.ml'])
    if r != 0:
        raise MKException('Failed testing ocamlc compiler. Set environment variable OCAMLC with the path to the Ocaml compiler')
    if is_verbose():
        print ('Testing %s...' % OCAMLOPT)
    r = exec_cmd([OCAMLOPT, '-o', 'a.out', 'hello.ml'])
    if r != 0:
        raise MKException('Failed testing ocamlopt compiler. Set environment variable OCAMLOPT with the path to the Ocaml native compiler. Note that ocamlopt may require flexlink to be in your path.')
    try:
        rmf('hello.cmi')
        rmf('hello.cmo')
        rmf('hello.cmx')
        rmf('a.out')
        rmf('hello.o')
    except:
        pass
    find_ml_lib()
    find_ocaml_find()

def find_ocaml_find():
    global OCAMLFIND
    if is_verbose():
        print ("Testing %s..." % OCAMLFIND)
    r = exec_cmd([OCAMLFIND, 'printconf'])
    if r != 0:
        OCAMLFIND = ''

def find_ml_lib():
    global OCAML_LIB
    if is_verbose():
        print ('Finding OCAML_LIB...')
    t = TempFile('output')
    null = open(os.devnull, 'wb')
    try:
        subprocess.call([OCAMLC, '-where'], stdout=t.fname, stderr=null)
        t.commit()
    except:
        raise MKException('Failed to find Ocaml library; please set OCAML_LIB')
    finally:
        null.close()

    t = open('output', 'r')
    for line in t:
        OCAML_LIB = line[:-1]
    if is_verbose():
        print ('OCAML_LIB=%s' % OCAML_LIB)
    t.close()
    rmf('output')
    return

def is64():
    global LINUX_X64
    if is_sunos() and sys.version_info.major < 3: 
        return LINUX_X64
    else:
        return LINUX_X64 and sys.maxsize >= 2**32

def check_ar():
    if is_verbose():
        print("Testing ar...")
    if which(AR) is None:
        raise MKException('%s (archive tool) was not found' % AR)

def find_cxx_compiler():
    global CXX, CXX_COMPILERS
    if CXX is not None:
        if test_cxx_compiler(CXX):
            return CXX
    for cxx in CXX_COMPILERS:
        if test_cxx_compiler(cxx):
            CXX = cxx
            return CXX
    raise MKException('C++ compiler was not found. Try to set the environment variable CXX with the C++ compiler available in your system.')

def find_c_compiler():
    global CC, C_COMPILERS
    if CC is not None:
        if test_c_compiler(CC):
            return CC
    for c in C_COMPILERS:
        if test_c_compiler(c):
            CC = c
            return CC
    raise MKException('C compiler was not found. Try to set the environment variable CC with the C compiler available in your system.')

def set_version(major, minor, build, revision):
    global VER_MAJOR, VER_MINOR, VER_BUILD, VER_TWEAK, GIT_DESCRIBE
    VER_MAJOR = major
    VER_MINOR = minor
    VER_BUILD = build
    VER_TWEAK = revision
    if GIT_DESCRIBE:
        branch = check_output(['git', 'rev-parse', '--abbrev-ref', 'HEAD'])
        VER_TWEAK = int(check_output(['git', 'rev-list', '--count', 'HEAD']))

def get_version():
    return (VER_MAJOR, VER_MINOR, VER_BUILD, VER_TWEAK)

def get_version_string(n):
    if n == 3:
        return "{}.{}.{}".format(VER_MAJOR,VER_MINOR,VER_BUILD)
    return "{}.{}.{}.{}".format(VER_MAJOR,VER_MINOR,VER_BUILD,VER_TWEAK)

def build_static_lib():
    return STATIC_LIB

def build_static_bin():
    return STATIC_BIN

def is_cr_lf(fname):
    # Check whether text files use cr/lf
    f = open(fname, 'r')
    line = f.readline()
    f.close()
    sz = len(line)
    return sz >= 2 and line[sz-2] == '\r' and line[sz-1] == '\n'

# dos2unix in python
#    cr/lf --> lf
def dos2unix(fname):
    if is_cr_lf(fname):
        fin  = open(fname, 'r')
        fname_new = '%s.new' % fname
        fout = open(fname_new, 'w')
        for line in fin:
            line = line.rstrip('\r\n')
            fout.write(line)
            fout.write('\n')
        fin.close()
        fout.close()
        shutil.move(fname_new, fname)
        if is_verbose():
            print("dos2unix '%s'" % fname)

def dos2unix_tree():
    for root, dirs, files in os.walk('src'):
        for f in files:
            dos2unix(os.path.join(root, f))


def check_eol():
    if not IS_WINDOWS:
        # Linux/OSX/BSD check if the end-of-line is cr/lf
        if is_cr_lf('LICENSE.txt'):
            if is_verbose():
                print("Fixing end of line...")
            dos2unix_tree()

if os.name == 'nt':
    IS_WINDOWS=True
    # Visual Studio already displays the files being compiled
    SHOW_CPPS=False
elif os.name == 'posix':
    if os.uname()[0] == 'Darwin':
        IS_OSX=True
    elif os.uname()[0] == 'Linux':
        IS_LINUX=True
    elif os.uname()[0] == 'GNU':
        IS_HURD=True
    elif os.uname()[0] == 'FreeBSD':
        IS_FREEBSD=True
    elif os.uname()[0] == 'NetBSD':
        IS_NETBSD=True
    elif os.uname()[0] == 'OpenBSD':
        IS_OPENBSD=True
    elif os.uname()[0] == 'SunOS':
        IS_SUNOS=True
    elif os.uname()[0][:6] == 'CYGWIN':
        IS_CYGWIN=True
        if (CC != None and "mingw" in CC):
            IS_CYGWIN_MINGW=True
    elif os.uname()[0].startswith('MSYS_NT') or os.uname()[0].startswith('MINGW'):
        IS_MSYS2=True
        if os.uname()[4] == 'x86_64':
            LINUX_X64=True
        else:
            LINUX_X64=False
            

def display_help(exit_code):
    print("mk_make.py: Z3 Makefile generator\n")
    print("This script generates the Makefile for the Z3 theorem prover.")
    print("It must be executed from the Z3 root directory.")
    print("\nOptions:")
    print("  -h, --help                    display this message.")
    print("  -s, --silent                  do not print verbose messages.")
    if not IS_WINDOWS:
        print("  -p <dir>, --prefix=<dir>      installation prefix (default: %s)." % PREFIX)
    else:
        print("  --parallel=num                use cl option /MP with 'num' parallel processes")
    print("  --pypkgdir=<dir>              Force a particular Python package directory (default %s)" % PYTHON_PACKAGE_DIR)
    print("  -b <subdir>, --build=<subdir>  subdirectory where Z3 will be built (default: %s)." % BUILD_DIR)
    print("  --githash=hash                include the given hash in the binaries.")
    print("  --git-describe                include the output of 'git describe' in the version information.")
    print("  -d, --debug                   compile Z3 in debug mode.")
    print("  -t, --trace                   enable tracing in release mode.")
    if IS_WINDOWS:
        print("  --guardcf                     enable Control Flow Guard runtime checks.")
        print("  -x, --x64                     create 64 binary when using Visual Studio.")
    else:
        print("  --x86                         force 32-bit x86 build on x64 systems.")
    print("  -m, --makefiles               generate only makefiles.")
    if IS_WINDOWS:
        print("  -v, --vsproj                  generate Visual Studio Project Files.")
        print("  --optimize                    generate optimized code during linking.")
    print("  --dotnet                      generate .NET platform bindings.")
    print("  --dotnet-key=<file>           sign the .NET assembly using the private key in <file>.")
    print("  --java                        generate Java bindings.")
    print("  --ml                          generate OCaml bindings.")
    print("  --js                          generate JScript bindings.")
    print("  --python                      generate Python bindings.")
    print("  --staticlib                   build Z3 static library.")
    print("  --staticbin                   build a statically linked Z3 binary.")
    if not IS_WINDOWS:
        print("  -g, --gmp                     use GMP.")
        print("  --gprof                       enable gprof")
    print("  --log-sync                    synchronize access to API log files to enable multi-thread API logging.")
    print("  --single-threaded             non-thread-safe build")
    print("")
    print("Some influential environment variables:")
    if not IS_WINDOWS:
        print("  CXX        C++ compiler")
        print("  CC         C compiler")
        print("  LDFLAGS    Linker flags, e.g., -L<lib dir> if you have libraries in a non-standard directory")
        print("  CPPFLAGS   Preprocessor flags, e.g., -I<include dir> if you have header files in a non-standard directory")
        print("  CXXFLAGS   C++ compiler flags")
    print("  JDK_HOME   JDK installation directory (only relevant if -j or --java option is provided)")
    print("  JNI_HOME   JNI bindings directory (only relevant if -j or --java option is provided)")
    print("  OCAMLC     Ocaml byte-code compiler (only relevant with --ml)")
    print("  OCAMLFIND  Ocaml find tool (only relevant with --ml)")
    print("  OCAMLOPT   Ocaml native compiler (only relevant with --ml)")
    print("  OCAML_LIB  Ocaml library directory (only relevant with --ml)")
    print("  Z3_INSTALL_BIN_DIR Install directory for binaries relative to install prefix")
    print("  Z3_INSTALL_LIB_DIR Install directory for libraries relative to install prefix")
    print("  Z3_INSTALL_INCLUDE_DIR Install directory for header files relative to install prefix")
    print("  Z3_INSTALL_PKGCONFIG_DIR Install directory for pkgconfig files relative to install prefix")
    exit(exit_code)

# Parse configuration option for mk_make script
def parse_options():
    global VERBOSE, DEBUG_MODE, IS_WINDOWS, VS_X64, ONLY_MAKEFILES, SHOW_CPPS, VS_PROJ, TRACE, VS_PAR, VS_PAR_NUM
    global DOTNET_CORE_ENABLED, DOTNET_KEY_FILE, JAVA_ENABLED, ML_ENABLED, JS_ENABLED, STATIC_LIB, STATIC_BIN, PREFIX, GMP, PYTHON_PACKAGE_DIR, GPROF, GIT_HASH, GIT_DESCRIBE, PYTHON_INSTALL_ENABLED, PYTHON_ENABLED
    global LINUX_X64, SLOW_OPTIMIZE, LOG_SYNC, SINGLE_THREADED
    global GUARD_CF, ALWAYS_DYNAMIC_BASE
    try:
        options, remainder = getopt.gnu_getopt(sys.argv[1:],
                                               'b:df:sxhmcvtnp:gj',
                                               ['build=', 'debug', 'silent', 'x64', 'help', 'makefiles', 'showcpp', 'vsproj', 'guardcf',
                                                'trace', 'dotnet', 'dotnet-key=', 'staticlib', 'prefix=', 'gmp', 'java', 'parallel=', 'gprof', 'js',
                                                'githash=', 'git-describe', 'x86', 'ml', 'optimize', 'pypkgdir=', 'python', 'staticbin', 'log-sync', 'single-threaded'])
    except:
        print("ERROR: Invalid command line option")
        display_help(1)

    for opt, arg in options:
        print('opt = %s, arg = %s' % (opt, arg))
        if opt in ('-b', '--build'):
            if arg == 'src':
                raise MKException('The src directory should not be used to host the Makefile')
            set_build_dir(arg)
        elif opt in ('-s', '--silent'):
            VERBOSE = False
        elif opt in ('-d', '--debug'):
            DEBUG_MODE = True
        elif opt in ('-x', '--x64'):
            if not IS_WINDOWS:
                raise MKException('x64 compilation mode can only be specified when using Visual Studio')
            VS_X64 = True
        elif opt in ('--x86'):
            LINUX_X64=False
        elif opt in ('-h', '--help'):
            display_help(0)
        elif opt in ('-m', '--makefiles'):
            ONLY_MAKEFILES = True
        elif opt in ('-c', '--showcpp'):
            SHOW_CPPS = True
        elif opt in ('-v', '--vsproj'):
            VS_PROJ = True
        elif opt in ('-t', '--trace'):
            TRACE = True
        elif opt in ('--dotnet',):
            DOTNET_CORE_ENABLED = True
        elif opt in ('--dotnet-key'):
            DOTNET_KEY_FILE = arg
        elif opt in ('--staticlib'):
            STATIC_LIB = True
        elif opt in ('--staticbin'):
            STATIC_BIN = True
        elif opt in ('--optimize'):
            SLOW_OPTIMIZE = True
        elif not IS_WINDOWS and opt in ('-p', '--prefix'):
            PREFIX = arg
        elif opt in ('--pypkgdir'):
            PYTHON_PACKAGE_DIR = arg
        elif IS_WINDOWS and opt == '--parallel':
            VS_PAR = True
            VS_PAR_NUM = int(arg)
        elif opt in ('-g', '--gmp'):
            GMP = True
        elif opt in ('-j', '--java'):
            JAVA_ENABLED = True
        elif opt == '--gprof':
            GPROF = True
        elif opt == '--githash':
            GIT_HASH=arg
        elif opt == '--git-describe':
            GIT_DESCRIBE = True
        elif opt in ('', '--ml'):
            ML_ENABLED = True
        elif opt == "--js":
            JS_ENABLED = True
        elif opt in ('', '--log-sync'):
            LOG_SYNC = True
        elif opt == '--single-threaded':
            SINGLE_THREADED = True
        elif opt in ('--python'):
            PYTHON_ENABLED = True
            PYTHON_INSTALL_ENABLED = True
        elif opt == '--guardcf':
            GUARD_CF = True
            ALWAYS_DYNAMIC_BASE = True # /GUARD:CF requires /DYNAMICBASE
        else:
            print("ERROR: Invalid command line option '%s'" % opt)
            display_help(1)


# Return a list containing a file names included using '#include' in
# the given C/C++ file named fname.
def extract_c_includes(fname):
    result = {}
    # We look for well behaved #include directives
    std_inc_pat     = re.compile("[ \t]*#include[ \t]*\"(.*)\"[ \t]*")
    system_inc_pat  = re.compile("[ \t]*#include[ \t]*\<.*\>[ \t]*")
    # We should generate and error for any occurrence of #include that does not match the previous pattern.
    non_std_inc_pat = re.compile(".*#include.*")

    f = io.open(fname, encoding='utf-8', mode='r')
    linenum = 1
    for line in f:
        m1 = std_inc_pat.match(line)
        if m1: 
            root_file_name = m1.group(1)
            slash_pos =  root_file_name.rfind('/')
            if slash_pos >= 0  and root_file_name.find("..") < 0 : #it is a hack for lp include files that behave as continued from "src"
                # print(root_file_name)
                root_file_name = root_file_name[slash_pos+1:]
            result[root_file_name] = m1.group(1)
        elif not system_inc_pat.match(line) and non_std_inc_pat.match(line):
            raise MKException("Invalid #include directive at '%s':%s" % (fname, line))
        linenum = linenum + 1
    f.close()
    return result


# Given a path dir1/subdir2/subdir3 returns ../../..
def reverse_path(p):
    # Filter out empty components (e.g. will have one if path ends in a slash)
    l = list(filter(lambda x: len(x) > 0, p.split(os.sep)))
    n = len(l)
    r = '..'
    for i in range(1, n):
        r = os.path.join(r, '..')
    return r

def mk_dir(d):
    if not os.path.exists(d):
        os.makedirs(d)

def set_build_dir(d):
    global BUILD_DIR, REV_BUILD_DIR
    BUILD_DIR = norm_path(d)
    REV_BUILD_DIR = reverse_path(d)

def set_z3js_dir(p):
    global SRC_DIR, Z3JS_SRC_DIR
    p = norm_path(p)
    full = os.path.join(SRC_DIR, p)
    if not os.path.exists(full):
        raise MKException("Python bindings directory '%s' does not exist" % full)
    Z3JS_SRC_DIR = full
    if VERBOSE:
        print("Js bindings directory was detected.")

def set_z3py_dir(p):
    global SRC_DIR, Z3PY_SRC_DIR
    p = norm_path(p)
    full = os.path.join(SRC_DIR, p)
    if not os.path.exists(full):
        raise MKException("Python bindings directory '%s' does not exist" % full)
    Z3PY_SRC_DIR = full
    if VERBOSE:
        print("Python bindings directory was detected.")

_UNIQ_ID = 0

def mk_fresh_name(prefix):
    global _UNIQ_ID
    r = '%s_%s' % (prefix, _UNIQ_ID)
    _UNIQ_ID = _UNIQ_ID + 1
    return r

_Id = 0
_Components = []
_ComponentNames = set()
_Name2Component = {}
_Processed_Headers = set()

# Return the Component object named name
def get_component(name):
    return _Name2Component[name]

def get_components():
    return _Components

# Return the directory where the python bindings are located.
def get_z3py_dir():
    return Z3PY_SRC_DIR

# Return directory where the js bindings are located
def get_z3js_dir():
    return Z3JS_SRC_DIR

# Return true if in verbose mode
def is_verbose():
    return VERBOSE

def is_java_enabled():
    return JAVA_ENABLED

def is_ml_enabled():
    return ML_ENABLED

def is_js_enabled():
    return JS_ENABLED

def is_dotnet_core_enabled():
    return DOTNET_CORE_ENABLED

def is_python_enabled():
    return PYTHON_ENABLED

def is_python_install_enabled():
    return PYTHON_INSTALL_ENABLED

def is_compiler(given, expected):
    """
    Return True if the 'given' compiler is the expected one.
    >>> is_compiler('g++', 'g++')
    True
    >>> is_compiler('/home/g++', 'g++')
    True
    >>> is_compiler(os.path.join('home', 'g++'), 'g++')
    True
    >>> is_compiler('clang++', 'g++')
    False
    >>> is_compiler(os.path.join('home', 'clang++'), 'clang++')
    True
    """
    if given == expected:
        return True
    if len(expected) < len(given):
        return given[len(given) - len(expected) - 1] == os.sep and given[len(given) - len(expected):] == expected
    return False

def is_CXX_gpp():
    return is_compiler(CXX, 'g++')

def is_clang_in_gpp_form(cc):
    str = check_output([cc, '--version'])
    try:
       version_string = str.encode('utf-8')
    except:
       version_string = str
    clang = 'clang'.encode('utf-8')
    return version_string.find(clang) != -1

def is_CXX_clangpp():
    if is_compiler(CXX, 'g++'):
        return is_clang_in_gpp_form(CXX)
    return is_compiler(CXX, 'clang++')

def get_files_with_ext(path, ext):
    return filter(lambda f: f.endswith(ext), os.listdir(path))

def get_cpp_files(path):
    return get_files_with_ext(path,'.cpp')

def get_c_files(path):
    return get_files_with_ext(path,'.c')

def get_cs_files(path):
    return get_files_with_ext(path,'.cs')

def get_java_files(path):
    return get_files_with_ext(path,'.java')

def get_ml_files(path):
    return get_files_with_ext(path,'.ml')

def find_all_deps(name, deps):
    new_deps = []
    for dep in deps:
        if dep in _ComponentNames:
            if not (dep in new_deps):
                new_deps.append(dep)
            for dep_dep in get_component(dep).deps:
                if not (dep_dep in new_deps):
                    new_deps.append(dep_dep)
        else:
            raise MKException("Unknown component '%s' at '%s'." % (dep, name))
    return new_deps

class Component:
    def __init__(self, name, path, deps):
        global BUILD_DIR, SRC_DIR, REV_BUILD_DIR
        if name in _ComponentNames:
            raise MKException("Component '%s' was already defined." % name)
        if path is None:
            path = name
        self.name = name
        path = norm_path(path)
        self.path = path
        self.deps = find_all_deps(name, deps)
        self.build_dir = path
        self.src_dir   = os.path.join(SRC_DIR, path)
        self.to_src_dir = os.path.join(REV_BUILD_DIR, self.src_dir)

    def get_link_name(self):
        return os.path.join(self.build_dir, self.name) + '$(LIB_EXT)'


    # Find fname in the include paths for the given component.
    # ownerfile is only used for creating error messages.
    # That is, we were looking for fname when processing ownerfile
    def find_file(self, fname, ownerfile, orig_include=None):
        full_fname = os.path.join(self.src_dir, fname)

        # Store all our possible locations
        possibilities = set()

        # If the our file exists in the current directory, then we store it
        if os.path.exists(full_fname):

            # We cannot return here, as we might have files with the same
            # basename, but different include paths
            possibilities.add(self)

        for dep in self.deps:
            c_dep = get_component(dep)
            full_fname = os.path.join(c_dep.src_dir, fname)
            if os.path.exists(full_fname):
                possibilities.add(c_dep)

        if possibilities:

            # We have ambiguity
            if len(possibilities) > 1:

                # We expect orig_path to be non-None here, so we can disambiguate
                assert orig_include is not None

                # Get the original directory name
                orig_dir = os.path.dirname(orig_include)

                # Iterate through all of the possibilities
                for possibility in possibilities:

                    path = possibility.path.replace("\\","/")
                    # If we match the suffix of the path ...
                    if path.endswith(orig_dir):

                        # ... use our new match
                        return possibility

            # This means we didn't make an exact match ...
            #
            # We return any one possibility, just to ensure we don't break Z3's
            # builds
            return possibilities.pop()

        raise MKException("Failed to find include file '%s' for '%s' when processing '%s'." % (fname, ownerfile, self.name))

    # Display all dependencies of file basename located in the given component directory.
    # The result is displayed at out
    def add_cpp_h_deps(self, out, basename):
        includes = extract_c_includes(os.path.join(self.src_dir, basename))
        out.write(os.path.join(self.to_src_dir, basename))
        for include, orig_include in includes.items():
            owner = self.find_file(include, basename, orig_include)
            out.write(' %s.node' % os.path.join(owner.build_dir, include))

    # Add a rule for each #include directive in the file basename located at the current component.
    def add_rule_for_each_include(self, out, basename):
        fullname = os.path.join(self.src_dir, basename)
        includes = extract_c_includes(fullname)
        for include, orig_include in includes.items():
            owner = self.find_file(include, fullname, orig_include)
            owner.add_h_rule(out, include)

    # Display a Makefile rule for an include file located in the given component directory.
    # 'include' is something of the form: ast.h, polynomial.h
    # The rule displayed at out is of the form
    #     ast/ast_pp.h.node : ../src/util/ast_pp.h util/util.h.node ast/ast.h.node
    #       @echo "done" > ast/ast_pp.h.node
    def add_h_rule(self, out, include):
        include_src_path   = os.path.join(self.to_src_dir, include)
        if include_src_path in _Processed_Headers:
            return
        _Processed_Headers.add(include_src_path)
        self.add_rule_for_each_include(out, include)
        include_node = '%s.node' % os.path.join(self.build_dir, include)
        out.write('%s: ' % include_node)
        self.add_cpp_h_deps(out, include)
        out.write('\n')
        out.write('\t@echo done > %s\n' % include_node)

    def add_cpp_rules(self, out, include_defs, cppfile):
        self.add_rule_for_each_include(out, cppfile)
        objfile = '%s$(OBJ_EXT)' % os.path.join(self.build_dir, os.path.splitext(cppfile)[0])
        srcfile = os.path.join(self.to_src_dir, cppfile)
        out.write('%s: ' % objfile)
        self.add_cpp_h_deps(out, cppfile)
        out.write('\n')
        if SHOW_CPPS:
            out.write('\t@echo %s\n' % os.path.join(self.src_dir, cppfile))
        out.write('\t@$(CXX) $(CXXFLAGS) $(%s) $(CXX_OUT_FLAG)%s %s\n' % (include_defs, objfile, srcfile))

    def mk_makefile(self, out):
        include_defs = mk_fresh_name('includes')
        out.write('%s =' % include_defs)
        for dep in self.deps:
            out.write(' -I%s' % get_component(dep).to_src_dir)
        out.write(' -I%s' % os.path.join(REV_BUILD_DIR,"src"))
        out.write('\n')
        mk_dir(os.path.join(BUILD_DIR, self.build_dir))
        if VS_PAR and IS_WINDOWS:
            cppfiles = list(get_cpp_files(self.src_dir))
            dependencies = set()
            for cppfile in cppfiles:
                dependencies.add(os.path.join(self.to_src_dir, cppfile))
                self.add_rule_for_each_include(out, cppfile)
                includes = extract_c_includes(os.path.join(self.src_dir, cppfile))
                for include, orig_include in includes.items():
                    owner = self.find_file(include, cppfile, orig_include)
                    dependencies.add('%s.node' % os.path.join(owner.build_dir, include))
            for cppfile in cppfiles:
                out.write('%s$(OBJ_EXT) ' % os.path.join(self.build_dir, os.path.splitext(cppfile)[0]))
            out.write(': ')
            for dep in dependencies:
                out.write(dep)
                out.write(' ')
            out.write('\n')
            out.write('\t@$(CXX) $(CXXFLAGS) /MP%s $(%s)' % (VS_PAR_NUM, include_defs))
            for cppfile in cppfiles:
                out.write(' ')
                out.write(os.path.join(self.to_src_dir, cppfile))
            out.write('\n')
            out.write('\tmove *.obj %s\n' % self.build_dir)
        else:
            for cppfile in get_cpp_files(self.src_dir):
                self.add_cpp_rules(out, include_defs, cppfile)

    # Return true if the component should be included in the all: rule
    def main_component(self):
        return False

    # Return true if the component contains an AssemblyInfo.cs file that needs to be updated.
    def has_assembly_info(self):
        return False

    # Return true if the component needs builder to generate an install_tactics.cpp file
    def require_install_tactics(self):
        return False

    # Return true if the component needs a def file
    def require_def_file(self):
        return False

    # Return true if the component needs builder to generate a mem_initializer.cpp file with mem_initialize() and mem_finalize() functions.
    def require_mem_initializer(self):
        return False

    def mk_install_deps(self, out):
        return

    def mk_install(self, out):
        return

    def mk_uninstall(self, out):
        return

    def is_example(self):
        return False

    # Invoked when creating a (windows) distribution package using components at build_path, and
    # storing them at dist_path
    def mk_win_dist(self, build_path, dist_path):
        return

    def mk_unix_dist(self, build_path, dist_path):
        return

    # Used to print warnings or errors after mk_make.py is done, so that they
    # are not quite as easy to miss.
    def final_info(self):
        pass

class LibComponent(Component):
    def __init__(self, name, path, deps, includes2install):
        Component.__init__(self, name, path, deps)
        self.includes2install = includes2install

    def mk_makefile(self, out):
        Component.mk_makefile(self, out)
        # generate rule for lib
        objs = []
        for cppfile in get_cpp_files(self.src_dir):
            objfile = '%s$(OBJ_EXT)' % os.path.join(self.build_dir, os.path.splitext(cppfile)[0])
            objs.append(objfile)

        libfile = '%s$(LIB_EXT)' % os.path.join(self.build_dir, self.name)
        out.write('%s:' % libfile)
        for obj in objs:
            out.write(' ')
            out.write(obj)
        out.write('\n')
        out.write('\t@$(AR) $(AR_FLAGS) $(AR_OUTFLAG)%s' % libfile)
        for obj in objs:
            out.write(' ')
            out.write(obj)
        out.write('\n')
        out.write('%s: %s\n\n' % (self.name, libfile))

    def mk_install_deps(self, out):
        return

    def mk_install(self, out):
        for include in self.includes2install:
            MakeRuleCmd.install_files(
                out,
                os.path.join(self.to_src_dir, include),
                os.path.join(INSTALL_INCLUDE_DIR, include)
            )

    def mk_uninstall(self, out):
        for include in self.includes2install:
            MakeRuleCmd.remove_installed_files(out, os.path.join(INSTALL_INCLUDE_DIR, include))

    def mk_win_dist(self, build_path, dist_path):
        mk_dir(os.path.join(dist_path, INSTALL_INCLUDE_DIR))
        for include in self.includes2install:
            shutil.copy(os.path.join(self.src_dir, include),
                        os.path.join(dist_path, INSTALL_INCLUDE_DIR, include))

    def mk_unix_dist(self, build_path, dist_path):
        self.mk_win_dist(build_path, dist_path)

# "Library" containing only .h files. This is just a placeholder for includes files to be installed.
class HLibComponent(LibComponent):
    def __init__(self, name, path, includes2install):
        LibComponent.__init__(self, name, path, [], includes2install)

    def mk_makefile(self, out):
        return

# Auxiliary function for sort_components
def comp_components(c1, c2):
    id1 = get_component(c1).id
    id2 = get_component(c2).id
    return id2 - id1

# Sort components based on (reverse) definition time
def sort_components(cnames):
    return sorted(cnames, key=lambda c: get_component(c).id, reverse=True)

class ExeComponent(Component):
    def __init__(self, name, exe_name, path, deps, install):
        Component.__init__(self, name, path, deps)
        if exe_name is None:
            exe_name = name
        self.exe_name = exe_name
        self.install = install

    def mk_makefile(self, out):
        Component.mk_makefile(self, out)
        # generate rule for exe

        exefile = '%s$(EXE_EXT)' % self.exe_name
        out.write('%s:' % exefile)
        deps = sort_components(self.deps)
        objs = []
        for cppfile in get_cpp_files(self.src_dir):
            objfile = '%s$(OBJ_EXT)' % os.path.join(self.build_dir, os.path.splitext(cppfile)[0])
            objs.append(objfile)
        for obj in objs:
            out.write(' ')
            out.write(obj)
        for dep in deps:
            c_dep = get_component(dep)
            out.write(' ' + c_dep.get_link_name())
        out.write('\n')
        extra_opt = '-static' if not IS_WINDOWS and STATIC_BIN else ''
        out.write('\t$(LINK) %s $(LINK_OUT_FLAG)%s $(LINK_FLAGS)' % (extra_opt, exefile))
        for obj in objs:
            out.write(' ')
            out.write(obj)
        for dep in deps:
            c_dep = get_component(dep)
            out.write(' ' + c_dep.get_link_name())
        out.write(' $(LINK_EXTRA_FLAGS)\n')
        out.write('%s: %s\n\n' % (self.name, exefile))

    def require_install_tactics(self):
        return ('tactic' in self.deps) and ('cmd_context' in self.deps)

    def require_mem_initializer(self):
        return True

    # All executables (to be installed) are included in the all: rule
    def main_component(self):
        return self.install

    def mk_install_deps(self, out):
        if self.install:
            exefile = '%s$(EXE_EXT)' % self.exe_name
            out.write('%s' % exefile)

    def mk_install(self, out):
        if self.install:
            exefile = '%s$(EXE_EXT)' % self.exe_name
            MakeRuleCmd.install_files(out, exefile, os.path.join(INSTALL_BIN_DIR, exefile))

    def mk_uninstall(self, out):
        if self.install:
            exefile = '%s$(EXE_EXT)' % self.exe_name
            MakeRuleCmd.remove_installed_files(out, os.path.join(INSTALL_BIN_DIR, exefile))

    def mk_win_dist(self, build_path, dist_path):
        if self.install:
            mk_dir(os.path.join(dist_path, INSTALL_BIN_DIR))
            shutil.copy('%s.exe' % os.path.join(build_path, self.exe_name),
                        '%s.exe' % os.path.join(dist_path, INSTALL_BIN_DIR, self.exe_name))

    def mk_unix_dist(self, build_path, dist_path):
        if self.install:
            mk_dir(os.path.join(dist_path, INSTALL_BIN_DIR))
            shutil.copy(os.path.join(build_path, self.exe_name),
                        os.path.join(dist_path, INSTALL_BIN_DIR, self.exe_name))


class ExtraExeComponent(ExeComponent):
    def __init__(self, name, exe_name, path, deps, install):
        ExeComponent.__init__(self, name, exe_name, path, deps, install)

    def main_component(self):
        return False

    def require_mem_initializer(self):
        return False

def get_so_ext():
    sysname = os.uname()[0]
    if sysname == 'Darwin':
        return 'dylib'
    elif sysname == 'Linux' or sysname == 'GNU' or sysname == 'FreeBSD' or sysname == 'NetBSD' or sysname == 'OpenBSD':
        return 'so'
    elif sysname == 'CYGWIN' or sysname.startswith('MSYS_NT') or sysname.startswith('MINGW'):
        return 'dll'
    else:
        assert(False)
        return 'dll'

class DLLComponent(Component):
    def __init__(self, name, dll_name, path, deps, export_files, reexports, install, static, staging_link=None):
        Component.__init__(self, name, path, deps)
        if dll_name is None:
            dll_name = name
        self.dll_name = dll_name
        self.export_files = export_files
        self.reexports = reexports
        self.install = install
        self.static = static
        self.staging_link = staging_link    # link a copy of the shared object into this directory on build

    def get_link_name(self):
        if self.static:
            return os.path.join(self.build_dir, self.name) + '$(LIB_EXT)'
        else:
            return self.name + '$(SO_EXT)'

    def dll_file(self):
        """
            Return file name of component suitable for use in a Makefile
        """
        return '%s$(SO_EXT)' % self.dll_name

    def install_path(self):
        """
            Return install location of component (relative to prefix)
            suitable for use in a Makefile
        """
        return os.path.join(INSTALL_LIB_DIR, self.dll_file())

    def mk_makefile(self, out):
        Component.mk_makefile(self, out)
        # generate rule for (SO_EXT)
        out.write('%s:' % self.dll_file())
        deps = sort_components(self.deps)
        objs = []
        for cppfile in get_cpp_files(self.src_dir):
            objfile = '%s$(OBJ_EXT)' % os.path.join(self.build_dir, os.path.splitext(cppfile)[0])
            objs.append(objfile)
        # Explicitly include obj files of reexport. This fixes problems with exported symbols on Linux and OSX.
        for reexport in self.reexports:
            reexport = get_component(reexport)
            for cppfile in get_cpp_files(reexport.src_dir):
                objfile = '%s$(OBJ_EXT)' % os.path.join(reexport.build_dir, os.path.splitext(cppfile)[0])
                objs.append(objfile)
        for obj in objs:
            out.write(' ')
            out.write(obj)
        for dep in deps:
            if dep not in self.reexports:
                c_dep = get_component(dep)
                out.write(' ' + c_dep.get_link_name())
        out.write('\n')
        out.write('\t$(LINK) $(SLINK_OUT_FLAG)%s $(SLINK_FLAGS)' % self.dll_file())
        for obj in objs:
            out.write(' ')
            out.write(obj)
        for dep in deps:
            if dep not in self.reexports:
                c_dep = get_component(dep)
                out.write(' ' + c_dep.get_link_name())
        out.write(' $(SLINK_EXTRA_FLAGS)')
        if IS_WINDOWS:
            out.write(' /DEF:%s.def' % os.path.join(self.to_src_dir, self.name))
        if self.staging_link:
            if IS_WINDOWS:
                out.write('\n\tcopy %s %s' % (self.dll_file(), self.staging_link))
            elif IS_OSX:
                out.write('\n\tcp %s %s' % (self.dll_file(), self.staging_link))
            else:
                out.write('\n\tln -f -s %s %s' % (os.path.join(reverse_path(self.staging_link), self.dll_file()), self.staging_link))
        out.write('\n')
        if self.static:
            if IS_WINDOWS:
                libfile = '%s-static$(LIB_EXT)' % self.dll_name
            else:
                libfile = '%s$(LIB_EXT)' % self.dll_name
            self.mk_static(out, libfile)
            out.write('%s: %s %s\n\n' % (self.name, self.dll_file(), libfile))
        else:
            out.write('%s: %s\n\n' % (self.name, self.dll_file()))

    def mk_static(self, out, libfile):
        # generate rule for lib
        objs = []
        for cppfile in get_cpp_files(self.src_dir):
            objfile = '%s$(OBJ_EXT)' % os.path.join(self.build_dir, os.path.splitext(cppfile)[0])
            objs.append(objfile)
        # we have to "reexport" all object files
        for dep in self.deps:
            dep = get_component(dep)
            for cppfile in get_cpp_files(dep.src_dir):
                objfile = '%s$(OBJ_EXT)' % os.path.join(dep.build_dir, os.path.splitext(cppfile)[0])
                objs.append(objfile)
        out.write('%s:' % libfile)
        for obj in objs:
            out.write(' ')
            out.write(obj)
        out.write('\n')
        out.write('\t@$(AR) $(AR_FLAGS) $(AR_OUTFLAG)%s' % libfile)
        for obj in objs:
            out.write(' ')
            out.write(obj)
        out.write('\n')

    def main_component(self):
        return self.install

    def require_install_tactics(self):
        return ('tactic' in self.deps) and ('cmd_context' in self.deps)

    def require_mem_initializer(self):
        return True

    def require_def_file(self):
        return IS_WINDOWS and self.export_files

    def mk_install_deps(self, out):
        out.write('%s$(SO_EXT)' % self.dll_name)
        if self.static:
            out.write(' %s$(LIB_EXT)' % self.dll_name)

    def mk_install(self, out):
        if self.install:
            MakeRuleCmd.install_files(out, self.dll_file(), self.install_path())
            if self.static:
                libfile = '%s$(LIB_EXT)' % self.dll_name
                MakeRuleCmd.install_files(out, libfile, os.path.join(INSTALL_LIB_DIR, libfile))

    def mk_uninstall(self, out):
        MakeRuleCmd.remove_installed_files(out, self.install_path())
        libfile = '%s$(LIB_EXT)' % self.dll_name
        MakeRuleCmd.remove_installed_files(out, os.path.join(INSTALL_LIB_DIR, libfile))

    def mk_win_dist(self, build_path, dist_path):
        if self.install:
            mk_dir(os.path.join(dist_path, INSTALL_BIN_DIR))
            shutil.copy('%s.dll' % os.path.join(build_path, self.dll_name),
                        '%s.dll' % os.path.join(dist_path, INSTALL_BIN_DIR, self.dll_name))
            shutil.copy('%s.pdb' % os.path.join(build_path, self.dll_name),
                        '%s.pdb' % os.path.join(dist_path, INSTALL_BIN_DIR, self.dll_name))
            shutil.copy('%s.lib' % os.path.join(build_path, self.dll_name),
                        '%s.lib' % os.path.join(dist_path, INSTALL_BIN_DIR, self.dll_name))

    def mk_unix_dist(self, build_path, dist_path):
        if self.install:
            mk_dir(os.path.join(dist_path, INSTALL_BIN_DIR))
            so = get_so_ext()
            shutil.copy('%s.%s' % (os.path.join(build_path, self.dll_name), so),
                        '%s.%s' % (os.path.join(dist_path, INSTALL_BIN_DIR, self.dll_name), so))
            shutil.copy('%s.a' % os.path.join(build_path, self.dll_name),
                        '%s.a' % os.path.join(dist_path, INSTALL_BIN_DIR, self.dll_name))

class JsComponent(Component):
    def __init__(self):
         Component.__init__(self, "js", None, [])

    def main_component(self):
        return False

    def mk_win_dist(self, build_path, dist_path):
        return

    def mk_unix_dist(self, build_path, dist_path):
        return

    def mk_makefile(self, out):
        return

class PythonComponent(Component):
    def __init__(self, name, libz3Component):
        assert isinstance(libz3Component, DLLComponent)
        global PYTHON_ENABLED
        Component.__init__(self, name, None, [])
        self.libz3Component = libz3Component

    def main_component(self):
        return False

    def mk_win_dist(self, build_path, dist_path):
        if not is_python_enabled():
            return

        src = os.path.join(build_path, 'python', 'z3')
        dst = os.path.join(dist_path, INSTALL_BIN_DIR, 'python', 'z3')
        if os.path.exists(dst):
            shutil.rmtree(dst)
        shutil.copytree(src, dst)

    def mk_unix_dist(self, build_path, dist_path):
        self.mk_win_dist(build_path, dist_path)

    def mk_makefile(self, out):
        return

class PythonInstallComponent(Component):
    def __init__(self, name, libz3Component):
        assert isinstance(libz3Component, DLLComponent)
        global PYTHON_INSTALL_ENABLED
        Component.__init__(self, name, None, [])
        self.pythonPkgDir = None
        self.in_prefix_install = True
        self.libz3Component = libz3Component

        if not PYTHON_INSTALL_ENABLED:
            return

        if IS_WINDOWS:
            # Installing under Windows doesn't make sense as the install prefix is used
            # but that doesn't make sense under Windows
            # CMW: It makes perfectly good sense; the prefix is Python's sys.prefix,
            # i.e., something along the lines of C:\Python\... At the moment we are not
            # sure whether we would want to install libz3.dll into that directory though.
            PYTHON_INSTALL_ENABLED = False
            return
        else:
            PYTHON_INSTALL_ENABLED = True

        if IS_WINDOWS or IS_OSX:
            # Use full path that is possibly outside of install prefix
            self.in_prefix_install = PYTHON_PACKAGE_DIR.startswith(PREFIX)
            self.pythonPkgDir = strip_path_prefix(PYTHON_PACKAGE_DIR, PREFIX)
        else:
            # Use path inside the prefix (should be the normal case on Linux)
            # CMW: Also normal on *BSD?
            if not PYTHON_PACKAGE_DIR.startswith(PREFIX):
                raise MKException(('The python package directory ({}) must live ' +
                    'under the install prefix ({}) to install the python bindings.' +
                    'Use --pypkgdir and --prefix to set the python package directory ' +
                    'and install prefix respectively. Note that the python package ' +
                    'directory does not need to exist and will be created if ' +
                    'necessary during install.').format(
                        PYTHON_PACKAGE_DIR,
                        PREFIX))
            self.pythonPkgDir = strip_path_prefix(PYTHON_PACKAGE_DIR, PREFIX)
            self.in_prefix_install = True

        if self.in_prefix_install:
            assert not os.path.isabs(self.pythonPkgDir)

    def final_info(self):
        if not PYTHON_PACKAGE_DIR.startswith(PREFIX) and PYTHON_INSTALL_ENABLED:
            print("Warning: The detected Python package directory (%s) is not "
                  "in the installation prefix (%s). This can lead to a broken "
                  "Python API installation. Use --pypkgdir= to change the "
                  "Python package directory." % (PYTHON_PACKAGE_DIR, PREFIX))

    def main_component(self):
        return False

    def mk_install(self, out):
        if not is_python_install_enabled():
            return
        MakeRuleCmd.make_install_directory(out,
                                           os.path.join(self.pythonPkgDir, 'z3'),
                                           in_prefix=self.in_prefix_install)
        MakeRuleCmd.make_install_directory(out,
                                           os.path.join(self.pythonPkgDir, 'z3', 'lib'),
                                           in_prefix=self.in_prefix_install)

        # Sym-link or copy libz3 into python package directory
        if IS_WINDOWS or IS_OSX:
            MakeRuleCmd.install_files(out,
                                      self.libz3Component.dll_file(),
                                      os.path.join(self.pythonPkgDir, 'z3', 'lib',
                                                   self.libz3Component.dll_file()),
                                      in_prefix=self.in_prefix_install
                                     )
        else:
            # Create symbolic link to save space.
            # It's important that this symbolic link be relative (rather
            # than absolute) so that the install is relocatable (needed for
            # staged installs that use DESTDIR).
            MakeRuleCmd.create_relative_symbolic_link(out,
                                                      self.libz3Component.install_path(),
                                                      os.path.join(self.pythonPkgDir, 'z3', 'lib',
                                                                   self.libz3Component.dll_file()
                                                                  ),
                                                     )

        MakeRuleCmd.install_files(out, os.path.join('python', 'z3', '*.py'),
                                  os.path.join(self.pythonPkgDir, 'z3'),
                                  in_prefix=self.in_prefix_install)
        if sys.version >= "3":
            pythonPycacheDir = os.path.join(self.pythonPkgDir, 'z3', '__pycache__')
            MakeRuleCmd.make_install_directory(out,
                                               pythonPycacheDir,
                                               in_prefix=self.in_prefix_install)
            MakeRuleCmd.install_files(out,
                                      os.path.join('python', 'z3', '__pycache__', '*.pyc'),
                                      pythonPycacheDir,
                                      in_prefix=self.in_prefix_install)
        else:
            MakeRuleCmd.install_files(out,
                                      os.path.join('python', 'z3', '*.pyc'),
                                      os.path.join(self.pythonPkgDir,'z3'),
                                      in_prefix=self.in_prefix_install)

        if PYTHON_PACKAGE_DIR != distutils.sysconfig.get_python_lib():
            out.write('\t@echo Z3Py was installed at \'%s\', make sure this directory is in your PYTHONPATH environment variable.' % PYTHON_PACKAGE_DIR)

    def mk_uninstall(self, out):
        if not is_python_install_enabled():
            return
        MakeRuleCmd.remove_installed_files(out,
                                           os.path.join(self.pythonPkgDir,
                                                        self.libz3Component.dll_file()),
                                           in_prefix=self.in_prefix_install
                                          )
        MakeRuleCmd.remove_installed_files(out,
                                           os.path.join(self.pythonPkgDir, 'z3', '*.py'),
                                           in_prefix=self.in_prefix_install)
        MakeRuleCmd.remove_installed_files(out,
                                           os.path.join(self.pythonPkgDir, 'z3', '*.pyc'),
                                           in_prefix=self.in_prefix_install)
        MakeRuleCmd.remove_installed_files(out,
                                           os.path.join(self.pythonPkgDir, 'z3', '__pycache__', '*.pyc'),
                                           in_prefix=self.in_prefix_install
                                          )
        MakeRuleCmd.remove_installed_files(out,
                                           os.path.join(self.pythonPkgDir, 'z3', 'lib',
                                                        self.libz3Component.dll_file()))

    def mk_makefile(self, out):
        return

def set_key_file(self):
    global DOTNET_KEY_FILE
    # We need to give the assembly a strong name so that it
    # can be installed into the GAC with ``make install``
    if not DOTNET_KEY_FILE is None:
       self.key_file = DOTNET_KEY_FILE

    if not self.key_file is None:
       if os.path.isfile(self.key_file):
           self.key_file = os.path.abspath(self.key_file)
       elif os.path.isfile(os.path.join(self.src_dir, self.key_file)):
           self.key_file = os.path.abspath(os.path.join(self.src_dir, self.key_file))
       else:
           print("Keyfile '%s' could not be found; %s.dll will be unsigned." % (self.key_file, self.dll_name))
           self.key_file = None
    

# build for dotnet core
class DotNetDLLComponent(Component):
    def __init__(self, name, dll_name, path, deps, assembly_info_dir, default_key_file):
        Component.__init__(self, name, path, deps)
        if dll_name is None:
            dll_name = name
        if assembly_info_dir is None:
            assembly_info_dir = "."
        self.dll_name          = dll_name
        self.assembly_info_dir = assembly_info_dir
        self.key_file = default_key_file

    
    def mk_makefile(self, out):
        if not is_dotnet_core_enabled():
            return
        cs_fp_files = []
        for cs_file in get_cs_files(self.src_dir):
            cs_fp_files.append(os.path.join(self.to_src_dir, cs_file))
        if self.assembly_info_dir != '.':
            for cs_file in get_cs_files(os.path.join(self.src_dir, self.assembly_info_dir)):
                cs_fp_files.append(os.path.join(self.to_src_dir, self.assembly_info_dir, cs_file))
        dllfile = '%s.dll' % self.dll_name
        out.write('%s: %s$(SO_EXT)' % (dllfile, get_component(Z3_DLL_COMPONENT).dll_name))
        for cs_file in cs_fp_files:
            out.write(' ')
            out.write(cs_file)
        out.write('\n')
        
        set_key_file(self)
        key = ""
        if not self.key_file is None:
            key = "<AssemblyOriginatorKeyFile>%s</AssemblyOriginatorKeyFile>" % self.key_file
            key += "\n<SignAssembly>true</SignAssembly>"

        version = get_version_string(3)

        core_csproj_str = """<Project Sdk="Microsoft.NET.Sdk">

  <PropertyGroup>
    <TargetFramework>netstandard1.4</TargetFramework>
    <DefineConstants>$(DefineConstants);DOTNET_CORE</DefineConstants>
    <DebugType>portable</DebugType>
    <AssemblyName>Microsoft.Z3</AssemblyName>
    <OutputType>Library</OutputType>
    <PackageId>Microsoft.Z3</PackageId>
    <GenerateDocumentationFile>true</GenerateDocumentationFile>
    <RuntimeFrameworkVersion>1.0.4</RuntimeFrameworkVersion>
    <Version>%s</Version>
    <GeneratePackageOnBuild>true</GeneratePackageOnBuild>
    <Authors>Microsoft</Authors>
    <Company>Microsoft</Company>
    <EnableDefaultCompileItems>false</EnableDefaultCompileItems>
    <Description>Z3 is a satisfiability modulo theories solver from Microsoft Research.</Description>
    <Copyright>Copyright Microsoft Corporation. All rights reserved.</Copyright>
    <PackageTags>smt constraint solver theorem prover</PackageTags>
    %s
  </PropertyGroup>

  <ItemGroup>
    <Compile Include="..\%s\*.cs;*.cs" Exclude="bin\**;obj\**;**\*.xproj;packages\**" />
  </ItemGroup>

</Project>""" % (version, key, self.to_src_dir)

        mk_dir(os.path.join(BUILD_DIR, 'dotnet'))
        csproj = os.path.join('dotnet', 'z3.csproj')
        with open(os.path.join(BUILD_DIR, csproj), 'w') as ous:
            ous.write(core_csproj_str)

        dotnetCmdLine = [DOTNET, "build", csproj]
        
        dotnetCmdLine.extend(['-c'])
        if DEBUG_MODE:
            dotnetCmdLine.extend(['Debug'])
        else:
            dotnetCmdLine.extend(['Release'])

        path = os.path.join(os.path.abspath(BUILD_DIR), ".")
        dotnetCmdLine.extend(['-o', path])
            
        MakeRuleCmd.write_cmd(out, ' '.join(dotnetCmdLine))
        out.write('\n')        
        out.write('%s: %s\n\n' % (self.name, dllfile))

    def main_component(self):
        return is_dotnet_core_enabled()
    
    def has_assembly_info(self):
        # TBD: is this required for dotnet core given that version numbers are in z3.csproj file?
        return False

    
    def mk_win_dist(self, build_path, dist_path):
        if is_dotnet_core_enabled():
            mk_dir(os.path.join(dist_path, INSTALL_BIN_DIR))
            shutil.copy('%s.dll' % os.path.join(build_path, self.dll_name),
                        '%s.dll' % os.path.join(dist_path, INSTALL_BIN_DIR, self.dll_name))
            shutil.copy('%s.pdb' % os.path.join(build_path, self.dll_name),
                        '%s.pdb' % os.path.join(dist_path, INSTALL_BIN_DIR, self.dll_name))
            shutil.copy('%s.xml' % os.path.join(build_path, self.dll_name),
                        '%s.xml' % os.path.join(dist_path, INSTALL_BIN_DIR, self.dll_name))
            shutil.copy('%s.deps.json' % os.path.join(build_path, self.dll_name),
                        '%s.deps.json' % os.path.join(dist_path, INSTALL_BIN_DIR, self.dll_name))
            if DEBUG_MODE:
                shutil.copy('%s.pdb' % os.path.join(build_path, self.dll_name),
                            '%s.pdb' % os.path.join(dist_path, INSTALL_BIN_DIR, self.dll_name))

    def mk_unix_dist(self, build_path, dist_path):
        if is_dotnet_core_enabled():
            mk_dir(os.path.join(dist_path, INSTALL_BIN_DIR))
            shutil.copy('%s.dll' % os.path.join(build_path, self.dll_name),
                        '%s.dll' % os.path.join(dist_path, INSTALL_BIN_DIR, self.dll_name))
            shutil.copy('%s.xml' % os.path.join(build_path, self.dll_name),
                        '%s.xml' % os.path.join(dist_path, INSTALL_BIN_DIR, self.dll_name))
            shutil.copy('%s.deps.json' % os.path.join(build_path, self.dll_name),
                        '%s.deps.json' % os.path.join(dist_path, INSTALL_BIN_DIR, self.dll_name))

    def mk_install_deps(self, out):
        pass

    def mk_install(self, out):
        pass

    def mk_uninstall(self, out):
        pass

class JavaDLLComponent(Component):
    def __init__(self, name, dll_name, package_name, manifest_file, path, deps):
        Component.__init__(self, name, path, deps)
        if dll_name is None:
            dll_name = name
        self.dll_name     = dll_name
        self.package_name = package_name
        self.manifest_file = manifest_file
        self.install = not is_windows()

    def mk_makefile(self, out):
        global JAVAC
        global JAR

        if is_java_enabled():
            mk_dir(os.path.join(BUILD_DIR, 'api', 'java', 'classes'))
            dllfile = '%s$(SO_EXT)' % self.dll_name
            out.write('libz3java$(SO_EXT): libz3$(SO_EXT) %s\n' % os.path.join(self.to_src_dir, 'Native.cpp'))
            t = '\t$(CXX) $(CXXFLAGS) $(CXX_OUT_FLAG)api/java/Native$(OBJ_EXT) -I"%s" -I"%s/PLATFORM" -I%s %s/Native.cpp\n' % (JNI_HOME, JNI_HOME, get_component('api').to_src_dir, self.to_src_dir)
            if IS_OSX:
                t = t.replace('PLATFORM', 'darwin')
            elif is_linux():
                t = t.replace('PLATFORM', 'linux')
            elif is_hurd():
                t = t.replace('PLATFORM', 'hurd')
            elif IS_FREEBSD:
                t = t.replace('PLATFORM', 'freebsd')
            elif IS_NETBSD:
                t = t.replace('PLATFORM', 'netbsd')
            elif IS_OPENBSD:
                t = t.replace('PLATFORM', 'openbsd')
            elif IS_SUNOS:
                t = t.replace('PLATFORM', 'SunOS')
            elif IS_CYGWIN:
                t = t.replace('PLATFORM', 'cygwin')
            elif IS_MSYS2:
                t = t.replace('PLATFORM', 'win32')
            else:
                t = t.replace('PLATFORM', 'win32')
            out.write(t)
            if IS_WINDOWS: # On Windows, CL creates a .lib file to link against.
                out.write('\t$(SLINK) $(SLINK_OUT_FLAG)libz3java$(SO_EXT) $(SLINK_FLAGS) %s$(OBJ_EXT) libz3$(LIB_EXT)\n' %
                          os.path.join('api', 'java', 'Native'))
            else:
                out.write('\t$(SLINK) $(SLINK_OUT_FLAG)libz3java$(SO_EXT) $(SLINK_FLAGS) %s$(OBJ_EXT) libz3$(SO_EXT)\n' %
                          os.path.join('api', 'java', 'Native'))
            out.write('%s.jar: libz3java$(SO_EXT) ' % self.package_name)
            deps = ''
            for jfile in get_java_files(self.src_dir):
                deps += ('%s ' % os.path.join(self.to_src_dir, jfile))
            for jfile in get_java_files(os.path.join(self.src_dir, "enumerations")):
                deps += '%s ' % os.path.join(self.to_src_dir, 'enumerations', jfile)
            out.write(deps)
            out.write('\n')
            #if IS_WINDOWS:
            JAVAC = '"%s"' % JAVAC
            JAR = '"%s"' % JAR
            t = ('\t%s -source 1.8 -target 1.8 %s.java -d %s\n' % (JAVAC, os.path.join(self.to_src_dir, 'enumerations', '*'), os.path.join('api', 'java', 'classes')))
            out.write(t)
            t = ('\t%s -source 1.8 -target 1.8 -cp %s %s.java -d %s\n' % (JAVAC,
                                                  os.path.join('api', 'java', 'classes'),
                                                  os.path.join(self.to_src_dir, '*'),
                                                  os.path.join('api', 'java', 'classes')))
            out.write(t)
            out.write('\t%s cfm %s.jar %s -C %s .\n' % (JAR, self.package_name,
                                                         os.path.join(self.to_src_dir, 'manifest'),
                                                         os.path.join('api', 'java', 'classes')))
            out.write('java: %s.jar\n\n' % self.package_name)

    def main_component(self):
        return is_java_enabled()

    def mk_win_dist(self, build_path, dist_path):
        if JAVA_ENABLED:
            mk_dir(os.path.join(dist_path, INSTALL_BIN_DIR))
            shutil.copy('%s.jar' % os.path.join(build_path, self.package_name),
                        '%s.jar' % os.path.join(dist_path, INSTALL_BIN_DIR, self.package_name))
            shutil.copy(os.path.join(build_path, 'libz3java.dll'),
                        os.path.join(dist_path, INSTALL_BIN_DIR, 'libz3java.dll'))
            shutil.copy(os.path.join(build_path, 'libz3java.lib'),
                        os.path.join(dist_path, INSTALL_BIN_DIR, 'libz3java.lib'))

    def mk_unix_dist(self, build_path, dist_path):
        if JAVA_ENABLED:
            mk_dir(os.path.join(dist_path, INSTALL_BIN_DIR))
            shutil.copy('%s.jar' % os.path.join(build_path, self.package_name),
                        '%s.jar' % os.path.join(dist_path, INSTALL_BIN_DIR, self.package_name))
            so = get_so_ext()
            shutil.copy(os.path.join(build_path, 'libz3java.%s' % so),
                        os.path.join(dist_path, INSTALL_BIN_DIR, 'libz3java.%s' % so))

    def mk_install(self, out):
        if is_java_enabled() and self.install:
            dllfile = '%s$(SO_EXT)' % self.dll_name
            MakeRuleCmd.install_files(out, dllfile, os.path.join(INSTALL_LIB_DIR, dllfile))
            jarfile = '{}.jar'.format(self.package_name)
            MakeRuleCmd.install_files(out, jarfile, os.path.join(INSTALL_LIB_DIR, jarfile))

    def mk_uninstall(self, out):
        if is_java_enabled() and self.install:
            dllfile = '%s$(SO_EXT)' % self.dll_name
            MakeRuleCmd.remove_installed_files(out, os.path.join(INSTALL_LIB_DIR, dllfile))
            jarfile = '{}.jar'.format(self.package_name)
            MakeRuleCmd.remove_installed_files(out, os.path.join(INSTALL_LIB_DIR, jarfile))

class MLComponent(Component):

    def __init__(self, name, lib_name, path, deps):
        Component.__init__(self, name, path, deps)
        if lib_name is None:
            lib_name = name
        self.lib_name = lib_name
        self.modules = ["z3enums", "z3native", "z3"]  # dependencies in this order!
        self.stubs = "z3native_stubs"
        self.sub_dir = os.path.join('api', 'ml')

        self.destdir = ""
        self.ldconf = ""
        # Calling _init_ocamlfind_paths() is postponed to later because
        # OCAMLFIND hasn't been checked yet.

    def _install_bindings(self):
        # FIXME: Depending on global state is gross.  We can't pre-compute this
        # in the constructor because we haven't tested for ocamlfind yet
        return OCAMLFIND != ''

    def _init_ocamlfind_paths(self):
        """
            Initialises self.destdir and self.ldconf
            Do not call this from the MLComponent constructor because OCAMLFIND
            has not been checked at that point
        """
        if self.destdir != "" and self.ldconf != "":
            # Initialisation already done
            return
        # Use Ocamlfind to get the default destdir and ldconf path
        self.destdir = check_output([OCAMLFIND, 'printconf', 'destdir'])
        if self.destdir == "":
            raise MKException('Failed to get OCaml destdir')

        if not os.path.isdir(self.destdir):
            raise MKException('The destdir reported by {ocamlfind} ({destdir}) does not exist'.format(ocamlfind=OCAMLFIND, destdir=self.destdir))

        self.ldconf = check_output([OCAMLFIND, 'printconf', 'ldconf'])
        if self.ldconf == "":
            raise MKException('Failed to get OCaml ldconf path')

    def final_info(self):
        if not self._install_bindings():
            print("WARNING: Could not find ocamlfind utility. OCaml bindings will not be installed")

    def mk_makefile(self, out):
        if is_ml_enabled():
            CP_CMD = 'cp'
            if IS_WINDOWS:
                CP_CMD='copy'

            OCAML_FLAGS = ''
            if DEBUG_MODE:
                OCAML_FLAGS += '-g'

            if OCAMLFIND:
                OCAMLCF = OCAMLFIND + ' ' + 'ocamlc -package zarith' + ' ' + OCAML_FLAGS
                OCAMLOPTF = OCAMLFIND + ' ' + 'ocamlopt -package zarith' + ' ' + OCAML_FLAGS
            else:
                OCAMLCF = OCAMLC + ' ' + OCAML_FLAGS
                OCAMLOPTF = OCAMLOPT + ' ' + OCAML_FLAGS

            src_dir = self.to_src_dir
            mk_dir(os.path.join(BUILD_DIR, self.sub_dir))
            api_src = get_component(API_COMPONENT).to_src_dir
            # remove /GL and -std=c++17; the ocaml tools don't like them.
            if IS_WINDOWS:
                out.write('CXXFLAGS_OCAML=$(CXXFLAGS:/GL=)\n')
            else:
                out.write('CXXFLAGS_OCAML=$(subst -std=c++17,,$(CXXFLAGS))\n')

            substitutions = { 'VERSION': "{}.{}.{}.{}".format(VER_MAJOR, VER_MINOR, VER_BUILD, VER_TWEAK) }

            configure_file(os.path.join(self.src_dir, 'META.in'),
                           os.path.join(BUILD_DIR, self.sub_dir, 'META'),
                           substitutions)

            stubsc = os.path.join(src_dir, self.stubs + '.c')
            stubso = os.path.join(self.sub_dir, self.stubs) + '$(OBJ_EXT)'
            base_dll_name = get_component(Z3_DLL_COMPONENT).dll_name
            if STATIC_LIB:
                z3link = 'z3-static'
                z3linkdep = base_dll_name + '-static$(LIB_EXT)'
                out.write('%s: %s\n' % (z3linkdep, base_dll_name + '$(LIB_EXT)'))
                out.write('\tcp $< $@\n')
            else:
                z3link = 'z3'
                z3linkdep = base_dll_name + '$(SO_EXT)'
            out.write('%s: %s %s\n' % (stubso, stubsc, z3linkdep))
            out.write('\t%s -ccopt "$(CXXFLAGS_OCAML) -I %s -I %s -I %s $(CXX_OUT_FLAG)%s" -c %s\n' %
                      (OCAMLCF, OCAML_LIB, api_src, src_dir, stubso, stubsc))

            cmos = ''
            for m in self.modules:
                ml = os.path.join(src_dir, m + '.ml')
                cmo = os.path.join(self.sub_dir, m + '.cmo')
                existing_mli = os.path.join(src_dir, m + '.mli')
                mli = os.path.join(self.sub_dir, m + '.mli')
                cmi = os.path.join(self.sub_dir, m + '.cmi')
                out.write('%s: %s %s\n' % (cmo, ml, cmos))
                if (os.path.exists(existing_mli[3:])):
                    out.write('\t%s %s %s\n' % (CP_CMD, existing_mli, mli))
                else:
                    out.write('\t%s -i -I %s -c %s > %s\n' % (OCAMLCF, self.sub_dir, ml, mli))
                out.write('\t%s -I %s -o %s -c %s\n' % (OCAMLCF, self.sub_dir, cmi, mli))
                out.write('\t%s -I %s -o %s -c %s\n' % (OCAMLCF, self.sub_dir, cmo, ml))
                cmos = cmos + cmo + ' '

            cmxs = ''
            for m in self.modules:
                ff = os.path.join(src_dir, m + '.ml')
                ft = os.path.join(self.sub_dir, m + '.cmx')
                out.write('%s: %s %s %s\n' % (ft, ff, cmos, cmxs))
                out.write('\t%s -I %s -o %s -c %s\n' % (OCAMLOPTF, self.sub_dir, ft, ff))
                cmxs = cmxs + ' ' + ft


            OCAMLMKLIB = 'ocamlmklib'

            LIBZ3 = '-l' + z3link + ' -lstdc++'
            if is_cygwin() and not(is_cygwin_mingw()):
                LIBZ3 = z3linkdep

            LIBZ3 = LIBZ3 + ' ' + ' '.join(map(lambda x: '-cclib ' + x, LDFLAGS.split()))

            if DEBUG_MODE and not(is_cygwin()):
                # Some ocamlmklib's don't like -g; observed on cygwin, but may be others as well.
                OCAMLMKLIB += ' -g'

            z3mls = os.path.join(self.sub_dir, 'z3ml')

            out.write('%s.cma: %s %s %s\n' % (z3mls, cmos, stubso, z3linkdep))
            out.write('\t%s -o %s -I %s -L. %s %s %s\n' % (OCAMLMKLIB, z3mls, self.sub_dir, stubso, cmos, LIBZ3))
            out.write('%s.cmxa: %s %s %s %s.cma\n' % (z3mls, cmxs, stubso, z3linkdep, z3mls))
            out.write('\t%s -o %s -I %s -L. %s %s %s\n' % (OCAMLMKLIB, z3mls, self.sub_dir, stubso, cmxs, LIBZ3))
            out.write('%s.cmxs: %s.cmxa\n' % (z3mls, z3mls))
            out.write('\t%s -linkall -shared -o %s.cmxs -I . -I %s %s.cmxa\n' % (OCAMLOPTF, z3mls, self.sub_dir, z3mls))

            out.write('\n')
            out.write('ml: %s.cma %s.cmxa %s.cmxs\n' % (z3mls, z3mls, z3mls))
            out.write('\n')

            if IS_WINDOWS:
                out.write('ocamlfind_install: ')
                self.mk_install_deps(out)
                out.write('\n')
                self.mk_install(out)
                out.write('\n')
                out.write('ocamlfind_uninstall:\n')
                self.mk_uninstall(out)
                out.write('\n')

    def mk_install_deps(self, out):
        if is_ml_enabled() and self._install_bindings():
            out.write(get_component(Z3_DLL_COMPONENT).dll_name + '$(SO_EXT) ')
            out.write(os.path.join(self.sub_dir, 'META '))
            out.write(os.path.join(self.sub_dir, 'z3ml.cma '))
            out.write(os.path.join(self.sub_dir, 'z3ml.cmxa '))
            out.write(os.path.join(self.sub_dir, 'z3ml.cmxs '))

    def mk_install(self, out):
        if is_ml_enabled() and self._install_bindings():
            self._init_ocamlfind_paths()
            in_prefix = self.destdir.startswith(PREFIX)
            maybe_stripped_destdir = strip_path_prefix(self.destdir, PREFIX)
            # Note that when doing a staged install with DESTDIR that modifying
            # OCaml's ``ld.conf`` may fail. Therefore packagers will need to
            # make their packages modify it manually at package install time
            # as opposed to ``make install`` time.
            MakeRuleCmd.make_install_directory(out,
                                               maybe_stripped_destdir,
                                               in_prefix=in_prefix)
            out.write('\t@{ocamlfind} install -ldconf $(DESTDIR){ldconf} -destdir $(DESTDIR){ocaml_destdir} Z3 {metafile}'.format(
                ldconf=self.ldconf,
                ocamlfind=OCAMLFIND,
                ocaml_destdir=self.destdir,
                metafile=os.path.join(self.sub_dir, 'META')))

            for m in self.modules:
                mli = os.path.join(self.src_dir, m) + '.mli'
                if os.path.exists(mli):
                    out.write(' ' + os.path.join(self.to_src_dir, m) + '.mli')
                else:
                    out.write(' ' + os.path.join(self.sub_dir, m) + '.mli')
                out.write(' ' + os.path.join(self.sub_dir, m) + '.cmi')
                out.write(' ' + os.path.join(self.sub_dir, m) + '.cmx')
            out.write(' %s' % ((os.path.join(self.sub_dir, 'libz3ml$(LIB_EXT)'))))
            out.write(' %s' % ((os.path.join(self.sub_dir, 'z3ml$(LIB_EXT)'))))
            out.write(' %s' % ((os.path.join(self.sub_dir, 'z3ml.cma'))))
            out.write(' %s' % ((os.path.join(self.sub_dir, 'z3ml.cmxa'))))
            out.write(' %s' % ((os.path.join(self.sub_dir, 'z3ml.cmxs'))))
            out.write(' %s' % ((os.path.join(self.sub_dir, 'dllz3ml'))))
            if is_windows() or is_cygwin_mingw():
                out.write('.dll')
            else:
                out.write('.so') # .so also on OSX!
            out.write('\n')

    def mk_uninstall(self, out):
        if is_ml_enabled() and self._install_bindings():
            self._init_ocamlfind_paths()
            out.write('\t@{ocamlfind} remove -ldconf $(DESTDIR){ldconf} -destdir $(DESTDIR){ocaml_destdir} Z3\n'.format(
                ldconf=self.ldconf,
                ocamlfind=OCAMLFIND,
                ocaml_destdir=self.destdir))

    def main_component(self):
        return is_ml_enabled()

class ExampleComponent(Component):
    def __init__(self, name, path):
        Component.__init__(self, name, path, [])
        self.ex_dir   = os.path.join(EXAMPLE_DIR, self.path)
        self.to_ex_dir = os.path.join(REV_BUILD_DIR, self.ex_dir)

    def is_example(self):
        return True

class CppExampleComponent(ExampleComponent):
    def __init__(self, name, path):
        ExampleComponent.__init__(self, name, path)

    def compiler(self):
        return "$(CXX)"

    def src_files(self):
        return get_cpp_files(self.ex_dir)

    def mk_makefile(self, out):
        dll_name = get_component(Z3_DLL_COMPONENT).dll_name
        dll = '%s$(SO_EXT)' % dll_name

        objfiles = ''
        for cppfile in self.src_files():
            objfile = '%s$(OBJ_EXT)' % (cppfile[:cppfile.rfind('.')])
            objfiles = objfiles + ('%s ' % objfile)
            out.write('%s: %s\n' % (objfile, os.path.join(self.to_ex_dir, cppfile)));
            out.write('\t%s $(CXXFLAGS) $(OS_DEFINES) $(EXAMP_DEBUG_FLAG) $(CXX_OUT_FLAG)%s $(LINK_FLAGS)' % (self.compiler(), objfile))
            # Add include dir components
            out.write(' -I%s' % get_component(API_COMPONENT).to_src_dir)
            out.write(' -I%s' % get_component(CPP_COMPONENT).to_src_dir)
            out.write(' %s' % os.path.join(self.to_ex_dir, cppfile))
            out.write('\n')

        exefile = '%s$(EXE_EXT)' % self.name
        out.write('%s: %s %s\n' % (exefile, dll, objfiles))
        out.write('\t$(LINK) $(LINK_OUT_FLAG)%s $(LINK_FLAGS) %s ' % (exefile, objfiles))
        if IS_WINDOWS:
            out.write('%s.lib' % dll_name)
        else:
            out.write(dll)
        out.write(' $(LINK_EXTRA_FLAGS)\n')
        out.write('_ex_%s: %s\n\n' % (self.name, exefile))

class CExampleComponent(CppExampleComponent):
    def __init__(self, name, path):
        CppExampleComponent.__init__(self, name, path)

    def compiler(self):
        return "$(CC)"

    def src_files(self):
        return get_c_files(self.ex_dir)

    def mk_makefile(self, out):
        dll_name = get_component(Z3_DLL_COMPONENT).dll_name
        dll = '%s$(SO_EXT)' % dll_name

        objfiles = ''
        for cfile in self.src_files():
            objfile = '%s$(OBJ_EXT)' % (cfile[:cfile.rfind('.')])
            objfiles = objfiles + ('%s ' % objfile)
            out.write('%s: %s\n' % (objfile, os.path.join(self.to_ex_dir, cfile)));
            out.write('\t%s $(CFLAGS) $(OS_DEFINES) $(EXAMP_DEBUG_FLAG) $(C_OUT_FLAG)%s $(LINK_FLAGS)' % (self.compiler(), objfile))
            out.write(' -I%s' % get_component(API_COMPONENT).to_src_dir)
            out.write(' %s' % os.path.join(self.to_ex_dir, cfile))
            out.write('\n')

        exefile = '%s$(EXE_EXT)' % self.name
        out.write('%s: %s %s\n' % (exefile, dll, objfiles))
        out.write('\t$(LINK) $(LINK_OUT_FLAG)%s $(LINK_FLAGS) %s ' % (exefile, objfiles))
        if IS_WINDOWS:
            out.write('%s.lib' % dll_name)
        else:
            out.write(dll)
        out.write(' $(LINK_EXTRA_FLAGS)\n')
        out.write('_ex_%s: %s\n\n' % (self.name, exefile))

class DotNetExampleComponent(ExampleComponent):
    def __init__(self, name, path):
        ExampleComponent.__init__(self, name, path)

    def is_example(self):
        return is_dotnet_core_enabled()

    def mk_makefile(self, out):
        if is_dotnet_core_enabled():
            proj_name = 'dotnet_example.csproj'
            out.write('_ex_%s:' % self.name)
            for csfile in get_cs_files(self.ex_dir):
                out.write(' ')
                out.write(os.path.join(self.to_ex_dir, csfile))

            mk_dir(os.path.join(BUILD_DIR, 'dotnet_example'))
            csproj = os.path.join('dotnet_example', proj_name)
            if VS_X64:
                platform = 'x64'
            elif VS_ARM:
                platform = 'ARM'
            else:
                platform = 'x86'

            dotnet_proj_str = """<Project Sdk="Microsoft.NET.Sdk">
  <PropertyGroup>
    <OutputType>Exe</OutputType>
    <TargetFramework>netcoreapp2.0</TargetFramework>
    <PlatformTarget>%s</PlatformTarget>
  </PropertyGroup>
  <ItemGroup>
    <Compile Include="..\%s/*.cs" />
    <Reference Include="Microsoft.Z3">
      <HintPath>..\Microsoft.Z3.dll</HintPath>
    </Reference>
  </ItemGroup>
</Project>""" % (platform, self.to_ex_dir)

            with open(os.path.join(BUILD_DIR, csproj), 'w') as ous:
                ous.write(dotnet_proj_str)

            out.write('\n')
            dotnetCmdLine = [DOTNET, "build", csproj]
            dotnetCmdLine.extend(['-c'])
            if DEBUG_MODE:
                dotnetCmdLine.extend(['Debug'])
            else:
                dotnetCmdLine.extend(['Release'])
            MakeRuleCmd.write_cmd(out, ' '.join(dotnetCmdLine))
            out.write('\n')

class JavaExampleComponent(ExampleComponent):
    def __init__(self, name, path):
        ExampleComponent.__init__(self, name, path)

    def is_example(self):
        return JAVA_ENABLED

    def mk_makefile(self, out):
        if JAVA_ENABLED:
            pkg = get_component(JAVA_COMPONENT).package_name + '.jar'
            out.write('JavaExample.class: %s' % (pkg))
            deps = ''
            for jfile in get_java_files(self.ex_dir):
                out.write(' %s' % os.path.join(self.to_ex_dir, jfile))
            if IS_WINDOWS:
                deps = deps.replace('/', '\\')
            out.write('%s\n' % deps)
            out.write('\t%s -cp %s ' % (JAVAC, pkg))
            win_ex_dir = self.to_ex_dir
            for javafile in get_java_files(self.ex_dir):
                out.write(' ')
                out.write(os.path.join(win_ex_dir, javafile))
            out.write(' -d .\n')
            out.write('_ex_%s: JavaExample.class\n\n' % (self.name))

class MLExampleComponent(ExampleComponent):
    def __init__(self, name, path):
        ExampleComponent.__init__(self, name, path)

    def is_example(self):
        return ML_ENABLED

    def mk_makefile(self, out):
        if ML_ENABLED:
            out.write('ml_example.byte: api/ml/z3ml.cma')
            for mlfile in get_ml_files(self.ex_dir):
                out.write(' %s' % os.path.join(self.to_ex_dir, mlfile))
            out.write('\n')
            out.write('\tocamlfind %s ' % OCAMLC)
            if DEBUG_MODE:
                out.write('-g ')
            out.write('-custom -o ml_example.byte -package zarith -I api/ml -cclib "-L. -lpthread -lstdc++ -lz3" -linkpkg z3ml.cma')
            for mlfile in get_ml_files(self.ex_dir):
                out.write(' %s/%s' % (self.to_ex_dir, mlfile))
            out.write('\n')
            out.write('ml_example$(EXE_EXT): api/ml/z3ml.cmxa')
            for mlfile in get_ml_files(self.ex_dir):
                out.write(' %s' % os.path.join(self.to_ex_dir, mlfile))
            out.write('\n')
            out.write('\tocamlfind %s ' % OCAMLOPT)
            if DEBUG_MODE:
                out.write('-g ')
            out.write('-o ml_example$(EXE_EXT) -package zarith -I api/ml -cclib "-L. -lpthread -lstdc++ -lz3" -linkpkg z3ml.cmxa')
            for mlfile in get_ml_files(self.ex_dir):
                out.write(' %s/%s' % (self.to_ex_dir, mlfile))
            out.write('\n')
            out.write('_ex_%s: ml_example.byte ml_example$(EXE_EXT)\n\n' % self.name)

class PythonExampleComponent(ExampleComponent):
    def __init__(self, name, path):
        ExampleComponent.__init__(self, name, path)

    # Python examples are just placeholders, we just copy the *.py files when mk_makefile is invoked.
    # We don't need to include them in the :examples rule
    def mk_makefile(self, out):
        full = os.path.join(EXAMPLE_DIR, self.path)
        for py in filter(lambda f: f.endswith('.py'), os.listdir(full)):
            shutil.copyfile(os.path.join(full, py), os.path.join(BUILD_DIR, 'python', py))
            if is_verbose():
                print("Copied Z3Py example '%s' to '%s'" % (py, os.path.join(BUILD_DIR, 'python')))
        out.write('_ex_%s: \n\n' % self.name)

    def mk_win_dist(self, build_path, dist_path):
        full = os.path.join(EXAMPLE_DIR, self.path)
        py = 'example.py'
        shutil.copyfile(os.path.join(full, py),
                        os.path.join(dist_path, INSTALL_BIN_DIR, 'python', py))

    def mk_unix_dist(self, build_path, dist_path):
        self.mk_win_dist(build_path, dist_path)


def reg_component(name, c):
    global _Id, _Components, _ComponentNames, _Name2Component
    c.id = _Id
    _Id = _Id + 1
    _Components.append(c)
    _ComponentNames.add(name)
    _Name2Component[name] = c
    if VERBOSE:
        print("New component: '%s'" % name)

def add_lib(name, deps=[], path=None, includes2install=[]):
    c = LibComponent(name, path, deps, includes2install)
    reg_component(name, c)

def add_clib(name, deps=[], path=None, includes2install=[]):
    c = CLibComponent(name, path, deps, includes2install)
    reg_component(name, c)

def add_hlib(name, path=None, includes2install=[]):
    c = HLibComponent(name, path, includes2install)
    reg_component(name, c)

def add_exe(name, deps=[], path=None, exe_name=None, install=True):
    c = ExeComponent(name, exe_name, path, deps, install)
    reg_component(name, c)

def add_extra_exe(name, deps=[], path=None, exe_name=None, install=True):
    c = ExtraExeComponent(name, exe_name, path, deps, install)
    reg_component(name, c)

def add_dll(name, deps=[], path=None, dll_name=None, export_files=[], reexports=[], install=True, static=False, staging_link=None):
    c = DLLComponent(name, dll_name, path, deps, export_files, reexports, install, static, staging_link)
    reg_component(name, c)
    return c

def add_dot_net_core_dll(name, deps=[], path=None, dll_name=None, assembly_info_dir=None, default_key_file=None):
    c = DotNetDLLComponent(name, dll_name, path, deps, assembly_info_dir, default_key_file)
    reg_component(name, c)

def add_java_dll(name, deps=[], path=None, dll_name=None, package_name=None, manifest_file=None):
    c = JavaDLLComponent(name, dll_name, package_name, manifest_file, path, deps)
    reg_component(name, c)

def add_python(libz3Component):
    name = 'python'
    reg_component(name, PythonComponent(name, libz3Component))

def add_js():
    reg_component('js', JsComponent())

def add_python_install(libz3Component):
    name = 'python_install'
    reg_component(name, PythonInstallComponent(name, libz3Component))

def add_ml_lib(name, deps=[], path=None, lib_name=None):
    c = MLComponent(name, lib_name, path, deps)
    reg_component(name, c)

def add_cpp_example(name, path=None):
    c = CppExampleComponent(name, path)
    reg_component(name, c)

def add_c_example(name, path=None):
    c = CExampleComponent(name, path)
    reg_component(name, c)

def add_dotnet_example(name, path=None):
    c = DotNetExampleComponent(name, path)
    reg_component(name, c)

def add_java_example(name, path=None):
    c = JavaExampleComponent(name, path)
    reg_component(name, c)

def add_ml_example(name, path=None):
    c = MLExampleComponent(name, path)
    reg_component(name, c)

def add_z3py_example(name, path=None):
    c = PythonExampleComponent(name, path)
    reg_component(name, c)

def mk_config():
    if ONLY_MAKEFILES:
        return
    config = open(os.path.join(BUILD_DIR, 'config.mk'), 'w')
    global CXX, CC, GMP, GUARD_CF, STATIC_BIN, GIT_HASH, CPPFLAGS, CXXFLAGS, LDFLAGS, EXAMP_DEBUG_FLAG, FPMATH_FLAGS, LOG_SYNC, SINGLE_THREADED
    if IS_WINDOWS:
        CXXFLAGS = '/nologo /Zi /D WIN32 /D _WINDOWS /EHsc /GS /Gd /std:c++17'
        config.write(
            'CC=cl\n'
            'CXX=cl\n'
            'CXX_OUT_FLAG=/Fo\n'
            'C_OUT_FLAG=/Fo\n'
            'OBJ_EXT=.obj\n'
            'LIB_EXT=.lib\n'
            'AR=lib\n'
            'AR_OUTFLAG=/OUT:\n'
            'EXE_EXT=.exe\n'
            'LINK=cl\n'
            'LINK_OUT_FLAG=/Fe\n'
            'SO_EXT=.dll\n'
            'SLINK=cl\n'
            'SLINK_OUT_FLAG=/Fe\n'
            'OS_DEFINES=/D _WINDOWS\n')
        extra_opt = ''
        link_extra_opt = ''
        if LOG_SYNC:
            extra_opt = '%s /DZ3_LOG_SYNC' % extra_opt
        if SINGLE_THREADED:
            extra_opt = '%s /DSINGLE_THREAD' % extra_opt
        if GIT_HASH:
            extra_opt = ' %s /D Z3GITHASH=%s' % (extra_opt, GIT_HASH)
        if GUARD_CF:
            extra_opt = ' %s /guard:cf' % extra_opt
            link_extra_opt = ' %s /GUARD:CF' % link_extra_opt
        if STATIC_BIN:
            static_opt = '/MT'
        else:
            static_opt = '/MD'
        maybe_disable_dynamic_base = '/DYNAMICBASE' if ALWAYS_DYNAMIC_BASE else '/DYNAMICBASE:NO'
        if DEBUG_MODE:
            static_opt = static_opt + 'd'
            config.write(
                'AR_FLAGS=/nologo\n'
                'LINK_FLAGS=/nologo %s\n'
                'SLINK_FLAGS=/nologo /LDd\n' % static_opt)
            if VS_X64:
                config.write(
                    'CXXFLAGS=/c %s /W3 /WX- /Od /Oy- /D _DEBUG /D Z3DEBUG /D _CONSOLE /D _TRACE /Gm- /RTC1 %s %s\n' % (CXXFLAGS, extra_opt, static_opt))
                config.write(
                    'LINK_EXTRA_FLAGS=/link /DEBUG /MACHINE:X64 /SUBSYSTEM:CONSOLE /INCREMENTAL:NO /STACK:8388608 /OPT:REF /OPT:ICF /TLBID:1 /DYNAMICBASE /NXCOMPAT %s\n'
                    'SLINK_EXTRA_FLAGS=/link /DEBUG /MACHINE:X64 /SUBSYSTEM:WINDOWS /INCREMENTAL:NO /STACK:8388608 /OPT:REF /OPT:ICF /TLBID:1 %s %s\n' % (link_extra_opt, maybe_disable_dynamic_base, link_extra_opt))
            elif VS_ARM:
                print("ARM on VS is unsupported")
                exit(1)
            else:
                config.write(
                    'CXXFLAGS=/c %s /W3 /WX- /Od /Oy- /D _DEBUG /D Z3DEBUG /D _CONSOLE /D _TRACE /Gm- /RTC1 /arch:SSE2 %s %s\n' % (CXXFLAGS, extra_opt, static_opt))
                config.write(
                    'LINK_EXTRA_FLAGS=/link /DEBUG /MACHINE:X86 /SUBSYSTEM:CONSOLE /INCREMENTAL:NO /STACK:8388608 /OPT:REF /OPT:ICF /TLBID:1 /DYNAMICBASE /NXCOMPAT %s\n'
                    'SLINK_EXTRA_FLAGS=/link /DEBUG /MACHINE:X86 /SUBSYSTEM:WINDOWS /INCREMENTAL:NO /STACK:8388608 /OPT:REF /OPT:ICF /TLBID:1 %s %s\n' % (link_extra_opt, maybe_disable_dynamic_base, link_extra_opt))
        else:
            # Windows Release mode
            LTCG=' /LTCG' if SLOW_OPTIMIZE else ''
            GL = ' /GL' if SLOW_OPTIMIZE else ''
            config.write(
                'AR_FLAGS=/nologo %s\n'
                'LINK_FLAGS=/nologo %s\n'
                'SLINK_FLAGS=/nologo /LD\n' % (LTCG, static_opt))
            if TRACE:
                extra_opt = '%s /D _TRACE ' % extra_opt
            if VS_X64:
                config.write(
                    'CXXFLAGS=/c%s %s /W3 /WX- /O2 /D _EXTERNAL_RELEASE /D NDEBUG /D _LIB /D UNICODE /Gm- /GF /Gy /TP %s %s\n' % (GL, CXXFLAGS, extra_opt, static_opt))
                config.write(
                    'LINK_EXTRA_FLAGS=/link%s /profile /MACHINE:X64 /SUBSYSTEM:CONSOLE /STACK:8388608 %s\n'
                    'SLINK_EXTRA_FLAGS=/link%s /profile /MACHINE:X64 /SUBSYSTEM:WINDOWS /STACK:8388608 %s\n' % (LTCG, link_extra_opt, LTCG, link_extra_opt))
            elif VS_ARM:
                print("ARM on VS is unsupported")
                exit(1)
            else:
                config.write(
                    'CXXFLAGS=/c%s %s /WX- /O2 /Oy- /D _EXTERNAL_RELEASE /D NDEBUG /D _CONSOLE /D ASYNC_COMMANDS /Gm- /arch:SSE2 %s %s\n' % (GL, CXXFLAGS, extra_opt, static_opt))
                config.write(
                    'LINK_EXTRA_FLAGS=/link%s /DEBUG /MACHINE:X86 /SUBSYSTEM:CONSOLE /INCREMENTAL:NO /STACK:8388608 /OPT:REF /OPT:ICF /TLBID:1 /DYNAMICBASE /NXCOMPAT %s\n'
                    'SLINK_EXTRA_FLAGS=/link%s /DEBUG /MACHINE:X86 /SUBSYSTEM:WINDOWS /INCREMENTAL:NO /STACK:8388608 /OPT:REF /OPT:ICF /TLBID:1 %s %s\n' % (LTCG, link_extra_opt, LTCG, maybe_disable_dynamic_base, link_extra_opt))

        config.write('CFLAGS=$(CXXFLAGS)\n')

        # End of Windows VS config.mk
        if is_verbose():
            print('64-bit:         %s' % is64())
            if is_java_enabled():
                print('JNI Bindings:   %s' % JNI_HOME)
                print('Java Compiler:  %s' % JAVAC)
            if is_ml_enabled():
                print('OCaml Compiler: %s' % OCAMLC)
                print('OCaml Find tool: %s' % OCAMLFIND)
                print('OCaml Native:   %s' % OCAMLOPT)
                print('OCaml Library:  %s' % OCAML_LIB)
    else:
        OS_DEFINES = ""
        ARITH = "internal"
        check_ar()
        CXX = find_cxx_compiler()
        CC  = find_c_compiler()
        SLIBEXTRAFLAGS = ''
#       SLIBEXTRAFLAGS = '%s -Wl,-soname,libz3.so.0' % LDFLAGS
        EXE_EXT = ''
        LIB_EXT = '.a'
        if GPROF:
            CXXFLAGS = '%s -pg' % CXXFLAGS
            LDFLAGS  = '%s -pg' % LDFLAGS
        if GMP:
            test_gmp(CXX)
            ARITH = "gmp"
            CPPFLAGS = '%s -D_MP_GMP' % CPPFLAGS
            LDFLAGS  = '%s -lgmp' % LDFLAGS
            SLIBEXTRAFLAGS = '%s -lgmp' % SLIBEXTRAFLAGS
        else:
            CPPFLAGS = '%s -D_MP_INTERNAL' % CPPFLAGS
        if GIT_HASH:
            CPPFLAGS = '%s -DZ3GITHASH=%s' % (CPPFLAGS, GIT_HASH)
        CXXFLAGS = '%s -std=c++17' % CXXFLAGS
        CXXFLAGS = '%s -fvisibility=hidden -fvisibility-inlines-hidden -c' % CXXFLAGS
        FPMATH = test_fpmath(CXX)
        CXXFLAGS = '%s %s' % (CXXFLAGS, FPMATH_FLAGS)
        if LOG_SYNC:
            CXXFLAGS = '%s -DZ3_LOG_SYNC' % CXXFLAGS
        if SINGLE_THREADED:
            CXXFLAGS = '%s -DSINGLE_THREAD' % CXXFLAGS
        if DEBUG_MODE:
            CXXFLAGS     = '%s -g -Wall' % CXXFLAGS
            EXAMP_DEBUG_FLAG = '-g'
            CPPFLAGS     = '%s -DZ3DEBUG -D_DEBUG' % CPPFLAGS
        else:
            CXXFLAGS     = '%s -O3' % CXXFLAGS
            if GPROF:
                CXXFLAGS     += '-fomit-frame-pointer'
            CPPFLAGS     = '%s -DNDEBUG -D_EXTERNAL_RELEASE' % CPPFLAGS
        if is_CXX_clangpp():
            CXXFLAGS   = '%s -Wno-unknown-pragmas -Wno-overloaded-virtual -Wno-unused-value' % CXXFLAGS
        sysname, _, _, _, machine = os.uname()
        if sysname == 'Darwin':
            SO_EXT         = '.dylib'
            SLIBFLAGS      = '-dynamiclib'
        elif sysname == 'Linux':
            CXXFLAGS       = '%s -D_LINUX_' % CXXFLAGS
            OS_DEFINES     = '-D_LINUX_'
            SO_EXT         = '.so'
            SLIBFLAGS      = '-shared'
            SLIBEXTRAFLAGS = '%s -Wl,-soname,libz3.so' % SLIBEXTRAFLAGS
        elif sysname == 'GNU':
            CXXFLAGS       = '%s -D_HURD_' % CXXFLAGS
            OS_DEFINES     = '-D_HURD_'
            SO_EXT         = '.so'
            SLIBFLAGS      = '-shared'
        elif sysname == 'FreeBSD':
            CXXFLAGS       = '%s -D_FREEBSD_' % CXXFLAGS
            OS_DEFINES     = '-D_FREEBSD_'
            SO_EXT         = '.so'
            SLIBFLAGS      = '-shared'
        elif sysname == 'NetBSD':
            CXXFLAGS       = '%s -D_NETBSD_' % CXXFLAGS
            OS_DEFINES     = '-D_NETBSD_'
            SO_EXT         = '.so'
            SLIBFLAGS      = '-shared'
        elif sysname == 'OpenBSD':
            CXXFLAGS       = '%s -D_OPENBSD_' % CXXFLAGS
            OS_DEFINES     = '-D_OPENBSD_'
            SO_EXT         = '.so'
            SLIBFLAGS      = '-shared'
        elif sysname  == 'SunOS':
            CXXFLAGS       = '%s -D_SUNOS_' % CXXFLAGS
            OS_DEFINES     = '-D_SUNOS_'
            SO_EXT         = '.so'
            SLIBFLAGS      = '-shared'
            SLIBEXTRAFLAGS = '%s -mimpure-text' % SLIBEXTRAFLAGS
        elif sysname.startswith('CYGWIN'):
            CXXFLAGS       = '%s -D_CYGWIN' % CXXFLAGS
            OS_DEFINES     = '-D_CYGWIN'
            SO_EXT         = '.dll'
            SLIBFLAGS      = '-shared'
        elif sysname.startswith('MSYS_NT') or sysname.startswith('MINGW'):
            CXXFLAGS       = '%s -D_MINGW' % CXXFLAGS
            OS_DEFINES     = '-D_MINGW'
            SO_EXT         = '.dll'
            SLIBFLAGS      = '-shared'
            EXE_EXT        = '.exe'
            LIB_EXT        = '.lib'
        else:
            raise MKException('Unsupported platform: %s' % sysname)
        if is64():
            if not sysname.startswith('CYGWIN') and not sysname.startswith('MSYS') and not sysname.startswith('MINGW'):
                CXXFLAGS     = '%s -fPIC' % CXXFLAGS
            if sysname == 'Linux':
                CPPFLAGS = '%s -D_USE_THREAD_LOCAL' % CPPFLAGS
        elif not LINUX_X64:
            CXXFLAGS     = '%s -m32' % CXXFLAGS
            LDFLAGS      = '%s -m32' % LDFLAGS
            SLIBFLAGS    = '%s -m32' % SLIBFLAGS
        if TRACE or DEBUG_MODE:
            CPPFLAGS     = '%s -D_TRACE' % CPPFLAGS
        if is_cygwin_mingw():
            # when cross-compiling with MinGW, we need to statically link its standard libraries
            # and to make it create an import library.
            SLIBEXTRAFLAGS = '%s -static-libgcc -static-libstdc++ -Wl,--out-implib,libz3.dll.a' % SLIBEXTRAFLAGS
            LDFLAGS = '%s -static-libgcc -static-libstdc++' % LDFLAGS
        if sysname == 'Linux' and machine.startswith('armv7') or machine.startswith('armv8'):
            CXXFLAGS = '%s -fpic' % CXXFLAGS

        config.write('PREFIX=%s\n' % PREFIX)
        config.write('CC=%s\n' % CC)
        config.write('CXX=%s\n' % CXX)
        config.write('CXXFLAGS=%s %s\n' % (CPPFLAGS, CXXFLAGS))
        config.write('CFLAGS=%s %s\n' % (CPPFLAGS, CXXFLAGS.replace('-std=c++17', '')))
        config.write('EXAMP_DEBUG_FLAG=%s\n' % EXAMP_DEBUG_FLAG)
        config.write('CXX_OUT_FLAG=-o \n')
        config.write('C_OUT_FLAG=-o \n')
        config.write('OBJ_EXT=.o\n')
        config.write('LIB_EXT=%s\n' % LIB_EXT)
        config.write('AR=%s\n' % AR)
        config.write('AR_FLAGS=rcs\n')
        config.write('AR_OUTFLAG=\n')
        config.write('EXE_EXT=%s\n' % EXE_EXT)
        config.write('LINK=%s\n' % CXX)
        config.write('LINK_FLAGS=\n')
        config.write('LINK_OUT_FLAG=-o \n')
        if is_linux() and (build_static_lib() or build_static_bin()):
            config.write('LINK_EXTRA_FLAGS=-Wl,--whole-archive -lrt -lpthread -Wl,--no-whole-archive %s\n' % LDFLAGS)
        else:
            config.write('LINK_EXTRA_FLAGS=-lpthread %s\n' % LDFLAGS)
        config.write('SO_EXT=%s\n' % SO_EXT)
        config.write('SLINK=%s\n' % CXX)
        config.write('SLINK_FLAGS=%s\n' % SLIBFLAGS)
        config.write('SLINK_EXTRA_FLAGS=-lpthread %s\n' % SLIBEXTRAFLAGS)
        config.write('SLINK_OUT_FLAG=-o \n')
        config.write('OS_DEFINES=%s\n' % OS_DEFINES)
        if is_verbose():
            print('Host platform:  %s' % sysname)
            print('C++ Compiler:   %s' % CXX)
            print('C Compiler  :   %s' % CC)
            if is_cygwin_mingw():
                print('MinGW32 cross:  %s' % (is_cygwin_mingw()))
            print('Archive Tool:   %s' % AR)
            print('Arithmetic:     %s' % ARITH)
            print('Prefix:         %s' % PREFIX)
            print('64-bit:         %s' % is64())
            print('FP math:        %s' % FPMATH)
            print("Python pkg dir: %s" % PYTHON_PACKAGE_DIR)
            if GPROF:
                print('gprof:          enabled')
            print('Python version: %s' % distutils.sysconfig.get_python_version())
            if is_java_enabled():
                print('JNI Bindings:   %s' % JNI_HOME)
                print('Java Compiler:  %s' % JAVAC)
            if is_ml_enabled():
                print('OCaml Compiler: %s' % OCAMLC)
                print('OCaml Find tool: %s' % OCAMLFIND)
                print('OCaml Native:   %s' % OCAMLOPT)
                print('OCaml Library:  %s' % OCAML_LIB)
            if is_dotnet_core_enabled():
                print('C# Compiler:    %s' % DOTNET)

    config.close()

def mk_install(out):
    out.write('install: ')
    for c in get_components():
        c.mk_install_deps(out)
        out.write(' ')
    out.write('\n')
    MakeRuleCmd.make_install_directory(out, INSTALL_BIN_DIR)
    MakeRuleCmd.make_install_directory(out, INSTALL_INCLUDE_DIR)
    MakeRuleCmd.make_install_directory(out, INSTALL_LIB_DIR)
    for c in get_components():
        c.mk_install(out)
    out.write('\t@echo Z3 was successfully installed.\n')
    out.write('\n')

def mk_uninstall(out):
    out.write('uninstall:\n')
    for c in get_components():
        c.mk_uninstall(out)
    out.write('\t@echo Z3 was successfully uninstalled.\n')
    out.write('\n')

# Generate the Z3 makefile
def mk_makefile():
    mk_dir(BUILD_DIR)
    mk_config()
    if VERBOSE:
        print("Writing %s" % os.path.join(BUILD_DIR, 'Makefile'))
    out = open(os.path.join(BUILD_DIR, 'Makefile'), 'w')
    out.write('# Automatically generated file.\n')
    out.write('include config.mk\n')
    # Generate :all rule
    out.write('all:')
    for c in get_components():
        if c.main_component():
            out.write(' %s' % c.name)
    out.write('\n\t@echo Z3 was successfully built.\n')
    out.write("\t@echo \"Z3Py scripts can already be executed in the \'%s\' directory.\"\n" % os.path.join(BUILD_DIR, 'python'))
    pathvar = "DYLD_LIBRARY_PATH" if IS_OSX else "PATH" if IS_WINDOWS else "LD_LIBRARY_PATH"
    out.write("\t@echo \"Z3Py scripts stored in arbitrary directories can be executed if the \'%s\' directory is added to the PYTHONPATH environment variable and the \'%s\' directory is added to the %s environment variable.\"\n" % (os.path.join(BUILD_DIR, 'python'), BUILD_DIR, pathvar))
    if not IS_WINDOWS:
        out.write("\t@echo Use the following command to install Z3 at prefix $(PREFIX).\n")
        out.write('\t@echo "    sudo make install"\n\n')
        # out.write("\t@echo If you are doing a staged install you can use DESTDIR.\n")
        # out.write('\t@echo "    make DESTDIR=/some/temp/directory install"\n')
    # Generate :examples rule
    out.write('examples:')
    for c in get_components():
        if c.is_example():
            out.write(' _ex_%s' % c.name)
    out.write('\n\t@echo Z3 examples were successfully built.\n')
    # Generate components
    for c in get_components():
        c.mk_makefile(out)
    # Generate install/uninstall rules if not WINDOWS
    if not IS_WINDOWS:
        mk_install(out)
        mk_uninstall(out)
    for c in get_components():
        c.final_info()
    out.close()
    # Finalize
    if VERBOSE:
        print("Makefile was successfully generated.")
        if DEBUG_MODE:
            print("  compilation mode: Debug")
        else:
            print("  compilation mode: Release")
        if IS_WINDOWS:
            if VS_X64:
                print("  platform: x64\n")
                print("To build Z3, open a [Visual Studio x64 Command Prompt], then")
            elif VS_ARM:
                print("  platform: ARM\n")
                print("To build Z3, open a [Visual Studio ARM Command Prompt], then")
            else:
                print("  platform: x86")
                print("To build Z3, open a [Visual Studio Command Prompt], then")
            print("type 'cd %s && nmake'\n" % os.path.join(os.getcwd(), BUILD_DIR))
            print('Remark: to open a Visual Studio Command Prompt, go to: "Start > All Programs > Visual Studio > Visual Studio Tools"')
        else:
            print("Type 'cd %s; make' to build Z3" % BUILD_DIR)

# Generate automatically generated source code
def mk_auto_src():
    if not ONLY_MAKEFILES:
        exec_pyg_scripts()
        mk_pat_db()
        mk_all_install_tactic_cpps()
        mk_all_mem_initializer_cpps()
        mk_all_gparams_register_modules()


def _execfile(file, globals=globals(), locals=locals()):
    if sys.version < "2.7":
        execfile(file, globals, locals)
    else:
        with open(file, "r") as fh:
            exec(fh.read()+"\n", globals, locals)

# Execute python auxiliary scripts that generate extra code for Z3.
def exec_pyg_scripts():
    for root, dirs, files in os.walk('src'):
        for f in files:
            if f.endswith('.pyg'):
                script = os.path.join(root, f)
                generated_file = mk_genfile_common.mk_hpp_from_pyg(script, root)
                if is_verbose():
                    print("Generated '{}'".format(generated_file))

# TODO: delete after src/ast/pattern/expr_pattern_match
# database.smt ==> database.h
def mk_pat_db():
    c = get_component(PATTERN_COMPONENT)
    fin  = os.path.join(c.src_dir, 'database.smt2')
    fout = os.path.join(c.src_dir, 'database.h')
    mk_genfile_common.mk_pat_db_internal(fin, fout)
    if VERBOSE:
        print("Generated '{}'".format(fout))

# Update version numbers
def update_version():
    major = VER_MAJOR
    minor = VER_MINOR
    build = VER_BUILD
    revision = VER_TWEAK
    if major is None or minor is None or build is None or revision is None:
        raise MKException("set_version(major, minor, build, revision) must be used before invoking update_version()")
    if not ONLY_MAKEFILES:
        mk_version_dot_h(major, minor, build, revision)
        mk_all_assembly_infos(major, minor, build, revision)
        mk_def_files()

def get_full_version_string(major, minor, build, revision):
    global GIT_HASH, GIT_DESCRIBE
    res = "Z3 %s.%s.%s.%s" % (major, minor, build, revision)
    if GIT_HASH:
        res += " " + GIT_HASH
    if GIT_DESCRIBE:
        branch = check_output(['git', 'rev-parse', '--abbrev-ref', 'HEAD'])
        res += " " + branch + " " + check_output(['git', 'describe'])
    return '"' + res + '"'

# Update files with the version number
def mk_version_dot_h(major, minor, build, revision):
    c = get_component(UTIL_COMPONENT)
    version_template = os.path.join(c.src_dir, 'z3_version.h.in')
    version_header_output = os.path.join(c.src_dir, 'z3_version.h')
    # Note the substitution names are what is used by the CMake
    # builds system. If you change these you should change them
    # in the CMake build too
    configure_file(version_template, version_header_output,
        { 'Z3_VERSION_MAJOR': str(major),
          'Z3_VERSION_MINOR': str(minor),
          'Z3_VERSION_PATCH': str(build),
          'Z3_VERSION_TWEAK': str(revision),
          'Z3_FULL_VERSION': get_full_version_string(major, minor, build, revision)
        }
    )
    if VERBOSE:
        print("Generated '%s'" % version_header_output)

# Generate AssemblyInfo.cs files with the right version numbers by using ``AssemblyInfo.cs.in`` files as a template
def mk_all_assembly_infos(major, minor, build, revision):
    for c in get_components():
        if c.has_assembly_info():
            c.make_assembly_info(major, minor, build, revision)

def get_header_files_for_components(component_src_dirs):
    assert isinstance(component_src_dirs, list)
    h_files_full_path = []
    for component_src_dir in sorted(component_src_dirs):
        h_files = filter(lambda f: f.endswith('.h') or f.endswith('.hpp'), os.listdir(component_src_dir))
        h_files = list(map(lambda p: os.path.join(component_src_dir, p), h_files))
        h_files_full_path.extend(h_files)
    return h_files_full_path

def mk_install_tactic_cpp(cnames, path):
    component_src_dirs = []
    for cname in cnames:
        print("Component %s" % cname)
        c = get_component(cname)
        component_src_dirs.append(c.src_dir)
    h_files_full_path = get_header_files_for_components(component_src_dirs)
    generated_file = mk_genfile_common.mk_install_tactic_cpp_internal(h_files_full_path, path)
    if VERBOSE:
        print("Generated '{}'".format(generated_file))

def mk_all_install_tactic_cpps():
    if not ONLY_MAKEFILES:
        for c in get_components():
            if c.require_install_tactics():
                cnames = []
                cnames.extend(c.deps)
                cnames.append(c.name)
                mk_install_tactic_cpp(cnames, c.src_dir)

def mk_mem_initializer_cpp(cnames, path):
    component_src_dirs = []
    for cname in cnames:
        c = get_component(cname)
        component_src_dirs.append(c.src_dir)
    h_files_full_path = get_header_files_for_components(component_src_dirs)
    generated_file = mk_genfile_common.mk_mem_initializer_cpp_internal(h_files_full_path, path)
    if VERBOSE:
        print("Generated '{}'".format(generated_file))

def mk_all_mem_initializer_cpps():
    if not ONLY_MAKEFILES:
        for c in get_components():
            if c.require_mem_initializer():
                cnames = []
                cnames.extend(c.deps)
                cnames.append(c.name)
                mk_mem_initializer_cpp(cnames, c.src_dir)

def mk_gparams_register_modules(cnames, path):
    component_src_dirs = []
    for cname in cnames:
        c = get_component(cname)
        component_src_dirs.append(c.src_dir)
    h_files_full_path = get_header_files_for_components(component_src_dirs)
    generated_file = mk_genfile_common.mk_gparams_register_modules_internal(h_files_full_path, path)
    if VERBOSE:
        print("Generated '{}'".format(generated_file))

def mk_all_gparams_register_modules():
    if not ONLY_MAKEFILES:
        for c in get_components():
            if c.require_mem_initializer():
                cnames = []
                cnames.extend(c.deps)
                cnames.append(c.name)
                mk_gparams_register_modules(cnames, c.src_dir)

# Generate a .def based on the files at c.export_files slot.
def mk_def_file(c):
    defname = '%s.def' % os.path.join(c.src_dir, c.name)
    dll_name = c.dll_name
    export_header_files = []
    for dot_h in c.export_files:
        dot_h_c = c.find_file(dot_h, c.name)
        api = os.path.join(dot_h_c.src_dir, dot_h)
        export_header_files.append(api)
    mk_genfile_common.mk_def_file_internal(defname, dll_name, export_header_files)
    if VERBOSE:
        print("Generated '%s'" % defname)

def mk_def_files():
    if not ONLY_MAKEFILES:
        for c in get_components():
            if c.require_def_file():
                mk_def_file(c)

def cp_z3py_to_build():
    mk_dir(BUILD_DIR)
    mk_dir(os.path.join(BUILD_DIR, 'python'))
    z3py_dest = os.path.join(BUILD_DIR, 'python', 'z3')
    z3py_src = os.path.join(Z3PY_SRC_DIR, 'z3')

    # Erase existing .pyc files
    for root, dirs, files in os.walk(Z3PY_SRC_DIR):
        for f in files:
            if f.endswith('.pyc'):
                rmf(os.path.join(root, f))
    # Compile Z3Py files
    if compileall.compile_dir(z3py_src, force=1) != 1:
        raise MKException("failed to compile Z3Py sources")
    if is_verbose:
        print("Generated python bytecode")
    # Copy sources to build
    mk_dir(z3py_dest)
    for py in filter(lambda f: f.endswith('.py'), os.listdir(z3py_src)):
        shutil.copyfile(os.path.join(z3py_src, py), os.path.join(z3py_dest, py))
        if is_verbose():
            print("Copied '%s'" % py)
    # Python 2.x support
    for pyc in filter(lambda f: f.endswith('.pyc'), os.listdir(z3py_src)):
        shutil.copyfile(os.path.join(z3py_src, pyc), os.path.join(z3py_dest, pyc))
        if is_verbose():
            print("Copied '%s'" % pyc)
    # Python 3.x support
    src_pycache = os.path.join(z3py_src, '__pycache__')
    target_pycache = os.path.join(z3py_dest, '__pycache__')
    if os.path.exists(src_pycache):
        for pyc in filter(lambda f: f.endswith('.pyc'), os.listdir(src_pycache)):
            mk_dir(target_pycache)
            shutil.copyfile(os.path.join(src_pycache, pyc), os.path.join(target_pycache, pyc))
            if is_verbose():
                print("Copied '%s'" % pyc)
    # Copy z3test.py
    shutil.copyfile(os.path.join(Z3PY_SRC_DIR, 'z3test.py'), os.path.join(BUILD_DIR, 'python', 'z3test.py'))

def mk_bindings(api_files):
    if not ONLY_MAKEFILES:
        mk_z3consts_py(api_files)
        new_api_files = []
        api = get_component(API_COMPONENT)
        for api_file in api_files:
            api_file_path = api.find_file(api_file, api.name)
            new_api_files.append(os.path.join(api_file_path.src_dir, api_file))
        g = globals()
        g["API_FILES"] = new_api_files
        if is_java_enabled():
            check_java()
            mk_z3consts_java(api_files)
        # Generate some of the bindings and "api" module files
        import update_api
        dotnet_output_dir = None
        if is_dotnet_core_enabled():
          dotnet_output_dir = os.path.join(BUILD_DIR, 'dotnet')
          mk_dir(dotnet_output_dir)
        java_output_dir = None
        java_package_name = None
        if is_java_enabled():
          java_output_dir = get_component('java').src_dir
          java_package_name = get_component('java').package_name
        ml_output_dir = None
        if is_ml_enabled():
          ml_output_dir = get_component('ml').src_dir
        if is_js_enabled():
          set_z3js_dir("api/js")
          js_output_dir = get_component('js').src_dir
        # Get the update_api module to do the work for us
        update_api.generate_files(api_files=new_api_files,
          api_output_dir=get_component('api').src_dir,
          z3py_output_dir=get_z3py_dir(),
          dotnet_output_dir=dotnet_output_dir,
          java_output_dir=java_output_dir,
          java_package_name=java_package_name,
          js_output_dir=get_z3js_dir(),
          ml_output_dir=ml_output_dir,
          ml_src_dir=ml_output_dir
        )
        cp_z3py_to_build()
        if is_ml_enabled():
            check_ml()
            mk_z3consts_ml(api_files)
        if  is_dotnet_core_enabled():
            check_dotnet_core()
            mk_z3consts_dotnet(api_files, dotnet_output_dir)

# Extract enumeration types from API files, and add python definitions.
def mk_z3consts_py(api_files):
    if Z3PY_SRC_DIR is None:
        raise MKException("You must invoke set_z3py_dir(path):")
    full_path_api_files = []
    api_dll = get_component(Z3_DLL_COMPONENT)
    for api_file in api_files:
        api_file_c = api_dll.find_file(api_file, api_dll.name)
        api_file   = os.path.join(api_file_c.src_dir, api_file)
        full_path_api_files.append(api_file)
    generated_file = mk_genfile_common.mk_z3consts_py_internal(full_path_api_files, Z3PY_SRC_DIR)
    if VERBOSE:
        print("Generated '{}".format(generated_file))

# Extract enumeration types from z3_api.h, and add .Net definitions
def mk_z3consts_dotnet(api_files, output_dir):
    dotnet = get_component(DOTNET_COMPONENT)
    if not dotnet:
       dotnet = get_component(DOTNET_CORE_COMPONENT)
    full_path_api_files = []
    for api_file in api_files:
        api_file_c = dotnet.find_file(api_file, dotnet.name)
        api_file   = os.path.join(api_file_c.src_dir, api_file)
        full_path_api_files.append(api_file)
    generated_file = mk_genfile_common.mk_z3consts_dotnet_internal(full_path_api_files, output_dir)
    if VERBOSE:
        print("Generated '{}".format(generated_file))

# Extract enumeration types from z3_api.h, and add Java definitions
def mk_z3consts_java(api_files):
    java = get_component(JAVA_COMPONENT)
    full_path_api_files = []
    for api_file in api_files:
        api_file_c = java.find_file(api_file, java.name)
        api_file   = os.path.join(api_file_c.src_dir, api_file)
        full_path_api_files.append(api_file)
    generated_files = mk_genfile_common.mk_z3consts_java_internal(
        full_path_api_files,
        java.package_name,
        java.src_dir)
    if VERBOSE:
        for generated_file in generated_files:
            print("Generated '{}'".format(generated_file))

# Extract enumeration types from z3_api.h, and add ML definitions
def mk_z3consts_ml(api_files):
    ml = get_component(ML_COMPONENT)
    full_path_api_files = []
    for api_file in api_files:
        api_file_c = ml.find_file(api_file, ml.name)
        api_file   = os.path.join(api_file_c.src_dir, api_file)
        full_path_api_files.append(api_file)
    generated_file = mk_genfile_common.mk_z3consts_ml_internal(
        full_path_api_files,
        ml.src_dir)
    if VERBOSE:
        print ('Generated "%s"' % generated_file)

def mk_gui_str(id):
    return '4D2F40D8-E5F9-473B-B548-%012d' % id

def get_platform_toolset_str():
    default = 'v110';
    vstr = check_output(['msbuild', '/ver'])
    lines = vstr.split('\n')
    lline = lines[-1]
    tokens = lline.split('.')
    if len(tokens) < 2:
        return default
    else:
        if tokens[0] == "15": 
            # Visual Studio 2017 reports 15.* but the PlatformToolsetVersion is 141
            return "v141"
        else:
            return 'v' + tokens[0] + tokens[1]

def mk_vs_proj_property_groups(f, name, target_ext, type):
    f.write('  <ItemGroup Label="ProjectConfigurations">\n')
    f.write('    <ProjectConfiguration Include="Debug|Win32">\n')
    f.write('      <Configuration>Debug</Configuration>\n')
    f.write('      <Platform>Win32</Platform>\n')
    f.write('    </ProjectConfiguration>\n')
    f.write('    <ProjectConfiguration Include="Release|Win32">\n')
    f.write('      <Configuration>Release</Configuration>\n')
    f.write('      <Platform>Win32</Platform>\n')
    f.write('    </ProjectConfiguration>\n')
    f.write('  </ItemGroup>\n')
    f.write('  <PropertyGroup Label="Globals">\n')
    f.write('    <ProjectGuid>{%s}</ProjectGuid>\n' % mk_gui_str(0))
    f.write('    <ProjectName>%s</ProjectName>\n' % name)
    f.write('    <Keyword>Win32Proj</Keyword>\n')
    f.write('    <PlatformToolset>%s</PlatformToolset>\n' % get_platform_toolset_str())
    f.write('  </PropertyGroup>\n')
    f.write('  <Import Project="$(VCTargetsPath)\Microsoft.Cpp.Default.props" />\n')
    f.write('  <PropertyGroup Condition="\'$(Configuration)|$(Platform)\'==\'Debug|Win32\'" Label="Configuration">\n')
    f.write('    <ConfigurationType>%s</ConfigurationType>\n' % type)
    f.write('    <CharacterSet>Unicode</CharacterSet>\n')
    f.write('    <UseOfMfc>false</UseOfMfc>\n')
    f.write('  </PropertyGroup>\n')
    f.write('  <PropertyGroup Condition="\'$(Configuration)|$(Platform)\'==\'Release|Win32\'" Label="Configuration">\n')
    f.write('    <ConfigurationType>%s</ConfigurationType>\n' % type)
    f.write('    <CharacterSet>Unicode</CharacterSet>\n')
    f.write('    <UseOfMfc>false</UseOfMfc>\n')
    f.write('  </PropertyGroup>\n')
    f.write('  <Import Project="$(VCTargetsPath)\Microsoft.Cpp.props" />\n')
    f.write('  <ImportGroup Label="ExtensionSettings" />\n')
    f.write('   <ImportGroup Label="PropertySheets">\n')
    f.write('    <Import Project="$(UserRootDir)\Microsoft.Cpp.$(Platform).user.props" Condition="exists(\'$(UserRootDir)\Microsoft.Cpp.$(Platform).user.props\')" Label="LocalAppDataPlatform" />  </ImportGroup>\n')
    f.write('  <PropertyGroup Label="UserMacros" />\n')
    f.write('  <PropertyGroup>\n')
    f.write('    <OutDir Condition="\'$(Configuration)|$(Platform)\'==\'Debug|Win32\'">$(SolutionDir)\$(ProjectName)\$(Configuration)\</OutDir>\n')
    f.write('    <TargetName Condition="\'$(Configuration)|$(Platform)\'==\'Debug|Win32\'">%s</TargetName>\n' % name)
    f.write('    <TargetExt Condition="\'$(Configuration)|$(Platform)\'==\'Debug|Win32\'">.%s</TargetExt>\n' % target_ext)
    f.write('    <OutDir Condition="\'$(Configuration)|$(Platform)\'==\'Release|Win32\'">$(SolutionDir)\$(ProjectName)\$(Configuration)\</OutDir>\n')
    f.write('    <TargetName Condition="\'$(Configuration)|$(Platform)\'==\'Release|Win32\'">%s</TargetName>\n' % name)
    f.write('    <TargetExt Condition="\'$(Configuration)|$(Platform)\'==\'Release|Win32\'">.%s</TargetExt>\n' % target_ext)
    f.write('  </PropertyGroup>\n')
    f.write('  <PropertyGroup Condition="\'$(Configuration)|$(Platform)\'==\'Debug|Win32\'">\n')
    f.write('        <IntDir>$(ProjectName)\$(Configuration)\</IntDir>\n')
    f.write('  </PropertyGroup>\n')
    f.write('  <PropertyGroup Condition="\'$(Configuration)|$(Platform)\'==\'Release|Win32\'">\n')
    f.write('    <IntDir>$(ProjectName)\$(Configuration)\</IntDir>\n')
    f.write('  </PropertyGroup>\n')


def mk_vs_proj_cl_compile(f, name, components, debug):
    f.write('    <ClCompile>\n')
    f.write('      <Optimization>Disabled</Optimization>\n')
    if debug:
        f.write('      <PreprocessorDefinitions>WIN32;_DEBUG;Z3DEBUG;_TRACE;_MP_INTERNAL;_WINDOWS;%(PreprocessorDefinitions)</PreprocessorDefinitions>\n')
    else:
        f.write('      <PreprocessorDefinitions>WIN32;NDEBUG;_MP_INTERNAL;_WINDOWS;%(PreprocessorDefinitions)</PreprocessorDefinitions>\n')
    if VS_PAR:
        f.write('      <MinimalRebuild>false</MinimalRebuild>\n')
        f.write('      <MultiProcessorCompilation>true</MultiProcessorCompilation>\n')
    else:
        f.write('      <MinimalRebuild>true</MinimalRebuild>\n')
    f.write('      <BasicRuntimeChecks>EnableFastChecks</BasicRuntimeChecks>\n')
    f.write('      <WarningLevel>Level3</WarningLevel>\n')
    if debug:
        f.write('      <RuntimeLibrary>MultiThreadedDebugDLL</RuntimeLibrary>\n')
    else:
        f.write('      <RuntimeLibrary>MultiThreadedDLL</RuntimeLibrary>\n')
    f.write('      <DebugInformationFormat>ProgramDatabase</DebugInformationFormat>\n')
    f.write('      <AdditionalIncludeDirectories>')
    deps = find_all_deps(name, components)
    first = True
    for dep in deps:
        if first:
            first = False
        else:
            f.write(';')
        f.write(get_component(dep).to_src_dir)
    f.write(';%s\n' % os.path.join(REV_BUILD_DIR, SRC_DIR))
    f.write('</AdditionalIncludeDirectories>\n')
    f.write('    </ClCompile>\n')

def mk_vs_proj_dep_groups(f, name, components):
    f.write('  <ItemGroup>\n')
    deps = find_all_deps(name, components)
    for dep in deps:
        dep = get_component(dep)
        for cpp in filter(lambda f: f.endswith('.cpp'), os.listdir(dep.src_dir)):
            f.write('    <ClCompile Include="%s" />\n' % os.path.join(dep.to_src_dir, cpp))
    f.write('  </ItemGroup>\n')

def mk_vs_proj_link_exe(f, name, debug):
    f.write('    <Link>\n')
    f.write('      <OutputFile>$(OutDir)%s.exe</OutputFile>\n' % name)
    f.write('      <GenerateDebugInformation>true</GenerateDebugInformation>\n')
    f.write('      <SubSystem>Console</SubSystem>\n')
    f.write('      <StackReserveSize>8388608</StackReserveSize>\n')
    f.write('      <RandomizedBaseAddress>false</RandomizedBaseAddress>\n')
    f.write('      <DataExecutionPrevention/>\n')
    f.write('      <TargetMachine>MachineX86</TargetMachine>\n')
    f.write('      <AdditionalLibraryDirectories>%(AdditionalLibraryDirectories)</AdditionalLibraryDirectories>\n')
    f.write('      <AdditionalDependencies>psapi.lib;kernel32.lib;user32.lib;gdi32.lib;winspool.lib;comdlg32.lib;advapi32.lib;shell32.lib;ole32.lib;oleaut32.lib;uuid.lib;odbc32.lib;odbccp32.lib;%(AdditionalDependencies)</AdditionalDependencies>\n')
    f.write('    </Link>\n')

def mk_vs_proj(name, components):
    if not VS_PROJ:
        return
    proj_name = '%s.vcxproj' % os.path.join(BUILD_DIR, name)
    modes=['Debug', 'Release']
    PLATFORMS=['Win32']
    f = open(proj_name, 'w')
    f.write('<?xml version="1.0" encoding="utf-8"?>\n')
    f.write('<Project DefaultTargets="Build" ToolsVersion="4.0" xmlns="http://schemas.microsoft.com/developer/msbuild/2003">\n')
    mk_vs_proj_property_groups(f, name, 'exe', 'Application')
    f.write('  <ItemDefinitionGroup Condition="\'$(Configuration)|$(Platform)\'==\'Debug|Win32\'">\n')
    mk_vs_proj_cl_compile(f, name, components, debug=True)
    mk_vs_proj_link_exe(f, name, debug=True)
    f.write('  </ItemDefinitionGroup>\n')
    f.write('  <ItemDefinitionGroup Condition="\'$(Configuration)|$(Platform)\'==\'Release|Win32\'">\n')
    mk_vs_proj_cl_compile(f, name, components, debug=False)
    mk_vs_proj_link_exe(f, name, debug=False)
    f.write('  </ItemDefinitionGroup>\n')
    mk_vs_proj_dep_groups(f, name, components)
    f.write('  <Import Project="$(VCTargetsPath)\Microsoft.Cpp.targets" />\n')
    f.write('  <ImportGroup Label="ExtensionTargets">\n')
    f.write('  </ImportGroup>\n')
    f.write('</Project>\n')
    f.close()
    if is_verbose():
        print("Generated '%s'" % proj_name)

def mk_vs_proj_link_dll(f, name, debug):
    f.write('    <Link>\n')
    f.write('      <OutputFile>$(OutDir)%s.dll</OutputFile>\n' % name)
    f.write('      <GenerateDebugInformation>true</GenerateDebugInformation>\n')
    f.write('      <SubSystem>Console</SubSystem>\n')
    f.write('      <StackReserveSize>8388608</StackReserveSize>\n')
    f.write('      <RandomizedBaseAddress>false</RandomizedBaseAddress>\n')
    f.write('      <DataExecutionPrevention/>\n')
    f.write('      <TargetMachine>MachineX86</TargetMachine>\n')
    f.write('      <AdditionalLibraryDirectories>%(AdditionalLibraryDirectories)</AdditionalLibraryDirectories>\n')
    f.write('      <AdditionalDependencies>psapi.lib;kernel32.lib;user32.lib;gdi32.lib;winspool.lib;comdlg32.lib;advapi32.lib;shell32.lib;ole32.lib;oleaut32.lib;uuid.lib;odbc32.lib;odbccp32.lib;%(AdditionalDependencies)</AdditionalDependencies>\n')
    f.write('      <ModuleDefinitionFile>%s</ModuleDefinitionFile>' % os.path.join(get_component('api_dll').to_src_dir, 'api_dll.def'))
    f.write('    </Link>\n')

def mk_vs_proj_dll(name, components):
    if not VS_PROJ:
        return
    proj_name = '%s.vcxproj' % os.path.join(BUILD_DIR, name)
    modes=['Debug', 'Release']
    PLATFORMS=['Win32']
    f = open(proj_name, 'w')
    f.write('<?xml version="1.0" encoding="utf-8"?>\n')
    f.write('<Project DefaultTargets="Build" ToolsVersion="4.0" xmlns="http://schemas.microsoft.com/developer/msbuild/2003">\n')
    mk_vs_proj_property_groups(f, name, 'dll', 'DynamicLibrary')
    f.write('  <ItemDefinitionGroup Condition="\'$(Configuration)|$(Platform)\'==\'Debug|Win32\'">\n')
    mk_vs_proj_cl_compile(f, name, components, debug=True)
    mk_vs_proj_link_dll(f, name, debug=True)
    f.write('  </ItemDefinitionGroup>\n')
    f.write('  <ItemDefinitionGroup Condition="\'$(Configuration)|$(Platform)\'==\'Release|Win32\'">\n')
    mk_vs_proj_cl_compile(f, name, components, debug=False)
    mk_vs_proj_link_dll(f, name, debug=False)
    f.write('  </ItemDefinitionGroup>\n')
    mk_vs_proj_dep_groups(f, name, components)
    f.write('  <Import Project="$(VCTargetsPath)\Microsoft.Cpp.targets" />\n')
    f.write('  <ImportGroup Label="ExtensionTargets">\n')
    f.write('  </ImportGroup>\n')
    f.write('</Project>\n')
    f.close()
    if is_verbose():
        print("Generated '%s'" % proj_name)

def mk_win_dist(build_path, dist_path):
    for c in get_components():
        c.mk_win_dist(build_path, dist_path)

def mk_unix_dist(build_path, dist_path):
    for c in get_components():
        c.mk_unix_dist(build_path, dist_path)
    # Add Z3Py to bin directory
    for pyc in filter(lambda f: f.endswith('.pyc') or f.endswith('.py'), os.listdir(build_path)):
        shutil.copy(os.path.join(build_path, pyc),
                    os.path.join(dist_path, INSTALL_BIN_DIR, pyc))

class MakeRuleCmd(object):
    """
        These class methods provide a convenient way to emit frequently
        needed commands used in Makefile rules
        Note that several of the method are meant for use during ``make
        install`` and ``make uninstall``.  These methods correctly use
        ``$(PREFIX)`` and ``$(DESTDIR)`` and therefore are preferable
        to writing commands manually which can be error prone.
    """
    @classmethod
    def install_root(cls):
        """
            Returns a string that will expand to the
            install location when used in a makefile rule.
        """
        # Note: DESTDIR is to support staged installs
        return "$(DESTDIR)$(PREFIX)/"

    @classmethod
    def _is_str(cls, obj):
        if sys.version_info.major > 2:
            # Python 3 or newer. Strings are always unicode and of type str
            return isinstance(obj, str)
        else:
            # Python 2. Has byte-string and unicode representation, allow both
            return isinstance(obj, str) or isinstance(obj, unicode)

    @classmethod
    def _install_root(cls, path, in_prefix, out, is_install=True):
        if not in_prefix:
            # The Python bindings on OSX are sometimes not installed inside the prefix.
            install_root = "$(DESTDIR)"
            action_string = 'install' if is_install else 'uninstall'
            cls.write_cmd(out, 'echo "WARNING: {}ing files/directories ({}) that are not in the install prefix ($(PREFIX))."'.format(
                    action_string, path))
            #print("WARNING: Generating makefile rule that {}s {} '{}' which is outside the installation prefix '{}'.".format(
            #        action_string, 'to' if is_install else 'from', path, PREFIX))
        else:
            # assert not os.path.isabs(path)
            install_root = cls.install_root()
        return install_root

    @classmethod
    def install_files(cls, out, src_pattern, dest, in_prefix=True):
        assert len(dest) > 0
        assert cls._is_str(src_pattern)
        assert not ' ' in src_pattern
        assert cls._is_str(dest)
        assert not ' ' in dest
        assert not os.path.isabs(src_pattern)
        install_root = cls._install_root(dest, in_prefix, out)

        cls.write_cmd(out, "cp {src_pattern} {install_root}{dest}".format(
            src_pattern=src_pattern,
            install_root=install_root,
            dest=dest))

    @classmethod
    def remove_installed_files(cls, out, pattern, in_prefix=True):
        assert len(pattern) > 0
        assert cls._is_str(pattern)
        assert not ' ' in pattern
        install_root = cls._install_root(pattern, in_prefix, out, is_install=False)

        cls.write_cmd(out, "rm -f {install_root}{pattern}".format(
            install_root=install_root,
            pattern=pattern))

    @classmethod
    def make_install_directory(cls, out, dir, in_prefix=True):
        assert len(dir) > 0
        assert cls._is_str(dir)
        assert not ' ' in dir
        install_root = cls._install_root(dir, in_prefix, out)

        if is_windows():
            cls.write_cmd(out, "IF NOT EXIST {dir} (mkdir {dir})".format(
                install_root=install_root,
                dir=dir))
        else:
            cls.write_cmd(out, "mkdir -p {install_root}{dir}".format(
                install_root=install_root,
                dir=dir))

    @classmethod
    def _is_path_prefix_of(cls, temp_path, target_as_abs):
        """
            Returns True iff ``temp_path`` is a path prefix
            of ``target_as_abs``
        """
        assert cls._is_str(temp_path)
        assert cls._is_str(target_as_abs)
        assert len(temp_path) > 0
        assert len(target_as_abs) > 0
        assert os.path.isabs(temp_path)
        assert os.path.isabs(target_as_abs)

        # Need to stick extra slash in front otherwise we might think that
        # ``/lib`` is a prefix of ``/lib64``.  Of course if ``temp_path ==
        # '/'`` then we shouldn't else we would check if ``//`` (rather than
        # ``/``) is a prefix of ``/lib64``, which would fail.
        if len(temp_path) > 1:
            temp_path += os.sep
        return target_as_abs.startswith(temp_path)

    @classmethod
    def create_relative_symbolic_link(cls, out, target, link_name):
        assert cls._is_str(target)
        assert cls._is_str(link_name)
        assert len(target) > 0
        assert len(link_name) > 0
        assert not os.path.isabs(target)
        assert not os.path.isabs(link_name)

        # We can't test to see if link_name is a file or directory
        # because it may not exist yet. Instead follow the convention
        # that if there is a leading slash target is a directory otherwise
        # it's a file
        if link_name[-1] != '/':
            # link_name is a file
            temp_path = os.path.dirname(link_name)
        else:
            # link_name is a directory
            temp_path = link_name[:-1]
        temp_path = '/' + temp_path
        relative_path = ""
        targetAsAbs = '/' + target
        assert os.path.isabs(targetAsAbs)
        assert os.path.isabs(temp_path)
        # Keep walking up the directory tree until temp_path
        # is a prefix of targetAsAbs
        while not cls._is_path_prefix_of(temp_path, targetAsAbs):
            assert temp_path != '/'
            temp_path = os.path.dirname(temp_path)
            relative_path += '../'

        # Now get the path from the common prefix directory to the target
        target_from_prefix = targetAsAbs[len(temp_path):]
        relative_path += target_from_prefix
        # Remove any double slashes
        relative_path = relative_path.replace('//','/')
        cls.create_symbolic_link(out, relative_path, link_name)

    @classmethod
    def create_symbolic_link(cls, out, target, link_name):
        assert cls._is_str(target)
        assert cls._is_str(link_name)
        assert not os.path.isabs(target)

        cls.write_cmd(out, 'ln -s {target} {install_root}{link_name}'.format(
            target=target,
            install_root=cls.install_root(),
            link_name=link_name))

    # TODO: Refactor all of the build system to emit commands using this
    # helper to simplify code. This will also let us replace ``@`` with
    # ``$(Verb)`` and have it set to ``@`` or empty at build time depending on
    # a variable (e.g. ``VERBOSE``) passed to the ``make`` invocation. This
    # would be very helpful for debugging.
    @classmethod
    def write_cmd(cls, out, line):
        out.write("\t@{}\n".format(line))

def strip_path_prefix(path, prefix):
    if path.startswith(prefix):
        stripped_path = path[len(prefix):]
        stripped_path.replace('//','/')
        if stripped_path[0] == '/':
            stripped_path = stripped_path[1:]
        assert not os.path.isabs(stripped_path)
        return stripped_path
    else:
        return path

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
        raise MKException('Could not find template file "{}"'.format(template_file_path))

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

if __name__ == '__main__':
    import doctest
    doctest.testmod()
