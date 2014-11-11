############################################
# Copyright (c) 2012 Microsoft Corporation
#
# Auxiliary scripts for generating Makefiles
# and Visual Studio project files.
#
# Author: Leonardo de Moura (leonardo)
############################################
import sys
import os
import glob
import re
import getopt
import shutil
from mk_exception import *
from fnmatch import fnmatch
import distutils.sysconfig
import compileall
import subprocess
import string

def getenv(name, default):
    try:
        return os.environ[name].strip(' "\'')
    except:
        return default

CXX=getenv("CXX", None)
CC=getenv("CC", None)
CPPFLAGS=getenv("CPPFLAGS", "")
CXXFLAGS=getenv("CXXFLAGS", "")
EXAMP_DEBUG_FLAG=''
LDFLAGS=getenv("LDFLAGS", "")
JNI_HOME=getenv("JNI_HOME", None)

CXX_COMPILERS=['g++', 'clang++']
C_COMPILERS=['gcc', 'clang']
JAVAC=None
JAR=None
PYTHON_PACKAGE_DIR=distutils.sysconfig.get_python_lib()
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
JAVA_COMPONENT='java'
CPP_COMPONENT='cpp'
#####################
IS_WINDOWS=False
IS_LINUX=False
IS_OSX=False
IS_FREEBSD=False
VERBOSE=True
DEBUG_MODE=False
SHOW_CPPS = True
VS_X64 = False
ONLY_MAKEFILES = False
Z3PY_SRC_DIR=None
VS_PROJ = False
TRACE = False
DOTNET_ENABLED=False
JAVA_ENABLED=False
STATIC_LIB=False
VER_MAJOR=None
VER_MINOR=None
VER_BUILD=None
VER_REVISION=None
PREFIX=os.path.split(os.path.split(os.path.split(PYTHON_PACKAGE_DIR)[0])[0])[0]
GMP=False
FOCI2=False
FOCI2LIB=''
VS_PAR=False
VS_PAR_NUM=8
GPROF=False
GIT_HASH=False

def check_output(cmd):
    return str(subprocess.Popen(cmd, stdout=subprocess.PIPE).communicate()[0]).rstrip('\r\n')

def git_hash():
    try:
        branch = check_output(['git', 'rev-parse', '--abbrev-ref', 'HEAD'])
        r = check_output(['git', 'show-ref', '--abbrev=12', 'refs/heads/%s' % branch])
    except:
        raise MKException("Failed to retrieve git hash")
    ls = r.split(' ')
    if len(ls) != 2:
        raise MKException("Unexpected git output")
    return ls[0]

def is_windows():
    return IS_WINDOWS

def is_linux():
    return IS_LINUX

def is_freebsd():
    return IS_FREEBSD

def is_osx():
    return IS_OSX

def norm_path(p):
    # We use '/' on mk_project for convenience
    return os.path.join(*(p.split('/')))

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

# rm -f fname
def rmf(fname):
    if os.path.exists(fname):
        os.remove(fname)

def exec_compiler_cmd(cmd):
    r = exec_cmd(cmd)
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

def test_foci2(cc,foci2lib):
    if is_verbose():
        print("Testing FOCI2...")
    t = TempFile('tstfoci2.cpp')
    t.add('#include<foci2.h>\nint main() { foci2 *f = foci2::create("lia"); return 0; }\n')
    t.commit()
    return exec_compiler_cmd([cc, CPPFLAGS, '-Isrc/interp', 'tstfoci2.cpp', LDFLAGS, foci2lib]) == 0

def test_openmp(cc):
    if is_verbose():
        print("Testing OpenMP...")
    t = TempFile('tstomp.cpp')
    t.add('#include<omp.h>\nint main() { return omp_in_parallel() ? 1 : 0; }\n')
    t.commit()
    return exec_compiler_cmd([cc, CPPFLAGS, 'tstomp.cpp', LDFLAGS, '-fopenmp']) == 0

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

    if JDK_HOME != None:
        if IS_WINDOWS:
            JAVAC = os.path.join(JDK_HOME, 'bin', 'javac.exe')
        else:
            JAVAC = os.path.join(JDK_HOME, 'bin', 'javac')

        if not os.path.exists(JAVAC):
            raise MKException("Failed to detect javac at '%s/bin'; the environment variable JDK_HOME is probably set to the wrong path." % os.path.join(JDK_HOME))
    else:
        # Search for javac in the path.
        ind = 'javac';
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

    if JAVAC == None:
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
        subprocess.call([JAVAC, 'Hello.java', '-verbose'], stdout=oo.fname, stderr=eo.fname)
        oo.commit()
        eo.commit()
    except:
        raise MKException('Found, but failed to run Java compiler at %s' % (JAVAC))

    os.remove('Hello.class')

    if is_verbose():
        print("Finding jni.h...")

    if JNI_HOME != None:
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
                    if cdirs.count(q) == 0:
                        cdirs.append(q)

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
            if q != False:
                JNI_HOME = q

        if JNI_HOME == None:
            raise MKException("Failed to detect jni.h. Possible solution: set JNI_HOME with the path to JDK.")

def is64():
    return sys.maxsize >= 2**32

def check_ar():
    if is_verbose():
        print("Testing ar...")
    if which('ar')== None:
        raise MKException('ar (archive tool) was not found')

def find_cxx_compiler():
    global CXX, CXX_COMPILERS
    if CXX != None:
        if test_cxx_compiler(CXX):
            return CXX
    for cxx in CXX_COMPILERS:
        if test_cxx_compiler(cxx):
            CXX = cxx
            return CXX
    raise MKException('C++ compiler was not found. Try to set the environment variable CXX with the C++ compiler available in your system.')

def find_c_compiler():
    global CC, C_COMPILERS
    if CC != None:
        if test_c_compiler(CC):
            return CC
    for c in C_COMPILERS:
        if test_c_compiler(c):
            CC = c
            return CC
    raise MKException('C compiler was not found. Try to set the environment variable CC with the C compiler available in your system.')

def set_version(major, minor, build, revision):
    global VER_MAJOR, VER_MINOR, VER_BUILD, VER_REVISION
    VER_MAJOR = major
    VER_MINOR = minor
    VER_BUILD = build
    VER_REVISION = revision

def get_version():
    return (VER_MAJOR, VER_MINOR, VER_BUILD, VER_REVISION)

def build_static_lib():
    return STATIC_LIB

def is_cr_lf(fname):
    # Check whether text files use cr/lf
    f = open(fname, 'r')
    line = f.readline()
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

def dos2unix_tree_core(pattern, dir, files):
    for filename in files:
        if fnmatch(filename, pattern):
            fname = os.path.join(dir, filename)
            if not os.path.isdir(fname):
                dos2unix(fname)

def dos2unix_tree():
    os.path.walk('src', dos2unix_tree_core, '*')

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
    # Enable .Net bindings by default on windows
    DOTNET_ENABLED=True
elif os.name == 'posix':
    if os.uname()[0] == 'Darwin':
        IS_OSX=True
    elif os.uname()[0] == 'Linux':
        IS_LINUX=True
    elif os.uname()[0] == 'FreeBSD':
        IS_FREEBSD=True

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
    print("  -b <sudir>, --build=<subdir>  subdirectory where Z3 will be built (default: build).")
    print("  --githash=hash                include the given hash in the binaries.")
    print("  -d, --debug                   compile Z3 in debug mode.")
    print("  -t, --trace                   enable tracing in release mode.")
    if IS_WINDOWS:
        print("  -x, --x64                     create 64 binary when using Visual Studio.")
    print("  -m, --makefiles               generate only makefiles.")
    if IS_WINDOWS:
        print("  -v, --vsproj                  generate Visual Studio Project Files.")
    if IS_WINDOWS:
        print("  -n, --nodotnet                do not generate Microsoft.Z3.dll make rules.")
    print("  -j, --java                    generate Java bindings.")
    print("  --staticlib                   build Z3 static library.")
    if not IS_WINDOWS:
        print("  -g, --gmp                     use GMP.")
        print("  --gprof                       enable gprof")
    print("  -f <path> --foci2=<path>          use foci2 library at path")
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
    exit(exit_code)

# Parse configuration option for mk_make script
def parse_options():
    global VERBOSE, DEBUG_MODE, IS_WINDOWS, VS_X64, ONLY_MAKEFILES, SHOW_CPPS, VS_PROJ, TRACE, VS_PAR, VS_PAR_NUM
    global DOTNET_ENABLED, JAVA_ENABLED, STATIC_LIB, PREFIX, GMP, FOCI2, FOCI2LIB, PYTHON_PACKAGE_DIR, GPROF, GIT_HASH
    try:
        options, remainder = getopt.gnu_getopt(sys.argv[1:],
                                               'b:df:sxhmcvtnp:gj',
                                               ['build=', 'debug', 'silent', 'x64', 'help', 'makefiles', 'showcpp', 'vsproj',
                                                'trace', 'nodotnet', 'staticlib', 'prefix=', 'gmp', 'foci2=', 'java', 'parallel=', 'gprof',
                                                'githash='])
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
        elif opt in ('-h', '--help'):
            display_help(0)
        elif opt in ('-m', '--onlymakefiles'):
            ONLY_MAKEFILES = True
        elif opt in ('-c', '--showcpp'):
            SHOW_CPPS = True
        elif opt in ('-v', '--vsproj'):
            VS_PROJ = True
        elif opt in ('-t', '--trace'):
            TRACE = True
        elif opt in ('-n', '--nodotnet'):
            DOTNET_ENABLED = False
        elif opt in ('--staticlib'):
            STATIC_LIB = True
        elif not IS_WINDOWS and opt in ('-p', '--prefix'):
            PREFIX = arg
            PYTHON_PACKAGE_DIR = os.path.join(PREFIX, 'lib', 'python%s' % distutils.sysconfig.get_python_version(), 'dist-packages')
            mk_dir(PYTHON_PACKAGE_DIR)
            if sys.version >= "3":
                mk_dir(os.path.join(PYTHON_PACKAGE_DIR, '__pycache__'))
        elif IS_WINDOWS and opt == '--parallel':
            VS_PAR = True
            VS_PAR_NUM = int(arg)
        elif opt in ('-g', '--gmp'):
            GMP = True
        elif opt in ('-f', '--foci2'):
            FOCI2 = True
            FOCI2LIB = arg
        elif opt in ('-j', '--java'):
            JAVA_ENABLED = True
        elif opt == '--gprof':
            GPROF = True
        elif opt == '--githash':
            GIT_HASH=arg
        else:
            print("ERROR: Invalid command line option '%s'" % opt)
            display_help(1)

# Return a list containing a file names included using '#include' in
# the given C/C++ file named fname.
def extract_c_includes(fname):
    result = []
    # We look for well behaved #include directives
    std_inc_pat     = re.compile("[ \t]*#include[ \t]*\"(.*)\"[ \t]*")
    system_inc_pat  = re.compile("[ \t]*#include[ \t]*\<.*\>[ \t]*")
    # We should generate and error for any occurrence of #include that does not match the previous pattern.
    non_std_inc_pat = re.compile(".*#include.*")

    f = open(fname, 'r')
    linenum = 1
    for line in f:
        m1 = std_inc_pat.match(line)
        if m1:
            result.append(m1.group(1))
        elif not system_inc_pat.match(line) and non_std_inc_pat.match(line):
            raise MKException("Invalid #include directive at '%s':%s" % (fname, line))
        linenum = linenum + 1
    return result


# Given a path dir1/subdir2/subdir3 returns ../../..
def reverse_path(p):
    l = p.split(os.sep)
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

# Return true if in verbose mode
def is_verbose():
    return VERBOSE

def is_java_enabled():
    return JAVA_ENABLED

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
    version_string = check_output([cc, '--version'])
    return str(version_string).find('clang') != -1

def is_CXX_clangpp():
    if is_compiler(CXX, 'g++'):
        return is_clang_in_gpp_form(CXX)
    return is_compiler(CXX, 'clang++')

def get_cpp_files(path):
    return filter(lambda f: f.endswith('.cpp'), os.listdir(path))

def get_c_files(path):
    return filter(lambda f: f.endswith('.c'), os.listdir(path))

def get_cs_files(path):
    return filter(lambda f: f.endswith('.cs'), os.listdir(path))

def get_java_files(path):
    return filter(lambda f: f.endswith('.java'), os.listdir(path))

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
        if path == None:
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
    def find_file(self, fname, ownerfile):
        full_fname = os.path.join(self.src_dir, fname)
        if os.path.exists(full_fname):
            return self
        for dep in self.deps:
            c_dep = get_component(dep)
            full_fname = os.path.join(c_dep.src_dir, fname)
            if os.path.exists(full_fname):
                return c_dep
        raise MKException("Failed to find include file '%s' for '%s' when processing '%s'." % (fname, ownerfile, self.name))

    # Display all dependencies of file basename located in the given component directory.
    # The result is displayed at out
    def add_cpp_h_deps(self, out, basename):
        includes = extract_c_includes(os.path.join(self.src_dir, basename))
        out.write(os.path.join(self.to_src_dir, basename))
        for include in includes:
            owner = self.find_file(include, basename)
            out.write(' %s.node' % os.path.join(owner.build_dir, include))

    # Add a rule for each #include directive in the file basename located at the current component.
    def add_rule_for_each_include(self, out, basename):
        fullname = os.path.join(self.src_dir, basename)
        includes = extract_c_includes(fullname)
        for include in includes:
            owner = self.find_file(include, fullname)
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
        out.write('\n')
        mk_dir(os.path.join(BUILD_DIR, self.build_dir))
        if VS_PAR and IS_WINDOWS:
            cppfiles = list(get_cpp_files(self.src_dir))
            dependencies = set()
            for cppfile in cppfiles:
                dependencies.add(os.path.join(self.to_src_dir, cppfile))
                self.add_rule_for_each_include(out, cppfile)
                includes = extract_c_includes(os.path.join(self.src_dir, cppfile))
                for include in includes:
                    owner = self.find_file(include, cppfile)
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

    def mk_install_dep(self, out):
        out.write('%s' % libfile)

    def mk_install(self, out):
        for include in self.includes2install:
            out.write('\t@cp %s %s\n' % (os.path.join(self.to_src_dir, include), os.path.join('$(PREFIX)', 'include', include)))

    def mk_uninstall(self, out):
        for include in self.includes2install:
            out.write('\t@rm -f %s\n' % os.path.join('$(PREFIX)', 'include', include))

    def mk_win_dist(self, build_path, dist_path):
        mk_dir(os.path.join(dist_path, 'include'))
        for include in self.includes2install:
            shutil.copy(os.path.join(self.src_dir, include),
                        os.path.join(dist_path, 'include', include))

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
        if exe_name == None:
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
        out.write('\t$(LINK) $(LINK_OUT_FLAG)%s $(LINK_FLAGS)' % exefile)
        for obj in objs:
            out.write(' ')
            out.write(obj)
        for dep in deps:
            c_dep = get_component(dep)
            out.write(' ' + c_dep.get_link_name())
        out.write(' ' + FOCI2LIB)
        out.write(' $(LINK_EXTRA_FLAGS)\n')
        out.write('%s: %s\n\n' % (self.name, exefile))

    def require_install_tactics(self):
        return ('tactic' in self.deps) and ('cmd_context' in self.deps)

    def require_mem_initializer(self):
        return True

    # All executables (to be installed) are included in the all: rule
    def main_component(self):
        return self.install

    def mk_install_dep(self, out):
        out.write('%s' % exefile)

    def mk_install(self, out):
        if self.install:
            exefile = '%s$(EXE_EXT)' % self.exe_name
            out.write('\t@cp %s %s\n' % (exefile, os.path.join('$(PREFIX)', 'bin', exefile)))

    def mk_uninstall(self, out):
        exefile = '%s$(EXE_EXT)' % self.exe_name
        out.write('\t@rm -f %s\n' % os.path.join('$(PREFIX)', 'bin', exefile))

    def mk_win_dist(self, build_path, dist_path):
        if self.install:
            mk_dir(os.path.join(dist_path, 'bin'))
            shutil.copy('%s.exe' % os.path.join(build_path, self.exe_name),
                        '%s.exe' % os.path.join(dist_path, 'bin', self.exe_name))

    def mk_unix_dist(self, build_path, dist_path):
        if self.install:
            mk_dir(os.path.join(dist_path, 'bin'))
            shutil.copy(os.path.join(build_path, self.exe_name),
                        os.path.join(dist_path, 'bin', self.exe_name))


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
    elif sysname == 'Linux' or sysname == 'FreeBSD':
        return 'so'
    elif sysname == 'CYGWIN':
        return 'dll'
    else:
        assert(False)
        return 'dll'

class DLLComponent(Component):
    def __init__(self, name, dll_name, path, deps, export_files, reexports, install, static):
        Component.__init__(self, name, path, deps)
        if dll_name == None:
            dll_name = name
        self.dll_name = dll_name
        self.export_files = export_files
        self.reexports = reexports
        self.install = install
        self.static = static

    def get_link_name(self):
        if self.static:
            return os.path.join(self.build_dir, self.name) + '$(LIB_EXT)'
        else:
            return self.name + '$(SO_EXT)'

    def mk_makefile(self, out):
        Component.mk_makefile(self, out)
        # generate rule for (SO_EXT)
        dllfile = '%s$(SO_EXT)' % self.dll_name
        out.write('%s:' % dllfile)
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
            if not dep in self.reexports:
                c_dep = get_component(dep)
                out.write(' ' + c_dep.get_link_name())
        out.write('\n')
        out.write('\t$(LINK) $(SLINK_OUT_FLAG)%s $(SLINK_FLAGS)' % dllfile)
        for obj in objs:
            out.write(' ')
            out.write(obj)
        for dep in deps:
            if not dep in self.reexports:
                c_dep = get_component(dep)
                out.write(' ' + c_dep.get_link_name())
        out.write(' ' + FOCI2LIB)
        out.write(' $(SLINK_EXTRA_FLAGS)')
        if IS_WINDOWS:
            out.write(' /DEF:%s.def' % os.path.join(self.to_src_dir, self.name))
        out.write('\n')
        if self.static:
            self.mk_static(out)
            libfile = '%s$(LIB_EXT)' % self.dll_name
            out.write('%s: %s %s\n\n' % (self.name, dllfile, libfile))
        else:
            out.write('%s: %s\n\n' % (self.name, dllfile))

    def mk_static(self, out):
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
        libfile = '%s$(LIB_EXT)' % self.dll_name
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

    def mk_install_dep(self, out):
        out.write('%s$(SO_EXT)' % self.dll_name)
        if self.static:
            out.write(' %s$(LIB_EXT)' % self.dll_name)

    def mk_install(self, out):
        if self.install:
            dllfile = '%s$(SO_EXT)' % self.dll_name
            out.write('\t@cp %s %s\n' % (dllfile, os.path.join('$(PREFIX)', 'lib', dllfile)))
            out.write('\t@cp %s %s\n' % (dllfile, os.path.join(PYTHON_PACKAGE_DIR, dllfile)))
            if self.static:
                libfile = '%s$(LIB_EXT)' % self.dll_name
                out.write('\t@cp %s %s\n' % (libfile, os.path.join('$(PREFIX)', 'lib', libfile)))


    def mk_uninstall(self, out):
        dllfile = '%s$(SO_EXT)' % self.dll_name
        out.write('\t@rm -f %s\n' % os.path.join('$(PREFIX)', 'lib', dllfile))
        out.write('\t@rm -f %s\n' % os.path.join(PYTHON_PACKAGE_DIR, dllfile))
        libfile = '%s$(LIB_EXT)' % self.dll_name
        out.write('\t@rm -f %s\n' % os.path.join('$(PREFIX)', 'lib', libfile))

    def mk_win_dist(self, build_path, dist_path):
        if self.install:
            mk_dir(os.path.join(dist_path, 'bin'))
            shutil.copy('%s.dll' % os.path.join(build_path, self.dll_name),
                        '%s.dll' % os.path.join(dist_path, 'bin', self.dll_name))
            shutil.copy('%s.lib' % os.path.join(build_path, self.dll_name),
                        '%s.lib' % os.path.join(dist_path, 'bin', self.dll_name))

    def mk_unix_dist(self, build_path, dist_path):
        if self.install:
            mk_dir(os.path.join(dist_path, 'bin'))
            so = get_so_ext()
            shutil.copy('%s.%s' % (os.path.join(build_path, self.dll_name), so),
                        '%s.%s' % (os.path.join(dist_path, 'bin', self.dll_name), so))
            shutil.copy('%s.a' % os.path.join(build_path, self.dll_name),
                        '%s.a' % os.path.join(dist_path, 'bin', self.dll_name))

class DotNetDLLComponent(Component):
    def __init__(self, name, dll_name, path, deps, assembly_info_dir):
        Component.__init__(self, name, path, deps)
        if dll_name == None:
            dll_name = name
        if assembly_info_dir == None:
            assembly_info_dir = "."
        self.dll_name          = dll_name
        self.assembly_info_dir = assembly_info_dir

    def mk_makefile(self, out):
        if DOTNET_ENABLED:
            cs_fp_files = []
            cs_files    = []
            for cs_file in get_cs_files(self.src_dir):
                cs_fp_files.append(os.path.join(self.to_src_dir, cs_file))
                cs_files.append(cs_file)
            if self.assembly_info_dir != '.':
                for cs_file in get_cs_files(os.path.join(self.src_dir, self.assembly_info_dir)):
                    cs_fp_files.append(os.path.join(self.to_src_dir, self.assembly_info_dir, cs_file))
                    cs_files.append(os.path.join(self.assembly_info_dir, cs_file))
            dllfile = '%s.dll' % self.dll_name
            out.write('%s: %s$(SO_EXT)' % (dllfile, get_component(Z3_DLL_COMPONENT).dll_name))
            for cs_file in cs_fp_files:
                out.write(' ')
                out.write(cs_file)
            out.write('\n')
            out.write('  csc /noconfig /unsafe+ /nowarn:1701,1702 /nostdlib+ /errorreport:prompt /warn:4 /reference:mscorlib.dll /reference:System.Core.dll /reference:System.dll /reference:System.Numerics.dll /filealign:512 /linkresource:%s.dll /out:%s.dll /target:library /doc:%s.xml' % (get_component(Z3_DLL_COMPONENT).dll_name, self.dll_name, self.dll_name))
            if DEBUG_MODE:
                out.write(' /define:DEBUG;TRACE /debug+ /debug:full /optimize-')
            else:
                out.write(' /optimize+')
            if VS_X64:
                out.write(' /platform:x64')
            else:
                out.write(' /platform:x86')
            for cs_file in cs_files:
                out.write(' %s' % os.path.join(self.to_src_dir, cs_file))
            out.write('\n')
            out.write('%s: %s\n\n' % (self.name, dllfile))
            return

    def main_component(self):
        return DOTNET_ENABLED

    def has_assembly_info(self):
        return True

    def mk_win_dist(self, build_path, dist_path):
        if DOTNET_ENABLED:
            # Assuming all DotNET dll should be in the distribution
            mk_dir(os.path.join(dist_path, 'bin'))
            shutil.copy('%s.dll' % os.path.join(build_path, self.dll_name),
                        '%s.dll' % os.path.join(dist_path, 'bin', self.dll_name))
            shutil.copy('%s.xml' % os.path.join(build_path, self.dll_name),
                        '%s.xml' % os.path.join(dist_path, 'bin', self.dll_name))
            if DEBUG_MODE:
                shutil.copy('%s.pdb' % os.path.join(build_path, self.dll_name),
                            '%s.pdb' % os.path.join(dist_path, 'bin', self.dll_name))



    def mk_unix_dist(self, build_path, dist_path):
        # Do nothing
        return

class JavaDLLComponent(Component):
    def __init__(self, name, dll_name, package_name, manifest_file, path, deps):
        Component.__init__(self, name, path, deps)
        if dll_name == None:
            dll_name = name
        self.dll_name     = dll_name
        self.package_name = package_name
        self.manifest_file = manifest_file

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
            elif IS_LINUX:
                t = t.replace('PLATFORM', 'linux')
            elif IS_FREEBSD:
                t = t.replace('PLATFORM', 'freebsd')
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
            t = ('\t%s %s.java -d %s\n' % (JAVAC, os.path.join(self.to_src_dir, 'enumerations', '*'), os.path.join('api', 'java', 'classes')))
            out.write(t)
            t = ('\t%s -cp %s %s.java -d %s\n' % (JAVAC,
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
            mk_dir(os.path.join(dist_path, 'bin'))
            shutil.copy('%s.jar' % os.path.join(build_path, self.package_name),
                        '%s.jar' % os.path.join(dist_path, 'bin', self.package_name))
            shutil.copy(os.path.join(build_path, 'libz3java.dll'),
                        os.path.join(dist_path, 'bin', 'libz3java.dll'))
            shutil.copy(os.path.join(build_path, 'libz3java.lib'),
                        os.path.join(dist_path, 'bin', 'libz3java.lib'))

    def mk_unix_dist(self, build_path, dist_path):
        if JAVA_ENABLED:
            mk_dir(os.path.join(dist_path, 'bin'))
            shutil.copy('%s.jar' % os.path.join(build_path, self.package_name),
                        '%s.jar' % os.path.join(dist_path, 'bin', self.package_name))
            so = get_so_ext()
            shutil.copy(os.path.join(build_path, 'libz3java.%s' % so),
                        os.path.join(dist_path, 'bin', 'libz3java.%s' % so))

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
        exefile = '%s$(EXE_EXT)' % self.name
        out.write('%s: %s' % (exefile, dll))
        for cppfile in self.src_files():
            out.write(' ')
            out.write(os.path.join(self.to_ex_dir, cppfile))
        out.write('\n')
        out.write('\t%s $(OS_DEFINES) $(EXAMP_DEBUG_FLAG) $(LINK_OUT_FLAG)%s $(LINK_FLAGS)' % (self.compiler(), exefile))
        # Add include dir components
        out.write(' -I%s' % get_component(API_COMPONENT).to_src_dir)
        out.write(' -I%s' % get_component(CPP_COMPONENT).to_src_dir)
        for cppfile in self.src_files():
            out.write(' ')
            out.write(os.path.join(self.to_ex_dir, cppfile))
        out.write(' ')
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

class DotNetExampleComponent(ExampleComponent):
    def __init__(self, name, path):
        ExampleComponent.__init__(self, name, path)

    def is_example(self):
        return IS_WINDOWS

    def mk_makefile(self, out):
        if DOTNET_ENABLED:
            dll_name = get_component(DOTNET_COMPONENT).dll_name
            dll = '%s.dll' % dll_name
            exefile = '%s$(EXE_EXT)' % self.name
            out.write('%s: %s' % (exefile, dll))
            for csfile in get_cs_files(self.ex_dir):
                out.write(' ')
                out.write(os.path.join(self.to_ex_dir, csfile))
            out.write('\n')
            out.write('\tcsc /out:%s /reference:%s /debug:full /reference:System.Numerics.dll' % (exefile, dll))
            if VS_X64:
                out.write(' /platform:x64')
            else:
                out.write(' /platform:x86')
            for csfile in get_cs_files(self.ex_dir):
                out.write(' ')
                # HACK
                win_ex_dir = self.to_ex_dir.replace('/', '\\')
                out.write(os.path.join(win_ex_dir, csfile))
            out.write('\n')
            out.write('_ex_%s: %s\n\n' % (self.name, exefile))

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

class PythonExampleComponent(ExampleComponent):
    def __init__(self, name, path):
        ExampleComponent.__init__(self, name, path)

    # Python examples are just placeholders, we just copy the *.py files when mk_makefile is invoked.
    # We don't need to include them in the :examples rule
    def mk_makefile(self, out):
        full = os.path.join(EXAMPLE_DIR, self.path)
        for py in filter(lambda f: f.endswith('.py'), os.listdir(full)):
            shutil.copyfile(os.path.join(full, py), os.path.join(BUILD_DIR, py))
            if is_verbose():
                print("Copied Z3Py example '%s' to '%s'" % (py, BUILD_DIR))
        out.write('_ex_%s: \n\n' % self.name)


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

def add_hlib(name, path=None, includes2install=[]):
    c = HLibComponent(name, path, includes2install)
    reg_component(name, c)

def add_exe(name, deps=[], path=None, exe_name=None, install=True):
    c = ExeComponent(name, exe_name, path, deps, install)
    reg_component(name, c)

def add_extra_exe(name, deps=[], path=None, exe_name=None, install=True):
    c = ExtraExeComponent(name, exe_name, path, deps, install)
    reg_component(name, c)

def add_dll(name, deps=[], path=None, dll_name=None, export_files=[], reexports=[], install=True, static=False):
    c = DLLComponent(name, dll_name, path, deps, export_files, reexports, install, static)
    reg_component(name, c)

def add_dot_net_dll(name, deps=[], path=None, dll_name=None, assembly_info_dir=None):
    c = DotNetDLLComponent(name, dll_name, path, deps, assembly_info_dir)
    reg_component(name, c)

def add_java_dll(name, deps=[], path=None, dll_name=None, package_name=None, manifest_file=None):
    c = JavaDLLComponent(name, dll_name, package_name, manifest_file, path, deps)
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

def add_z3py_example(name, path=None):
    c = PythonExampleComponent(name, path)
    reg_component(name, c)

def mk_config():
    if ONLY_MAKEFILES:
        return
    config = open(os.path.join(BUILD_DIR, 'config.mk'), 'w')
    if IS_WINDOWS:
        config.write(
            'CC=cl\n'
            'CXX=cl\n'
            'CXX_OUT_FLAG=/Fo\n'
            'OBJ_EXT=.obj\n'
            'LIB_EXT=.lib\n'
            'AR=lib\n'
            'AR_FLAGS=/nologo\n'
            'AR_OUTFLAG=/OUT:\n'
            'EXE_EXT=.exe\n'
            'LINK=cl\n'
            'LINK_OUT_FLAG=/Fe\n'
            'SO_EXT=.dll\n'
            'SLINK=cl\n'
            'SLINK_OUT_FLAG=/Fe\n'
            'OS_DEFINES=/D _WINDOWS\n')
        extra_opt = ''
        if GIT_HASH:
            extra_opt = '%s /D Z3GITHASH=%s' % (extra_opt, GIT_HASH)
        if DEBUG_MODE:
            config.write(
                'LINK_FLAGS=/nologo /MDd\n'
                'SLINK_FLAGS=/nologo /LDd\n')
            if not VS_X64:
                config.write(
                    'CXXFLAGS=/c /Zi /nologo /openmp /W3 /WX- /Od /Oy- /D WIN32 /D _DEBUG /D Z3DEBUG %s /D _CONSOLE /D _TRACE /D _WINDOWS /Gm- /EHsc /RTC1 /MDd /GS /fp:precise /Zc:wchar_t /Zc:forScope /Gd /analyze- /arch:SSE2\n' % extra_opt)
                config.write(
                    'LINK_EXTRA_FLAGS=/link /DEBUG /MACHINE:X86 /SUBSYSTEM:CONSOLE /INCREMENTAL:NO /STACK:8388608 /OPT:REF /OPT:ICF /TLBID:1 /DYNAMICBASE /NXCOMPAT\n'
                    'SLINK_EXTRA_FLAGS=/link /DEBUG /MACHINE:X86 /SUBSYSTEM:WINDOWS /INCREMENTAL:NO /STACK:8388608 /OPT:REF /OPT:ICF /TLBID:1 /DYNAMICBASE:NO\n')
            else:
                config.write(
                    'CXXFLAGS=/c /Zi /nologo /openmp /W3 /WX- /Od /Oy- /D WIN32 /D _AMD64_ /D _DEBUG /D Z3DEBUG %s /D _CONSOLE /D _TRACE /D _WINDOWS /Gm- /EHsc /RTC1 /MDd /GS /fp:precise /Zc:wchar_t /Zc:forScope /Gd /analyze-\n' % extra_opt)
                config.write(
                    'LINK_EXTRA_FLAGS=/link /DEBUG /MACHINE:X64 /SUBSYSTEM:CONSOLE /INCREMENTAL:NO /STACK:8388608 /OPT:REF /OPT:ICF /TLBID:1 /DYNAMICBASE /NXCOMPAT\n'
                    'SLINK_EXTRA_FLAGS=/link /DEBUG /MACHINE:X64 /SUBSYSTEM:WINDOWS /INCREMENTAL:NO /STACK:8388608 /OPT:REF /OPT:ICF /TLBID:1 /DYNAMICBASE:NO\n')
        else:
            # Windows Release mode
            config.write(
                'LINK_FLAGS=/nologo /MD\n'
                'SLINK_FLAGS=/nologo /LD\n')
            if TRACE:
                extra_opt = '%s /D _TRACE' % extra_opt
            if not VS_X64:
                config.write(
                    'CXXFLAGS=/nologo /c /Zi /openmp /W3 /WX- /O2 /Oy- /D _EXTERNAL_RELEASE /D WIN32 /D NDEBUG %s /D _CONSOLE /D _WINDOWS /D ASYNC_COMMANDS /Gm- /EHsc /MD /GS /fp:precise /Zc:wchar_t /Zc:forScope /Gd /analyze- /arch:SSE2\n' % extra_opt)
                config.write(
                    'LINK_EXTRA_FLAGS=/link /DEBUG /MACHINE:X86 /SUBSYSTEM:CONSOLE /INCREMENTAL:NO /STACK:8388608 /OPT:REF /OPT:ICF /TLBID:1 /DYNAMICBASE /NXCOMPAT\n'
                    'SLINK_EXTRA_FLAGS=/link /DEBUG /MACHINE:X86 /SUBSYSTEM:WINDOWS /INCREMENTAL:NO /STACK:8388608 /OPT:REF /OPT:ICF /TLBID:1 /DYNAMICBASE:NO\n')
            else:
                config.write(
                    'CXXFLAGS=/c /Zi /nologo /openmp /W3 /WX- /O2 /D _EXTERNAL_RELEASE /D WIN32 /D NDEBUG %s /D _LIB /D _WINDOWS /D _AMD64_ /D _UNICODE /D UNICODE /Gm- /EHsc /MD /GS /fp:precise /Zc:wchar_t /Zc:forScope /Gd /TP\n' % extra_opt)
                config.write(
                    'LINK_EXTRA_FLAGS=/link /MACHINE:X64 /SUBSYSTEM:CONSOLE /INCREMENTAL:NO /STACK:8388608\n'
                    'SLINK_EXTRA_FLAGS=/link /MACHINE:X64 /SUBSYSTEM:WINDOWS /INCREMENTAL:NO /STACK:8388608\n')

        # End of Windows VS config.mk
        if is_verbose():
            print('64-bit:         %s' % is64())
            if is_java_enabled():
                print('JNI Bindings:   %s' % JNI_HOME)
                print('Java Compiler:  %s' % JAVAC)
    else:
        global CXX, CC, GMP, FOCI2, CPPFLAGS, CXXFLAGS, LDFLAGS, EXAMP_DEBUG_FLAG
        OS_DEFINES = ""
        ARITH = "internal"
        check_ar()
        CXX = find_cxx_compiler()
        CC  = find_c_compiler()
        SLIBEXTRAFLAGS = ''
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
        if FOCI2:
            if test_foci2(CXX,FOCI2LIB):
                LDFLAGS  = '%s %s' % (LDFLAGS,FOCI2LIB)
                SLIBEXTRAFLAGS = '%s %s' % (SLIBEXTRAFLAGS,FOCI2LIB)
                CPPFLAGS = '%s -D_FOCI2' % CPPFLAGS
            else:
                print("FAILED\n")
                FOCI2 = False
        if GIT_HASH:
            CPPFLAGS = '%s -DZ3GITHASH=%s' % (CPPFLAGS, GIT_HASH)
        CXXFLAGS = '%s -c' % CXXFLAGS
        HAS_OMP = test_openmp(CXX)
        if HAS_OMP:
            CXXFLAGS = '%s -fopenmp -mfpmath=sse' % CXXFLAGS
            LDFLAGS  = '%s -fopenmp' % LDFLAGS
            SLIBEXTRAFLAGS = '%s -fopenmp' % SLIBEXTRAFLAGS
        else:
            CXXFLAGS = '%s -D_NO_OMP_' % CXXFLAGS
        if DEBUG_MODE:
            CXXFLAGS     = '%s -g -Wall' % CXXFLAGS
            EXAMP_DEBUG_FLAG = '-g'
        else:
            if GPROF:
                CXXFLAGS     = '%s -O3 -D _EXTERNAL_RELEASE' % CXXFLAGS
            else:
                CXXFLAGS     = '%s -O3 -D _EXTERNAL_RELEASE -fomit-frame-pointer' % CXXFLAGS
        if is_CXX_clangpp():
            CXXFLAGS   = '%s -Wno-unknown-pragmas -Wno-overloaded-virtual -Wno-unused-value' % CXXFLAGS
        sysname = os.uname()[0]
        if sysname == 'Darwin':
            SO_EXT    = '.dylib'
            SLIBFLAGS = '-dynamiclib'
        elif sysname == 'Linux':
            CXXFLAGS       = '%s -fno-strict-aliasing -D_LINUX_' % CXXFLAGS
            OS_DEFINES     = '-D_LINUX'
            SO_EXT         = '.so'
            LDFLAGS        = '%s -lrt' % LDFLAGS
            SLIBFLAGS      = '-shared'
            SLIBEXTRAFLAGS = '%s -lrt' % SLIBEXTRAFLAGS
        elif sysname == 'FreeBSD':
            CXXFLAGS       = '%s -fno-strict-aliasing -D_FREEBSD_' % CXXFLAGS
            OS_DEFINES     = '-D_FREEBSD_'
            SO_EXT         = '.so'
            LDFLAGS        = '%s -lrt' % LDFLAGS
            SLIBFLAGS      = '-shared'
            SLIBEXTRAFLAGS = '%s -lrt' % SLIBEXTRAFLAGS
        elif sysname[:6] ==  'CYGWIN':
            CXXFLAGS    = '%s -D_CYGWIN -fno-strict-aliasing' % CXXFLAGS
            OS_DEFINES     = '-D_CYGWIN'
            SO_EXT      = '.dll'
            SLIBFLAGS   = '-shared'
        else:
            raise MKException('Unsupported platform: %s' % sysname)
        if is64():
            CXXFLAGS     = '%s -fPIC' % CXXFLAGS
            CPPFLAGS     = '%s -D_AMD64_' % CPPFLAGS
            if sysname == 'Linux':
                CPPFLAGS = '%s -D_USE_THREAD_LOCAL' % CPPFLAGS
        if DEBUG_MODE:
            CPPFLAGS     = '%s -DZ3DEBUG' % CPPFLAGS
        if TRACE or DEBUG_MODE:
            CPPFLAGS     = '%s -D_TRACE' % CPPFLAGS
        CXXFLAGS         = '%s -msse -msse2' % CXXFLAGS
        config.write('PREFIX=%s\n' % PREFIX)
        config.write('CC=%s\n' % CC)
        config.write('CXX=%s\n' % CXX)
        config.write('CXXFLAGS=%s %s\n' % (CPPFLAGS, CXXFLAGS))
        config.write('EXAMP_DEBUG_FLAG=%s\n' % EXAMP_DEBUG_FLAG)
        config.write('CXX_OUT_FLAG=-o \n')
        config.write('OBJ_EXT=.o\n')
        config.write('LIB_EXT=.a\n')
        config.write('AR=ar\n')
        config.write('AR_FLAGS=rcs\n')
        config.write('AR_OUTFLAG=\n')
        config.write('EXE_EXT=\n')
        config.write('LINK=%s\n' % CXX)
        config.write('LINK_FLAGS=\n')
        config.write('LINK_OUT_FLAG=-o \n')
        config.write('LINK_EXTRA_FLAGS=-lpthread %s\n' % LDFLAGS)
        config.write('SO_EXT=%s\n' % SO_EXT)
        config.write('SLINK=%s\n' % CXX)
        config.write('SLINK_FLAGS=%s\n' % SLIBFLAGS)
        config.write('SLINK_EXTRA_FLAGS=%s\n' % SLIBEXTRAFLAGS)
        config.write('SLINK_OUT_FLAG=-o \n')
        config.write('OS_DEFINES=%s\n' % OS_DEFINES)
        if is_verbose():
            print('Host platform:  %s' % sysname)
            print('C++ Compiler:   %s' % CXX)
            print('C Compiler  :   %s' % CC)
            print('Arithmetic:     %s' % ARITH)
            print('OpenMP:         %s' % HAS_OMP)
            print('Prefix:         %s' % PREFIX)
            print('64-bit:         %s' % is64())
            if GPROF:
                print('gprof:          enabled')
            print('Python version: %s' % distutils.sysconfig.get_python_version())
            if is_java_enabled():
                print('JNI Bindings:   %s' % JNI_HOME)
                print('Java Compiler:  %s' % JAVAC)

def mk_install(out):
    out.write('install: ')
    for c in get_components():
        c.mk_install_deps(out)
        out.write(' ')
    out.write('\n')
    out.write('\t@mkdir -p %s\n' % os.path.join('$(PREFIX)', 'bin'))
    out.write('\t@mkdir -p %s\n' % os.path.join('$(PREFIX)', 'include'))
    out.write('\t@mkdir -p %s\n' % os.path.join('$(PREFIX)', 'lib'))
    for c in get_components():
        c.mk_install(out)
    out.write('\t@cp z3*.py %s\n' % PYTHON_PACKAGE_DIR)
    if sys.version >= "3":
        out.write('\t@cp %s*.pyc %s\n' % (os.path.join('__pycache__', 'z3'),
                                          os.path.join(PYTHON_PACKAGE_DIR, '__pycache__')))
    else:
        out.write('\t@cp z3*.pyc %s\n' % PYTHON_PACKAGE_DIR)
    out.write('\t@echo Z3 was successfully installed.\n')
    if PYTHON_PACKAGE_DIR != distutils.sysconfig.get_python_lib():
        if os.uname()[0] == 'Darwin':
            LD_LIBRARY_PATH = "DYLD_LIBRARY_PATH"
        else:
            LD_LIBRARY_PATH = "LD_LIBRARY_PATH"
        out.write('\t@echo Z3 shared libraries were installed at \'%s\', make sure this directory is in your %s environment variable.\n' %
                  (os.path.join(PREFIX, 'lib'), LD_LIBRARY_PATH))
        out.write('\t@echo Z3Py was installed at \'%s\', make sure this directory is in your PYTHONPATH environment variable.' % PYTHON_PACKAGE_DIR)
    out.write('\n')

def mk_uninstall(out):
    out.write('uninstall:\n')
    for c in get_components():
        c.mk_uninstall(out)
    out.write('\t@rm -f %s*.py\n' % os.path.join(PYTHON_PACKAGE_DIR, 'z3'))
    out.write('\t@rm -f %s*.pyc\n' % os.path.join(PYTHON_PACKAGE_DIR, 'z3'))
    out.write('\t@rm -f %s*.pyc\n' % os.path.join(PYTHON_PACKAGE_DIR, '__pycache__', 'z3'))
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
    out.write("\t@echo \"Z3Py scripts can already be executed in the \'%s\' directory.\"\n" % BUILD_DIR)
    out.write("\t@echo \"Z3Py scripts stored in arbitrary directories can be also executed if \'%s\' directory is added to the PYTHONPATH environment variable.\"\n" % BUILD_DIR)
    if not IS_WINDOWS:
        out.write("\t@echo Use the following command to install Z3 at prefix $(PREFIX).\n")
        out.write('\t@echo "    sudo make install"\n')
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
    # Finalize
    if VERBOSE:
        print("Makefile was successfully generated.")
        if not IS_WINDOWS:
            print("  python packages dir: %s" % PYTHON_PACKAGE_DIR)
        if DEBUG_MODE:
            print("  compilation mode: Debug")
        else:
            print("  compilation mode: Release")
        if IS_WINDOWS:
            if VS_X64:
                print("  platform: x64\n")
                print("To build Z3, open a [Visual Studio x64 Command Prompt], then")
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

UINT   = 0
BOOL   = 1
DOUBLE = 2
STRING = 3
SYMBOL = 4
UINT_MAX = 4294967295
CURR_PYG = None

def get_curr_pyg():
    return CURR_PYG

TYPE2CPK = { UINT : 'CPK_UINT', BOOL : 'CPK_BOOL',  DOUBLE : 'CPK_DOUBLE',  STRING : 'CPK_STRING',  SYMBOL : 'CPK_SYMBOL' }
TYPE2CTYPE = { UINT : 'unsigned', BOOL : 'bool', DOUBLE : 'double', STRING : 'char const *', SYMBOL : 'symbol' }
TYPE2GETTER = { UINT : 'get_uint', BOOL : 'get_bool', DOUBLE : 'get_double', STRING : 'get_str',  SYMBOL : 'get_sym' }

def pyg_default(p):
    if p[1] == BOOL:
        if p[2]:
            return "true"
        else:
            return "false"
    return p[2]

def pyg_default_as_c_literal(p):
    if p[1] == BOOL:
        if p[2]:
            return "true"
        else:
            return "false"
    elif p[1] == STRING:
        return '"%s"' % p[2]
    elif p[1] == SYMBOL:
        return 'symbol("%s")' % p[2]
    elif p[1] == UINT:
        return '%su' % p[2]
    else:
        return p[2]

def to_c_method(s):
    return s.replace('.', '_')

def def_module_params(module_name, export, params, class_name=None, description=None):
    pyg = get_curr_pyg()
    dirname = os.path.split(get_curr_pyg())[0]
    if class_name == None:
        class_name = '%s_params' % module_name
    hpp = os.path.join(dirname, '%s.hpp' % class_name)
    out = open(hpp, 'w')
    out.write('// Automatically generated file\n')
    out.write('#ifndef __%s_HPP_\n' % class_name.upper())
    out.write('#define __%s_HPP_\n' % class_name.upper())
    out.write('#include"params.h"\n')
    if export:
        out.write('#include"gparams.h"\n')
    out.write('struct %s {\n' % class_name)
    out.write('  params_ref const & p;\n')
    if export:
        out.write('  params_ref g;\n')
    out.write('  %s(params_ref const & _p = params_ref::get_empty()):\n' % class_name)
    out.write('     p(_p)')
    if export:
        out.write(', g(gparams::get_module("%s"))' % module_name)
    out.write(' {}\n')
    out.write('  static void collect_param_descrs(param_descrs & d) {\n')
    for param in params:
        out.write('    d.insert("%s", %s, "%s", "%s","%s");\n' % (param[0], TYPE2CPK[param[1]], param[3], pyg_default(param), module_name))
    out.write('  }\n')
    if export:
        out.write('  /*\n')
        out.write("     REG_MODULE_PARAMS('%s', '%s::collect_param_descrs')\n" % (module_name, class_name))
        if description != None:
            out.write("     REG_MODULE_DESCRIPTION('%s', '%s')\n" % (module_name, description))
        out.write('  */\n')
    # Generated accessors
    for param in params:
        if export:
            out.write('  %s %s() const { return p.%s("%s", g, %s); }\n' %
                      (TYPE2CTYPE[param[1]], to_c_method(param[0]), TYPE2GETTER[param[1]], param[0], pyg_default_as_c_literal(param)))
        else:
            out.write('  %s %s() const { return p.%s("%s", %s); }\n' %
                      (TYPE2CTYPE[param[1]], to_c_method(param[0]), TYPE2GETTER[param[1]], param[0], pyg_default_as_c_literal(param)))
    out.write('};\n')
    out.write('#endif\n')
    if is_verbose():
        print("Generated '%s'" % hpp)

def max_memory_param():
    return ('max_memory', UINT, UINT_MAX, 'maximum amount of memory in megabytes')

def max_steps_param():
    return ('max_steps', UINT, UINT_MAX, 'maximum number of steps')

PYG_GLOBALS = { 'UINT' : UINT, 'BOOL' : BOOL, 'DOUBLE' : DOUBLE, 'STRING' : STRING, 'SYMBOL' : SYMBOL,
                'UINT_MAX' : UINT_MAX,
                'max_memory_param' : max_memory_param,
                'max_steps_param' : max_steps_param,
                'def_module_params' : def_module_params }

def _execfile(file, globals=globals(), locals=locals()):
    if sys.version < "2.7":
        execfile(file, globals, locals)
    else:
        with open(file, "r") as fh:
            exec(fh.read()+"\n", globals, locals)

# Execute python auxiliary scripts that generate extra code for Z3.
def exec_pyg_scripts():
    global CURR_PYG
    for root, dirs, files in os.walk('src'):
        for f in files:
            if f.endswith('.pyg'):
                script = os.path.join(root, f)
                CURR_PYG = script
                _execfile(script, PYG_GLOBALS)

# TODO: delete after src/ast/pattern/expr_pattern_match
# database.smt ==> database.h
def mk_pat_db():
    c = get_component(PATTERN_COMPONENT)
    fin  = open(os.path.join(c.src_dir, 'database.smt2'), 'r')
    fout = open(os.path.join(c.src_dir, 'database.h'), 'w')
    fout.write('char const * g_pattern_database =\n')
    for line in fin:
        fout.write('"%s\\n"\n' % line.strip('\n'))
    fout.write(';\n')
    if VERBOSE:
        print("Generated '%s'" % os.path.join(c.src_dir, 'database.h'))

# Update version numbers
def update_version():
    major = VER_MAJOR
    minor = VER_MINOR
    build = VER_BUILD
    revision = VER_REVISION
    if major == None or minor == None or build == None or revision == None:
        raise MKException("set_version(major, minor, build, revision) must be used before invoking update_version()")
    if not ONLY_MAKEFILES:
        mk_version_dot_h(major, minor, build, revision)
        mk_all_assembly_infos(major, minor, build, revision)
        mk_def_files()

# Update files with the version number
def mk_version_dot_h(major, minor, build, revision):
    c = get_component(UTIL_COMPONENT)
    fout = open(os.path.join(c.src_dir, 'version.h'), 'w')
    fout.write('// automatically generated file.\n')
    fout.write('#define Z3_MAJOR_VERSION   %s\n' % major)
    fout.write('#define Z3_MINOR_VERSION   %s\n' % minor)
    fout.write('#define Z3_BUILD_NUMBER    %s\n' % build)
    fout.write('#define Z3_REVISION_NUMBER %s\n' % revision)
    if VERBOSE:
        print("Generated '%s'" % os.path.join(c.src_dir, 'version.h'))

# Generate AssemblyInfo.cs files with the right version numbers by using AssemblyInfo files as a template
def mk_all_assembly_infos(major, minor, build, revision):
    for c in get_components():
        if c.has_assembly_info():
            assembly = os.path.join(c.src_dir, c.assembly_info_dir, 'AssemblyInfo')
            if os.path.exists(assembly):
                # It is a CS file
                mk_assembly_info_version(assembly, major, minor, build, revision)
            else:
                raise MKException("Failed to find assembly info file 'AssemblyInfo' at '%s'" % os.path.join(c.src_dir, c.assembly_info_dir))


# Generate version number in the given 'AssemblyInfo.cs' file using 'AssemblyInfo' as a template.
def mk_assembly_info_version(assemblyinfo, major, minor, build, revision):
    ver_pat   = re.compile('[assembly: AssemblyVersion\("[\.\d]*"\) *')
    fver_pat  = re.compile('[assembly: AssemblyFileVersion\("[\.\d]*"\) *')
    fin  = open(assemblyinfo, 'r')
    tmp  = '%s.cs' % assemblyinfo
    fout = open(tmp, 'w')
    num_updates = 0
    for line in fin:
        if ver_pat.match(line):
            fout.write('[assembly: AssemblyVersion("%s.%s.%s.%s")]\n' % (major, minor, build, revision))
            num_updates = num_updates + 1
        elif fver_pat.match(line):
            fout.write('[assembly: AssemblyFileVersion("%s.%s.%s.%s")]\n' % (major, minor, build, revision))
            num_updates = num_updates + 1
        else:
            fout.write(line)
    # if VERBOSE:
    #    print("%s version numbers updated at '%s'" % (num_updates, assemblyinfo))
    assert num_updates == 2, "unexpected number of version number updates"
    fin.close()
    fout.close()
    if VERBOSE:
        print("Updated '%s'" % assemblyinfo)

ADD_TACTIC_DATA=[]
ADD_PROBE_DATA=[]

def ADD_TACTIC(name, descr, cmd):
    global ADD_TACTIC_DATA
    ADD_TACTIC_DATA.append((name, descr, cmd))

def ADD_PROBE(name, descr, cmd):
    global ADD_PROBE_DATA
    ADD_PROBE_DATA.append((name, descr, cmd))

# Generate an install_tactics.cpp at path.
# This file implements the procedure
#    void install_tactics(tactic_manager & ctx)
# It installs all tactics in the given component (name) list cnames
# The procedure looks for ADD_TACTIC commands in the .h files of these components.
def mk_install_tactic_cpp(cnames, path):
    global ADD_TACTIC_DATA, ADD_PROBE_DATA
    ADD_TACTIC_DATA = []
    ADD_PROBE_DATA = []
    fullname = os.path.join(path, 'install_tactic.cpp')
    fout  = open(fullname, 'w')
    fout.write('// Automatically generated file.\n')
    fout.write('#include"tactic.h"\n')
    fout.write('#include"tactic_cmds.h"\n')
    fout.write('#include"cmd_context.h"\n')
    tactic_pat   = re.compile('[ \t]*ADD_TACTIC\(.*\)')
    probe_pat    = re.compile('[ \t]*ADD_PROBE\(.*\)')
    for cname in cnames:
        c = get_component(cname)
        h_files = filter(lambda f: f.endswith('.h') or f.endswith('.hpp'), os.listdir(c.src_dir))
        for h_file in h_files:
            added_include = False
            fin = open(os.path.join(c.src_dir, h_file), 'r')
            for line in fin:
                if tactic_pat.match(line):
                    if not added_include:
                        added_include = True
                        fout.write('#include"%s"\n' % h_file)
                    try:
                        exec(line.strip('\n '), globals())
                    except:
                        raise MKException("Failed processing ADD_TACTIC command at '%s'\n%s" % (fullname, line))
                if probe_pat.match(line):
                    if not added_include:
                        added_include = True
                        fout.write('#include"%s"\n' % h_file)
                    try:
                        exec(line.strip('\n '), globals())
                    except:
                        raise MKException("Failed processing ADD_PROBE command at '%s'\n%s" % (fullname, line))
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
    if VERBOSE:
        print("Generated '%s'" % fullname)

def mk_all_install_tactic_cpps():
    if not ONLY_MAKEFILES:
        for c in get_components():
            if c.require_install_tactics():
                cnames = []
                cnames.extend(c.deps)
                cnames.append(c.name)
                mk_install_tactic_cpp(cnames, c.src_dir)

# Generate an mem_initializer.cpp at path.
# This file implements the procedures
#    void mem_initialize()
#    void mem_finalize()
# These procedures are invoked by the Z3 memory_manager
def mk_mem_initializer_cpp(cnames, path):
    initializer_cmds = []
    finalizer_cmds   = []
    fullname = os.path.join(path, 'mem_initializer.cpp')
    fout  = open(fullname, 'w')
    fout.write('// Automatically generated file.\n')
    initializer_pat      = re.compile('[ \t]*ADD_INITIALIZER\(\'([^\']*)\'\)')
    # ADD_INITIALIZER with priority
    initializer_prio_pat = re.compile('[ \t]*ADD_INITIALIZER\(\'([^\']*)\',[ \t]*(-?[0-9]*)\)')
    finalizer_pat        = re.compile('[ \t]*ADD_FINALIZER\(\'([^\']*)\'\)')
    for cname in cnames:
        c = get_component(cname)
        h_files = filter(lambda f: f.endswith('.h') or f.endswith('.hpp'), os.listdir(c.src_dir))
        for h_file in h_files:
            added_include = False
            fin = open(os.path.join(c.src_dir, h_file), 'r')
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
    if VERBOSE:
        print("Generated '%s'" % fullname)

def mk_all_mem_initializer_cpps():
    if not ONLY_MAKEFILES:
        for c in get_components():
            if c.require_mem_initializer():
                cnames = []
                cnames.extend(c.deps)
                cnames.append(c.name)
                mk_mem_initializer_cpp(cnames, c.src_dir)

# Generate an mem_initializer.cpp at path.
# This file implements the procedure
#    void gparams_register_modules()
# This procedure is invoked by gparams::init()
def mk_gparams_register_modules(cnames, path):
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
    for cname in cnames:
        c = get_component(cname)
        h_files = filter(lambda f: f.endswith('.h') or f.endswith('.hpp'), os.listdir(c.src_dir))
        for h_file in h_files:
            added_include = False
            fin = open(os.path.join(c.src_dir, h_file), 'r')
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
    fout.write('void gparams_register_modules() {\n')
    for code in cmds:
        fout.write('{ param_descrs d; %s(d); gparams::register_global(d); }\n' % code)
    for (mod, code) in mod_cmds:
        fout.write('{ param_descrs * d = alloc(param_descrs); %s(*d); gparams::register_module("%s", d); }\n' % (code, mod))
    for (mod, descr) in mod_descrs:
        fout.write('gparams::register_module_descr("%s", "%s");\n' % (mod, descr))
    fout.write('}\n')
    if VERBOSE:
        print("Generated '%s'" % fullname)

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
    pat1 = re.compile(".*Z3_API.*")
    defname = '%s.def' % os.path.join(c.src_dir, c.name)
    fout = open(defname, 'w')
    fout.write('LIBRARY "%s"\nEXPORTS\n' % c.dll_name)
    num = 1
    for dot_h in c.export_files:
        dot_h_c = c.find_file(dot_h, c.name)
        api = open(os.path.join(dot_h_c.src_dir, dot_h), 'r')
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
    if VERBOSE:
        print("Generated '%s'" % defname)

def mk_def_files():
    if not ONLY_MAKEFILES:
        for c in get_components():
            if c.require_def_file():
                mk_def_file(c)

def cp_z3py_to_build():
    mk_dir(BUILD_DIR)
    # Erase existing .pyc files
    for root, dirs, files in os.walk(Z3PY_SRC_DIR):
        for f in files:
            if f.endswith('.pyc'):
                rmf(os.path.join(root, f))
    # Compile Z3Py files
    if compileall.compile_dir(Z3PY_SRC_DIR, force=1) != 1:
        raise MKException("failed to compile Z3Py sources")
    # Copy sources to build
    for py in filter(lambda f: f.endswith('.py'), os.listdir(Z3PY_SRC_DIR)):
        shutil.copyfile(os.path.join(Z3PY_SRC_DIR, py), os.path.join(BUILD_DIR, py))
        if is_verbose():
            print("Copied '%s'" % py)
    # Python 2.x support
    for pyc in filter(lambda f: f.endswith('.pyc'), os.listdir(Z3PY_SRC_DIR)):
        shutil.copyfile(os.path.join(Z3PY_SRC_DIR, pyc), os.path.join(BUILD_DIR, pyc))
        if is_verbose():
            print("Generated '%s'" % pyc)
    # Python 3.x support
    src_pycache = os.path.join(Z3PY_SRC_DIR, '__pycache__')
    if os.path.exists(src_pycache):
        for pyc in filter(lambda f: f.endswith('.pyc'), os.listdir(src_pycache)):
            target_pycache = os.path.join(BUILD_DIR, '__pycache__')
            mk_dir(target_pycache)
            shutil.copyfile(os.path.join(src_pycache, pyc), os.path.join(target_pycache, pyc))
            if is_verbose():
                print("Generated '%s'" % pyc)

def mk_bindings(api_files):
    if not ONLY_MAKEFILES:
        mk_z3consts_py(api_files)
        mk_z3consts_dotnet(api_files)
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
        _execfile(os.path.join('scripts', 'update_api.py'), g) # HACK
        cp_z3py_to_build()

# Extract enumeration types from API files, and add python definitions.
def mk_z3consts_py(api_files):
    if Z3PY_SRC_DIR == None:
        raise MKException("You must invoke set_z3py_dir(path):")

    blank_pat      = re.compile("^ *$")
    comment_pat    = re.compile("^ *//.*$")
    typedef_pat    = re.compile("typedef enum *")
    typedef2_pat   = re.compile("typedef enum { *")
    openbrace_pat  = re.compile("{ *")
    closebrace_pat = re.compile("}.*;")

    z3consts  = open(os.path.join(Z3PY_SRC_DIR, 'z3consts.py'), 'w')
    z3consts.write('# Automatically generated file\n\n')

    api_dll = get_component(Z3_DLL_COMPONENT)

    for api_file in api_files:
        api_file_c = api_dll.find_file(api_file, api_dll.name)
        api_file   = os.path.join(api_file_c.src_dir, api_file)
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
                else:
                    if words[2] != '':
                        if len(words[2]) > 1 and words[2][1] == 'x':
                            idx = int(words[2], 16)
                        else:
                            idx = int(words[2])
                    decls[words[1]] = idx
                    idx = idx + 1
            linenum = linenum + 1
    if VERBOSE:
        print("Generated '%s'" % os.path.join(Z3PY_SRC_DIR, 'z3consts.py'))


# Extract enumeration types from z3_api.h, and add .Net definitions
def mk_z3consts_dotnet(api_files):
    blank_pat      = re.compile("^ *$")
    comment_pat    = re.compile("^ *//.*$")
    typedef_pat    = re.compile("typedef enum *")
    typedef2_pat   = re.compile("typedef enum { *")
    openbrace_pat  = re.compile("{ *")
    closebrace_pat = re.compile("}.*;")

    dotnet = get_component(DOTNET_COMPONENT)

    DeprecatedEnums = [ 'Z3_search_failure' ]
    z3consts  = open(os.path.join(dotnet.src_dir, 'Enumerations.cs'), 'w')
    z3consts.write('// Automatically generated file\n\n')
    z3consts.write('using System;\n\n'
                   '#pragma warning disable 1591\n\n'
                   'namespace Microsoft.Z3\n'
                   '{\n');

    for api_file in api_files:
        api_file_c = dotnet.find_file(api_file, dotnet.name)
        api_file   = os.path.join(api_file_c.src_dir, api_file)

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
                        for k in decls:
                            i = decls[k]
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
    if VERBOSE:
        print("Generated '%s'" % os.path.join(dotnet.src_dir, 'Enumerations.cs'))


# Extract enumeration types from z3_api.h, and add Java definitions
def mk_z3consts_java(api_files):
    blank_pat      = re.compile("^ *$")
    comment_pat    = re.compile("^ *//.*$")
    typedef_pat    = re.compile("typedef enum *")
    typedef2_pat   = re.compile("typedef enum { *")
    openbrace_pat  = re.compile("{ *")
    closebrace_pat = re.compile("}.*;")

    java = get_component(JAVA_COMPONENT)

    DeprecatedEnums = [ 'Z3_search_failure' ]
    gendir = os.path.join(java.src_dir, "enumerations")
    if not os.path.exists(gendir):
        os.mkdir(gendir)

    for api_file in api_files:
        api_file_c = java.find_file(api_file, java.name)
        api_file   = os.path.join(api_file_c.src_dir, api_file)

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
                        efile  = open('%s.java' % os.path.join(gendir, name), 'w')
                        efile.write('/**\n *  Automatically generated file\n **/\n\n')
                        efile.write('package %s.enumerations;\n\n' % java.package_name);

                        efile.write('/**\n')
                        efile.write(' * %s\n' % name)
                        efile.write(' **/\n')
                        efile.write('public enum %s {\n' % name)
                        efile.write
                        first = True
                        for k in decls:
                            i = decls[k]
                            if first:
                               first = False
                            else:
                                efile.write(',\n')
                            efile.write('    %s (%s)' % (k, i))
                        efile.write(";\n")
                        efile.write('\n    private final int intValue;\n\n')
                        efile.write('    %s(int v) {\n' % name)
                        efile.write('        this.intValue = v;\n')
                        efile.write('    }\n\n')
                        efile.write('    public static final %s fromInt(int v) {\n' % name)
                        efile.write('        for (%s k: values()) \n' % name)
                        efile.write('            if (k.intValue == v) return k;\n')
                        efile.write('        return values()[0];\n')
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
    if VERBOSE:
        print("Generated '%s'" % ('%s' % gendir))

def mk_gui_str(id):
    return '4D2F40D8-E5F9-473B-B548-%012d' % id

def mk_vs_proj(name, components):
    if not VS_PROJ:
        return
    proj_name = '%s.vcxproj' % os.path.join(BUILD_DIR, name)
    modes=['Debug', 'Release']
    PLATFORMS=['Win32']
    f = open(proj_name, 'w')
    f.write('<?xml version="1.0" encoding="utf-8"?>\n')
    f.write('<Project DefaultTargets="Build" ToolsVersion="4.0" xmlns="http://schemas.microsoft.com/developer/msbuild/2003">\n')
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
    f.write('   <PropertyGroup Label="Globals">\n')
    f.write('    <ProjectGuid>{%s}</ProjectGuid>\n' % mk_gui_str(0))
    f.write('    <ProjectName>%s</ProjectName>\n' % name)
    f.write('    <Keyword>Win32Proj</Keyword>\n')
    f.write('  </PropertyGroup>\n')
    f.write('  <Import Project="$(VCTargetsPath)\Microsoft.Cpp.Default.props" />\n')
    f.write('  <PropertyGroup Condition="\'$(Configuration)|$(Platform)\'==\'Debug|Win32\'" Label="Configuration">\n')
    f.write('    <ConfigurationType>Application</ConfigurationType>\n')
    f.write('    <CharacterSet>Unicode</CharacterSet>\n')
    f.write('    <UseOfMfc>false</UseOfMfc>\n')
    f.write('  </PropertyGroup>\n')
    f.write('  <Import Project="$(VCTargetsPath)\Microsoft.Cpp.props" />\n')
    f.write('  <ImportGroup Label="ExtensionSettings">\n')
    f.write('   </ImportGroup>\n')
    f.write('   <ImportGroup Label="PropertySheets">\n')
    f.write('    <Import Project="$(UserRootDir)\Microsoft.Cpp.$(Platform).user.props" Condition="exists(\'$(UserRootDir)\Microsoft.Cpp.$(Platform).user.props\')" Label="LocalAppDataPlatform" />  </ImportGroup>\n')
    f.write('  <PropertyGroup Label="UserMacros" />\n')
    f.write('  <PropertyGroup>\n')
    f.write('    <OutDir Condition="\'$(Configuration)|$(Platform)\'==\'Debug|Win32\'">$(SolutionDir)$(Configuration)\</OutDir>\n')
    f.write('    <TargetName Condition="\'$(Configuration)|$(Platform)\'==\'Debug|Win32\'">%s</TargetName>\n' % name)
    f.write('    <TargetExt Condition="\'$(Configuration)|$(Platform)\'==\'Debug|Win32\'">.exe</TargetExt>\n')
    f.write('    <OutDir Condition="\'$(Configuration)|$(Platform)\'==\'Release|Win32\'">$(SolutionDir)$(Configuration)\</OutDir>\n')
    f.write('    <TargetName Condition="\'$(Configuration)|$(Platform)\'==\'Release|Win32\'">%s</TargetName>\n' % name)
    f.write('    <TargetExt Condition="\'$(Configuration)|$(Platform)\'==\'Release|Win32\'">.exe</TargetExt>\n')
    f.write('  </PropertyGroup>\n')
    f.write('  <ItemDefinitionGroup Condition="\'$(Configuration)|$(Platform)\'==\'Debug|Win32\'">\n')
    f.write('    <ClCompile>\n')
    f.write('      <Optimization>Disabled</Optimization>\n')
    f.write('      <PreprocessorDefinitions>WIN32;_DEBUG;Z3DEBUG;_TRACE;_MP_INTERNAL;_WINDOWS;%(PreprocessorDefinitions)</PreprocessorDefinitions>\n')
    if VS_PAR:
        f.write('      <MinimalRebuild>false</MinimalRebuild>\n')
        f.write('      <MultiProcessorCompilation>true</MultiProcessorCompilation>\n')
    else:
        f.write('      <MinimalRebuild>true</MinimalRebuild>\n')
    f.write('      <BasicRuntimeChecks>EnableFastChecks</BasicRuntimeChecks>\n')
    f.write('      <WarningLevel>Level3</WarningLevel>\n')
    f.write('      <RuntimeLibrary>MultiThreadedDebugDLL</RuntimeLibrary>\n')
    f.write('      <OpenMPSupport>true</OpenMPSupport>\n')
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
    f.write('</AdditionalIncludeDirectories>\n')
    f.write('    </ClCompile>\n')
    f.write('    <Link>\n')
    f.write('      <OutputFile>$(OutDir)%s.exe</OutputFile>\n' % name)
    f.write('      <GenerateDebugInformation>true</GenerateDebugInformation>\n')
    f.write('      <SubSystem>Console</SubSystem>\n')
    f.write('      <StackReserveSize>8388608</StackReserveSize>\n')
    f.write('      <RandomizedBaseAddress>false</RandomizedBaseAddress>\n')
    f.write('      <DataExecutionPrevention>\n')
    f.write('      </DataExecutionPrevention>\n')
    f.write('      <TargetMachine>MachineX86</TargetMachine>\n')
    f.write('      <AdditionalLibraryDirectories>%(AdditionalLibraryDirectories)</AdditionalLibraryDirectories>\n')
    f.write('<AdditionalDependencies>psapi.lib;kernel32.lib;user32.lib;gdi32.lib;winspool.lib;comdlg32.lib;advapi32.lib;shell32.lib;ole32.lib;oleaut32.lib;uuid.lib;odbc32.lib;odbccp32.lib;%(AdditionalDependencies)</AdditionalDependencies>\n')
    f.write('    </Link>\n')
    f.write('  </ItemDefinitionGroup>\n')
    f.write('  <ItemDefinitionGroup Condition="\'$(Configuration)|$(Platform)\'==\'Release|Win32\'">\n')
    f.write('    <ClCompile>\n')
    f.write('      <Optimization>Disabled</Optimization>\n')
    f.write('      <PreprocessorDefinitions>WIN32;_NDEBUG;_MP_INTERNAL;_WINDOWS;%(PreprocessorDefinitions)</PreprocessorDefinitions>\n')
    if VS_PAR:
        f.write('      <MinimalRebuild>false</MinimalRebuild>\n')
        f.write('      <MultiProcessorCompilation>true</MultiProcessorCompilation>\n')
    else:
        f.write('      <MinimalRebuild>true</MinimalRebuild>\n')
    f.write('      <BasicRuntimeChecks>EnableFastChecks</BasicRuntimeChecks>\n')
    f.write('      <WarningLevel>Level3</WarningLevel>\n')
    f.write('      <RuntimeLibrary>MultiThreadedDLL</RuntimeLibrary>\n')
    f.write('      <OpenMPSupport>true</OpenMPSupport>\n')
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
    f.write('</AdditionalIncludeDirectories>\n')
    f.write('    </ClCompile>\n')
    f.write('    <Link>\n')
    f.write('      <OutputFile>$(OutDir)%s.exe</OutputFile>\n' % name)
    f.write('      <GenerateDebugInformation>true</GenerateDebugInformation>\n')
    f.write('      <SubSystem>Console</SubSystem>\n')
    f.write('      <StackReserveSize>8388608</StackReserveSize>\n')
    f.write('      <RandomizedBaseAddress>false</RandomizedBaseAddress>\n')
    f.write('      <DataExecutionPrevention>\n')
    f.write('      </DataExecutionPrevention>\n')
    f.write('      <TargetMachine>MachineX86</TargetMachine>\n')
    f.write('      <AdditionalLibraryDirectories>%(AdditionalLibraryDirectories)</AdditionalLibraryDirectories>\n')
    f.write('<AdditionalDependencies>psapi.lib;kernel32.lib;user32.lib;gdi32.lib;winspool.lib;comdlg32.lib;advapi32.lib;shell32.lib;ole32.lib;oleaut32.lib;uuid.lib;odbc32.lib;odbccp32.lib;%(AdditionalDependencies)</AdditionalDependencies>\n')
    f.write('    </Link>\n')
    f.write('  </ItemDefinitionGroup>\n')
    f.write('  <ItemGroup>\n')
    for dep in deps:
        dep = get_component(dep)
        for cpp in filter(lambda f: f.endswith('.cpp'), os.listdir(dep.src_dir)):
            f.write('    <ClCompile Include="%s" />\n' % os.path.join(dep.to_src_dir, cpp))
    f.write('  </ItemGroup>\n')
    f.write('  <Import Project="$(VCTargetsPath)\Microsoft.Cpp.targets" />\n')
    f.write('  <ImportGroup Label="ExtensionTargets">\n')
    f.write('  </ImportGroup>\n')
    f.write('</Project>\n')
    if is_verbose():
        print("Generated '%s'" % proj_name)

def mk_win_dist(build_path, dist_path):
    for c in get_components():
        c.mk_win_dist(build_path, dist_path)
    # Add Z3Py to bin directory
    print("Adding to %s\n" % dist_path)
    for pyc in filter(lambda f: f.endswith('.pyc') or f.endswith('.py'), os.listdir(build_path)):
        shutil.copy(os.path.join(build_path, pyc),
                    os.path.join(dist_path, 'bin', pyc))

def mk_unix_dist(build_path, dist_path):
    for c in get_components():
        c.mk_unix_dist(build_path, dist_path)
    # Add Z3Py to bin directory
    for pyc in filter(lambda f: f.endswith('.pyc') or f.endswith('.py'), os.listdir(build_path)):
        shutil.copy(os.path.join(build_path, pyc),
                    os.path.join(dist_path, 'bin', pyc))


if __name__ == '__main__':
    import doctest
    doctest.testmod()
