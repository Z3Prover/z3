############################################
# Copyright (c) 2012 Microsoft Corporation
# 
# Auxiliary scripts for generating Makefiles 
# and Visual Studio project files.
#
# Author: Leonardo de Moura (leonardo)
############################################
import os
import glob
import re
import getopt
import sys
import shutil
from mk_exception import *
from fnmatch import fnmatch
import distutils.sysconfig
import compileall

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
CPP_COMPONENT='cpp'
#####################
IS_WINDOWS=False
VERBOSE=True
DEBUG_MODE=False
SHOW_CPPS = True
VS_X64 = False
ONLY_MAKEFILES = False
Z3PY_SRC_DIR=None
VS_PROJ = False
TRACE = False
DOTNET_ENABLED=False
STATIC_LIB=False

VER_MAJOR=None
VER_MINOR=None
VER_BUILD=None
VER_REVISION=None

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
            print "dos2unix '%s'" % fname

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
                print "Fixing end of line..."
            dos2unix_tree()

if os.name == 'nt':
    IS_WINDOWS=True
    # Visual Studio already displays the files being compiled
    SHOW_CPPS=False
    # Enable .Net bindings by default on windows
    DOTNET_ENABLED=True

def display_help():
    print "mk_make.py: Z3 Makefile generator\n"
    print "This script generates the Makefile for the Z3 theorem prover."
    print "It must be executed from the Z3 root directory."
    print "\nOptions:"
    print "  -h, --help                    display this message."
    print "  -s, --silent                  do not print verbose messages."
    print "  -b <sudir>, --build=<subdir>  subdirectory where Z3 will be built (default: build)."
    print "  -d, --debug                   compile Z3 in debug mode."
    print "  -x, --x64                     create 64 binary when using Visual Studio."
    print "  -m, --makefiles               generate only makefiles."
    print "  -c, --showcpp                 display file .cpp file names before invoking compiler."
    print "  -v, --vsproj                  generate Visual Studio Project Files."
    print "  -t, --trace                   enable tracing in release mode."
    print "  -n, --nodotnet                do not generate Microsoft.Z3.dll make rules."
    print "  --staticlib                   build Z3 static library."
    exit(0)

# Parse configuration option for mk_make script
def parse_options():
    global VERBOSE, DEBUG_MODE, IS_WINDOWS, VS_X64, ONLY_MAKEFILES, SHOW_CPPS, VS_PROJ, TRACE, DOTNET_ENABLED, STATIC_LIB
    options, remainder = getopt.gnu_getopt(sys.argv[1:], 'b:dsxhmcvtn', ['build=', 
                                                                         'debug',
                                                                         'silent',
                                                                         'x64',
                                                                         'help',
                                                                         'makefiles',
                                                                         'showcpp',
                                                                         'vsproj',
                                                                         'trace',
                                                                         'nodotnet',
                                                                         'staticlib'
                                                                         ])
    for opt, arg in options:
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
            display_help()
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
        else:
            raise MKException("Invalid command line option '%s'" % opt)
        
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
    l = p.split('/')
    n = len(l)
    r = '..'
    for i in range(1, n):
        r = '%s/%s' % (r, '..')
    return r

def mk_dir(d):
    if not os.path.exists(d):
        os.makedirs(d)

def set_build_dir(d):
    global BUILD_DIR, REV_BUILD_DIR
    BUILD_DIR = d
    REV_BUILD_DIR = reverse_path(d)

def set_z3py_dir(p):
    global SRC_DIR, Z3PY_SRC_DIR
    full = '%s/%s' % (SRC_DIR, p)
    if not os.path.exists(full):
        raise MKException("Python bindings directory '%s' does not exist" % full)
    Z3PY_SRC_DIR = full
    if VERBOSE:
        print "Python bindinds directory was detected."

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

def get_cpp_files(path):
    return filter(lambda f: f.endswith('.cpp'), os.listdir(path))

def get_c_files(path):
    return filter(lambda f: f.endswith('.c'), os.listdir(path))

def get_cs_files(path):
    return filter(lambda f: f.endswith('.cs'), os.listdir(path))

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
        self.path = path
        self.deps = find_all_deps(name, deps)
        self.build_dir = path
        self.src_dir   = '%s/%s' % (SRC_DIR, path)
        self.to_src_dir = '%s/%s' % (REV_BUILD_DIR, self.src_dir)

    # Find fname in the include paths for the given component.
    # ownerfile is only used for creating error messages.
    # That is, we were looking for fname when processing ownerfile
    def find_file(self, fname, ownerfile):
        full_fname = '%s/%s' % (self.src_dir, fname)
        if os.path.exists(full_fname):
            return self
        for dep in self.deps:
            c_dep = get_component(dep)
            full_fname = '%s/%s' % (c_dep.src_dir, fname)
            if os.path.exists(full_fname):
                return c_dep
        raise MKException("Failed to find include file '%s' for '%s' when processing '%s'." % (fname, ownerfile, self.name))

    # Display all dependencies of file basename located in the given component directory.
    # The result is displayed at out
    def add_cpp_h_deps(self, out, basename):
        includes = extract_c_includes('%s/%s' % (self.src_dir, basename))
        out.write('%s/%s' % (self.to_src_dir, basename))
        for include in includes:
            owner = self.find_file(include, basename)
            out.write(' %s/%s.node' % (owner.build_dir, include))

    # Add a rule for each #include directive in the file basename located at the current component.
    def add_rule_for_each_include(self, out, basename):
        fullname = '%s/%s' % (self.src_dir, basename)
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
        include_src_path   = '%s/%s' % (self.to_src_dir, include)
        if include_src_path in _Processed_Headers:
            return
        _Processed_Headers.add(include_src_path)
        self.add_rule_for_each_include(out, include)
        include_node = '%s/%s.node' % (self.build_dir, include)
        out.write('%s: ' % include_node)
        self.add_cpp_h_deps(out, include)              
        out.write('\n')
        out.write('\t@echo done > %s\n' % include_node)

    def add_cpp_rules(self, out, include_defs, cppfile):
        self.add_rule_for_each_include(out, cppfile)
        objfile = '%s/%s$(OBJ_EXT)' % (self.build_dir, os.path.splitext(cppfile)[0])
        srcfile = '%s/%s' % (self.to_src_dir, cppfile)
        out.write('%s: ' % objfile)
        self.add_cpp_h_deps(out, cppfile)
        out.write('\n')
        if SHOW_CPPS:
            out.write('\t@echo %s/%s\n' % (self.src_dir, cppfile))
        # TRACE is enabled in debug mode by default
        extra_opt = ''
        if TRACE and not DEBUG_MODE:
            if IS_WINDOWS:
                extra_opt = '/D _TRACE'
            else:
                extra_opt = '-D _TRACE'
        out.write('\t@$(CXX) $(CXXFLAGS) %s $(%s) $(CXX_OUT_FLAG)%s %s\n' % (extra_opt, include_defs, objfile, srcfile))

    def mk_makefile(self, out):
        include_defs = mk_fresh_name('includes')
        out.write('%s =' % include_defs)
        for dep in self.deps:
            out.write(' -I%s' % get_component(dep).to_src_dir)
        out.write('\n')
        mk_dir('%s/%s' % (BUILD_DIR, self.build_dir))
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


class LibComponent(Component):
    def __init__(self, name, path, deps, includes2install):
        Component.__init__(self, name, path, deps)
        self.includes2install = includes2install

    def mk_makefile(self, out):
        Component.mk_makefile(self, out)
        # generate rule for lib
        objs = []
        for cppfile in get_cpp_files(self.src_dir):
            objfile = '%s/%s$(OBJ_EXT)' % (self.build_dir, os.path.splitext(cppfile)[0])
            objs.append(objfile)

        libfile = '%s/%s$(LIB_EXT)' % (self.build_dir, self.name)
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

    def mk_install(self, out):
        for include in self.includes2install:
            out.write('\t@cp %s/%s $(PREFIX)/include/%s\n' % (self.to_src_dir, include, include))
    
    def mk_uninstall(self, out):
        for include in self.includes2install:
            out.write('\t@rm -f $(PREFIX)/include/%s\n' % include)

    def mk_win_dist(self, build_path, dist_path):
        mk_dir('%s/include' % dist_path)
        for include in self.includes2install:
            shutil.copy('%s/%s' % (self.src_dir, include),
                        '%s/include/%s' % (dist_path, include))        

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
    return sorted(cnames, cmp=comp_components)

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
            objfile = '%s/%s$(OBJ_EXT)' % (self.build_dir, os.path.splitext(cppfile)[0])
            objs.append(objfile)
        for obj in objs:
            out.write(' ')
            out.write(obj)
        for dep in deps:
            c_dep = get_component(dep)
            out.write(' %s/%s$(LIB_EXT)' % (c_dep.build_dir, c_dep.name))
        out.write('\n')
        out.write('\t$(LINK) $(LINK_OUT_FLAG)%s $(LINK_FLAGS)' % exefile)
        for obj in objs:
            out.write(' ')
            out.write(obj)
        for dep in deps:
            c_dep = get_component(dep)
            out.write(' %s/%s$(LIB_EXT)' % (c_dep.build_dir, c_dep.name))
        out.write(' $(LINK_EXTRA_FLAGS)\n')
        out.write('%s: %s\n\n' % (self.name, exefile))

    def require_install_tactics(self):
        return ('tactic' in self.deps) and ('cmd_context' in self.deps)

    # All executables are included in the all: rule
    def main_component(self):
        return True

    def mk_install(self, out):
        if self.install:
            exefile = '%s$(EXE_EXT)' % self.exe_name
            out.write('\t@cp %s $(PREFIX)/bin/%s\n' % (exefile, exefile))
    
    def mk_uninstall(self, out):
        exefile = '%s$(EXE_EXT)' % self.exe_name
        out.write('\t@rm -f $(PREFIX)/bin/%s\n' % exefile)

    def mk_win_dist(self, build_path, dist_path):
        if self.install:
            mk_dir('%s/bin' % dist_path)
            shutil.copy('%s/%s.exe' % (build_path, self.exe_name),
                        '%s/bin/%s.exe' % (dist_path, self.exe_name))


class ExtraExeComponent(ExeComponent):
    def __init__(self, name, exe_name, path, deps, install):
        ExeComponent.__init__(self, name, exe_name, path, deps, install)

    def main_component(self):
        return False

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

    def mk_makefile(self, out):
        Component.mk_makefile(self, out)
        # generate rule for (SO_EXT)
        dllfile = '%s$(SO_EXT)' % self.dll_name
        out.write('%s:' % dllfile)
        deps = sort_components(self.deps)
        objs = []
        for cppfile in get_cpp_files(self.src_dir):
            objfile = '%s/%s$(OBJ_EXT)' % (self.build_dir, os.path.splitext(cppfile)[0])
            objs.append(objfile)
        # Explicitly include obj files of reexport. This fixes problems with exported symbols on Linux and OSX.
        for reexport in self.reexports:
            reexport = get_component(reexport)
            for cppfile in get_cpp_files(reexport.src_dir):
                objfile = '%s/%s$(OBJ_EXT)' % (reexport.build_dir, os.path.splitext(cppfile)[0])
                objs.append(objfile)
        for obj in objs:
            out.write(' ')
            out.write(obj)
        for dep in deps:
            if not dep in self.reexports:
                c_dep = get_component(dep)
                out.write(' %s/%s$(LIB_EXT)' % (c_dep.build_dir, c_dep.name))
        out.write('\n')
        out.write('\t$(LINK) $(SLINK_OUT_FLAG)%s $(SLINK_FLAGS)' % dllfile)
        for obj in objs:
            out.write(' ')
            out.write(obj)
        for dep in deps:
            if not dep in self.reexports:
                c_dep = get_component(dep)
                out.write(' %s/%s$(LIB_EXT)' % (c_dep.build_dir, c_dep.name))
        out.write(' $(SLINK_EXTRA_FLAGS)')
        if IS_WINDOWS:
            out.write(' /DEF:%s/%s.def' % (self.to_src_dir, self.name))
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
            objfile = '%s/%s$(OBJ_EXT)' % (self.build_dir, os.path.splitext(cppfile)[0])
            objs.append(objfile)
        # we have to "reexport" all object files
        for dep in self.deps:
            dep = get_component(dep)
            for cppfile in get_cpp_files(dep.src_dir):
                objfile = '%s/%s$(OBJ_EXT)' % (dep.build_dir, os.path.splitext(cppfile)[0])
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

    def require_def_file(self):
        return IS_WINDOWS and self.export_files

    def mk_install(self, out):
        if self.install:
            dllfile = '%s$(SO_EXT)' % self.dll_name
            out.write('\t@cp %s $(PREFIX)/lib/%s\n' % (dllfile, dllfile))
            out.write('\t@cp %s %s/%s\n' % (dllfile, PYTHON_PACKAGE_DIR, dllfile))
            if self.static:
                libfile = '%s$(LIB_EXT)' % self.dll_name
                out.write('\t@cp %s $(PREFIX)/lib/%s\n' % (libfile, libfile))
            

    def mk_uninstall(self, out):
        dllfile = '%s$(SO_EXT)' % self.dll_name
        out.write('\t@rm -f $(PREFIX)/lib/%s\n' % dllfile)
        out.write('\t@rm -f %s/%s\n' % (PYTHON_PACKAGE_DIR, dllfile))
        libfile = '%s$(LIB_EXT)' % self.dll_name
        out.write('\t@rm -f $(PREFIX)/lib/%s\n' % libfile)

    def mk_win_dist(self, build_path, dist_path):
        if self.install:
            mk_dir('%s/bin' % dist_path)
            shutil.copy('%s/%s.dll' % (build_path, self.dll_name),
                        '%s/bin/%s.dll' % (dist_path, self.dll_name))
            if self.static:
                mk_dir('%s/bin' % dist_path)
                shutil.copy('%s/%s.lib' % (build_path, self.dll_name),
                            '%s/bin/%s.lib' % (dist_path, self.dll_name))

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
                cs_fp_files.append('%s/%s' % (self.to_src_dir, cs_file))
                cs_files.append(cs_file)
            if self.assembly_info_dir != '.':
                for cs_file in get_cs_files('%s/%s' % (self.src_dir, self.assembly_info_dir)):
                    cs_fp_files.append('%s/%s/%s' % (self.to_src_dir, self.assembly_info_dir, cs_file))
                    cs_files.append('%s\%s' % (self.assembly_info_dir, cs_file))
            dllfile = '%s.dll' % self.dll_name
            out.write('%s:' % dllfile)
            for cs_file in cs_fp_files:
                out.write(' ')
                out.write(cs_file)
            out.write('\n')
            out.write('  cd %s && csc /noconfig /unsafe+ /nowarn:1701,1702 /nostdlib+ /errorreport:prompt /warn:4 /define:DEBUG;TRACE /reference:mscorlib.dll /reference:System.Core.dll /reference:System.dll /reference:System.Numerics.dll /debug+ /debug:full /filealign:512 /optimize- /out:%s.dll /target:library' % (self.to_src_dir, self.dll_name))
            for cs_file in cs_files:
                out.write(' ')
                out.write(cs_file)
            out.write('\n')
            # HACK
            win_to_src_dir = self.to_src_dir.replace('/', '\\')
            out.write('  move %s\%s\n' % (win_to_src_dir, dllfile))
            out.write('  move %s\%s.pdb\n' % (win_to_src_dir, self.dll_name))
            out.write('%s: %s\n\n' % (self.name, dllfile))
            return
    
    def main_component(self):
        return DOTNET_ENABLED

    def has_assembly_info(self):
        return True

    def mk_win_dist(self, build_path, dist_path):
        if DOTNET_ENABLED:
            # Assuming all DotNET dll should be in the distribution
            mk_dir('%s/bin' % dist_path)
            shutil.copy('%s/%s.dll' % (build_path, self.dll_name),
                        '%s/bin/%s.dll' % (dist_path, self.dll_name))

class ExampleComponent(Component):
    def __init__(self, name, path):
        Component.__init__(self, name, path, [])
        self.ex_dir   = '%s/%s' % (EXAMPLE_DIR, self.path)
        self.to_ex_dir = '%s/%s' % (REV_BUILD_DIR, self.ex_dir)

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
            out.write('%s/%s' % (self.to_ex_dir, cppfile))
        out.write('\n')
        out.write('\t%s $(LINK_OUT_FLAG)%s $(LINK_FLAGS)' % (self.compiler(), exefile))
        # Add include dir components
        out.write(' -I%s' % get_component(API_COMPONENT).to_src_dir)
        out.write(' -I%s' % get_component(CPP_COMPONENT).to_src_dir)
        for cppfile in self.src_files():
            out.write(' ')
            out.write('%s/%s' % (self.to_ex_dir, cppfile))
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
            exefile = '%s.exe' % self.name
            out.write('%s: %s' % (exefile, dll))
            for csfile in get_cs_files(self.ex_dir):
                out.write(' ')
                out.write('%s/%s' % (self.to_ex_dir, csfile))
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
                out.write('%s\\%s' % (win_ex_dir, csfile))
            out.write('\n')
            out.write('_ex_%s: %s\n\n' % (self.name, exefile))

class PythonExampleComponent(ExampleComponent):
    def __init__(self, name, path):
        ExampleComponent.__init__(self, name, path)

    # Python examples are just placeholders, we just copy the *.py files when mk_makefile is invoked.
    # We don't need to include them in the :examples rule
    def mk_makefile(self, out):
        full = '%s/%s' % (EXAMPLE_DIR, self.path)
        for py in filter(lambda f: f.endswith('.py'), os.listdir(full)):
            shutil.copyfile('%s/%s' % (full, py), '%s/%s' % (BUILD_DIR, py))
            if is_verbose():
                print "Copied Z3Py example '%s' to '%s'" % (py, BUILD_DIR)
        out.write('_ex_%s: \n\n' % self.name)


def reg_component(name, c):
    global _Id, _Components, _ComponentNames, _Name2Component
    c.id = _Id
    _Id = _Id + 1
    _Components.append(c)
    _ComponentNames.add(name)
    _Name2Component[name] = c
    if VERBOSE:
        print "New component: '%s'" % name

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

def add_cpp_example(name, path=None):
    c = CppExampleComponent(name, path)
    reg_component(name, c)

def add_c_example(name, path=None):
    c = CExampleComponent(name, path)
    reg_component(name, c)

def add_dotnet_example(name, path=None):
    c = DotNetExampleComponent(name, path)
    reg_component(name, c)

def add_z3py_example(name, path=None):
    c = PythonExampleComponent(name, path)
    reg_component(name, c)

# Copy configuration correct file to BUILD_DIR
def cp_config_mk():
    if IS_WINDOWS:
        if VS_X64:
            if DEBUG_MODE:
                shutil.copyfile('scripts/config-vs-debug-x64.mk', '%s/config.mk' % BUILD_DIR)
            else:
                shutil.copyfile('scripts/config-vs-release-x64.mk', '%s/config.mk' % BUILD_DIR)
        else:
            if DEBUG_MODE:
                shutil.copyfile('scripts/config-vs-debug.mk', '%s/config.mk' % BUILD_DIR)
            else:
                shutil.copyfile('scripts/config-vs-release.mk', '%s/config.mk' % BUILD_DIR)
    else:
        if DEBUG_MODE:
            shutil.copyfile('scripts/config-debug.mk', '%s/config.mk' % BUILD_DIR)
        else:
            shutil.copyfile('scripts/config-release.mk', '%s/config.mk' % BUILD_DIR)

def mk_install(out):
    out.write('install:\n')
    out.write('\t@mkdir -p $(PREFIX)/bin\n')
    out.write('\t@mkdir -p $(PREFIX)/include\n')
    out.write('\t@mkdir -p $(PREFIX)/lib\n')
    for c in get_components():
        c.mk_install(out)
    out.write('\t@cp z3*.pyc %s\n' % PYTHON_PACKAGE_DIR)
    out.write('\t@echo Z3 was successfully installed.\n')
    out.write('\n')    

def mk_uninstall(out):
    out.write('uninstall:\n')
    for c in get_components():
        c.mk_uninstall(out)
    out.write('\t@rm -f %s/z3*.pyc\n' % PYTHON_PACKAGE_DIR)
    out.write('\t@echo Z3 was successfully uninstalled.\n')
    out.write('\n')    

# Generate the Z3 makefile
def mk_makefile():
    mk_dir(BUILD_DIR)
    cp_config_mk()
    if VERBOSE:
        print "Writing %s/Makefile" % BUILD_DIR
    out = open('%s/Makefile' % BUILD_DIR, 'w')
    out.write('# Automatically generated file. Generator: scripts/mk_make.py\n')
    out.write('include config.mk\n')
    # Generate :all rule
    out.write('all:')
    for c in get_components():
        if c.main_component():
            out.write(' %s' % c.name)
    out.write('\n\t@echo Z3 was successfully built.\n')
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
        print "Makefile was successfully generated."
        if not IS_WINDOWS:
            print "  python packages dir:", PYTHON_PACKAGE_DIR
        if DEBUG_MODE:
            print "  compilation mode: Debug"
        else:
            print "  compilation mode: Release"
        if IS_WINDOWS:
            if VS_X64:
                print "  platform: x64\n"
                print "To build Z3, open a [Visual Studio x64 Command Prompt], then"
            else:
                print "  platform: x86"
                print "To build Z3, open a [Visual Studio Command Prompt], then"
            print "type 'cd %s/%s && nmake'\n" % (os.getcwd(), BUILD_DIR)
            print 'Remark: to open a Visual Studio Command Prompt, go to: "Start > All Programs > Visual Studio > Visual Studio Tools"'
        else:
            print "Type 'cd %s; make' to build Z3" % BUILD_DIR
        
# Generate automatically generated source code
def mk_auto_src():
    if not ONLY_MAKEFILES:
        mk_pat_db()
        mk_all_install_tactic_cpps()

# TODO: delete after src/ast/pattern/expr_pattern_match
# database.smt ==> database.h
def mk_pat_db():
    c = get_component(PATTERN_COMPONENT)
    fin  = open('%s/database.smt2' % c.src_dir, 'r')
    fout = open('%s/database.h'  % c.src_dir, 'w')
    fout.write('char const * g_pattern_database =\n')
    for line in fin:
        fout.write('"%s\\n"\n' % line.strip('\n'))
    fout.write(';\n')    
    if VERBOSE:
        print "Generated '%s/database.h'" % c.src_dir

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
        update_all_assembly_infos(major, minor, build, revision)
        mk_def_files()
        
# Update files with the version number
def mk_version_dot_h(major, minor, build, revision):
    c = get_component(UTIL_COMPONENT)
    fout = open('%s/version.h' % c.src_dir, 'w')
    fout.write('// automatically generated file.\n')
    fout.write('#define Z3_MAJOR_VERSION   %s\n' % major)
    fout.write('#define Z3_MINOR_VERSION   %s\n' % minor)
    fout.write('#define Z3_BUILD_NUMBER    %s\n' % build)
    fout.write('#define Z3_REVISION_NUMBER %s\n' % revision)
    if VERBOSE:
        print "Generated '%s/version.h'" % c.src_dir

# Update version number in AssemblyInfo.cs files
def update_all_assembly_infos(major, minor, build, revision):
    for c in get_components():
        if c.has_assembly_info():
            assembly = '%s/%s/AssemblyInfo.cs' % (c.src_dir, c.assembly_info_dir)
            if os.path.exists(assembly):
                # It is a CS file
                update_assembly_info_version(assembly,
                                             major, minor, build, revision, False)
            else:
                assembly = '%s/%s/AssemblyInfo.cpp' % (c.src_dir, c.assembly_info_dir)
                if os.path.exists(assembly):
                    # It is a cpp file
                    update_assembly_info_version(assembly,
                                                 major, minor, build, revision, True)
                else:
                    raise MKException("Failed to find assembly info file at '%s/%s'" % (c.src_dir, c.assembly_info_dir))
                    
                
# Update version number in the given AssemblyInfo.cs files
def update_assembly_info_version(assemblyinfo, major, minor, build, revision, is_cpp=False):
    if is_cpp:
        ver_pat   = re.compile('[assembly:AssemblyVersionAttribute\("[\.\d]*"\) *')
        fver_pat  = re.compile('[assembly:AssemblyFileVersionAttribute\("[\.\d]*"\) *')
    else:
        ver_pat   = re.compile('[assembly: AssemblyVersion\("[\.\d]*"\) *')
        fver_pat  = re.compile('[assembly: AssemblyFileVersion\("[\.\d]*"\) *')
    fin  = open(assemblyinfo, 'r')
    tmp  = '%s.new' % assemblyinfo
    fout = open(tmp, 'w')
    num_updates = 0
    for line in fin:
        if ver_pat.match(line):
            if is_cpp:
                fout.write('[assembly:AssemblyVersionAttribute("%s.%s.%s.%s")];\n' % (major, minor, build, revision))
            else:
                fout.write('[assembly: AssemblyVersion("%s.%s.%s.%s")]\n' % (major, minor, build, revision))
            num_updates = num_updates + 1
        elif fver_pat.match(line):
            if is_cpp:
                fout.write('[assembly:AssemblyFileVersionAttribute("%s.%s.%s.%s")];\n' % (major, minor, build, revision))
            else:
                fout.write('[assembly: AssemblyFileVersion("%s.%s.%s.%s")]\n' % (major, minor, build, revision))
            num_updates = num_updates + 1
        else:
            fout.write(line)
    # if VERBOSE:
    #    print "%s version numbers updated at '%s'" % (num_updates, assemblyinfo)
    assert num_updates == 2, "unexpected number of version number updates"
    fin.close()
    fout.close()
    shutil.move(tmp, assemblyinfo)
    if VERBOSE:
        print "Updated '%s'" % assemblyinfo

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
    fullname = '%s/install_tactic.cpp' % path
    fout  = open(fullname, 'w')
    fout.write('// Automatically generated file.\n')
    fout.write('#include"tactic.h"\n')
    fout.write('#include"tactic_cmds.h"\n')
    fout.write('#include"cmd_context.h"\n')
    tactic_pat   = re.compile('[ \t]*ADD_TACTIC\(.*\)')
    probe_pat    = re.compile('[ \t]*ADD_PROBE\(.*\)')
    for cname in cnames:
        c = get_component(cname)
        h_files = filter(lambda f: f.endswith('.h'), os.listdir(c.src_dir))
        for h_file in h_files:
            added_include = False
            fin = open("%s/%s" % (c.src_dir, h_file), 'r')
            for line in fin:
                if tactic_pat.match(line):
                    if not added_include:
                        added_include = True
                        fout.write('#include"%s"\n' % h_file)
                    try: 
                        exec line.strip('\n ') in globals()
                    except:
                        raise MKException("Failed processing ADD_TACTIC command at '%s'\n%s" % (fullname, line))
                if probe_pat.match(line):
                    if not added_include:
                        added_include = True
                        fout.write('#include"%s"\n' % h_file)
                    try: 
                        exec line.strip('\n ') in globals()
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
        print "Generated '%s'" % fullname

def mk_all_install_tactic_cpps():
    if not ONLY_MAKEFILES:
        for c in get_components():
            if c.require_install_tactics():
                cnames = []
                cnames.extend(c.deps)
                cnames.append(c.name)
                mk_install_tactic_cpp(cnames, c.src_dir)

# Generate a .def based on the files at c.export_files slot.
def mk_def_file(c):
    pat1 = re.compile(".*Z3_API.*")
    defname = '%s/%s.def' % (c.src_dir, c.name)
    fout = open(defname, 'w')
    fout.write('LIBRARY "%s"\nEXPORTS\n' % c.dll_name)
    num = 1
    for dot_h in c.export_files:
        dot_h_c = c.find_file(dot_h, c.name)
        api = open('%s/%s' % (dot_h_c.src_dir, dot_h), 'r')
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
        print "Generated '%s'" % defname

def mk_def_files():
    if not ONLY_MAKEFILES:
        for c in get_components():
            if c.require_def_file():
                mk_def_file(c)

def cp_z3pyc_to_build():
    mk_dir(BUILD_DIR)
    if compileall.compile_dir(Z3PY_SRC_DIR, force=1) != 1:
        raise MKException("failed to compile Z3Py sources")
    for pyc in filter(lambda f: f.endswith('.pyc'), os.listdir(Z3PY_SRC_DIR)):
        try:
            os.remove('%s/%s' % (BUILD_DIR, pyc))
        except:
            pass
        shutil.copyfile('%s/%s' % (Z3PY_SRC_DIR, pyc), '%s/%s' % (BUILD_DIR, pyc))
        os.remove('%s/%s' % (Z3PY_SRC_DIR, pyc))
        if is_verbose():
            print "Generated '%s'" % pyc

def mk_bindings(api_files):
    if not ONLY_MAKEFILES:
        mk_z3consts_py(api_files)
        mk_z3consts_donet(api_files)
        new_api_files = []
        api = get_component(API_COMPONENT)
        for api_file in api_files:
            api_file_path = api.find_file(api_file, api.name)
            new_api_files.append('%s/%s' % (api_file_path.src_dir, api_file))
        g = {}
        g["API_FILES"] = new_api_files
        execfile('scripts/update_api.py', g) # HACK
        cp_z3pyc_to_build()
                          
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

    z3consts  = open('%s/z3consts.py' % Z3PY_SRC_DIR, 'w')
    z3consts.write('# Automatically generated file\n\n')

    api_dll = get_component(Z3_DLL_COMPONENT)

    for api_file in api_files:
        api_file_c = api_dll.find_file(api_file, api_dll.name)
        api_file   = '%s/%s' % (api_file_c.src_dir, api_file)
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
    if VERBOSE:
        print "Generated '%s'" % ('%s/z3consts.py' % Z3PY_SRC_DIR)
                

# Extract enumeration types from z3_api.h, and add .Net definitions
def mk_z3consts_donet(api_files):
    blank_pat      = re.compile("^ *$")
    comment_pat    = re.compile("^ *//.*$")
    typedef_pat    = re.compile("typedef enum *")
    typedef2_pat   = re.compile("typedef enum { *")
    openbrace_pat  = re.compile("{ *")
    closebrace_pat = re.compile("}.*;")

    dotnet = get_component(DOTNET_COMPONENT)

    DeprecatedEnums = [ 'Z3_search_failure' ]
    z3consts  = open('%s/Enumerations.cs' % dotnet.src_dir, 'w')
    z3consts.write('// Automatically generated file\n\n')
    z3consts.write('using System;\n\n'
                   '#pragma warning disable 1591\n\n'
                   'namespace Microsoft.Z3\n'
                   '{\n');

    for api_file in api_files:
        api_file_c = dotnet.find_file(api_file, dotnet.name)
        api_file   = '%s/%s' % (api_file_c.src_dir, api_file)

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
    if VERBOSE:
        print "Generated '%s'" % ('%s/Enumerations.cs' % dotnet.src_dir)

def mk_gui_str(id):
    return '4D2F40D8-E5F9-473B-B548-%012d' % id

def mk_vs_proj(name, components):
    if not VS_PROJ:
        return
    proj_name = '%s/%s.vcxproj' % (BUILD_DIR, name)
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
    f.write('  </PropertyGroup>\n')
    f.write('  <ItemDefinitionGroup Condition="\'$(Configuration)|$(Platform)\'==\'Debug|Win32\'">\n')
    f.write('    <ClCompile>\n')
    f.write('      <Optimization>Disabled</Optimization>\n')
    f.write('      <PreprocessorDefinitions>WIN32;_DEBUG;Z3DEBUG;_TRACE;_MP_INTERNAL;_WINDOWS;%(PreprocessorDefinitions)</PreprocessorDefinitions>\n')
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
    f.write('  <ItemGroup>\n')
    for dep in deps:
        dep = get_component(dep)
        for cpp in filter(lambda f: f.endswith('.cpp'), os.listdir(dep.src_dir)):
            f.write('    <ClCompile Include="%s/%s" />\n' % (dep.to_src_dir, cpp))
    f.write('  </ItemGroup>\n')
    f.write('  <Import Project="$(VCTargetsPath)\Microsoft.Cpp.targets" />\n')
    f.write('  <ImportGroup Label="ExtensionTargets">\n')
    f.write('  </ImportGroup>\n')
    f.write('</Project>\n')
    if is_verbose():
        print "Generated '%s'" % proj_name

def mk_win_dist(build_path, dist_path):
    for c in get_components():
        c.mk_win_dist(build_path, dist_path)
    # Add Z3Py to lib directory
    for pyc in filter(lambda f: f.endswith('.pyc'), os.listdir(build_path)):
        shutil.copy('%s/%s' % (build_path, pyc),
                    '%s/bin/%s' % (dist_path, pyc))
