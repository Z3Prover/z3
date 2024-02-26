############################################
# Copyright (c) 2013 Microsoft Corporation
#
# Scripts for automatically generating
# Linux/OSX/BSD distribution zip files.
#
# Author: Leonardo de Moura (leonardo)
############################################

import os
import subprocess
import zipfile
import re
import getopt
import sys
import shutil
from mk_exception import *
from fnmatch import fnmatch

def getenv(name, default):
    try:
        return os.environ[name].strip(' "\'')
    except:
        return default

BUILD_DIR = 'build-dist'
DIST_DIR = 'dist'
VERBOSE = True
FORCE_MK = False
ASSEMBLY_VERSION = None
DOTNET_CORE_ENABLED = True
DOTNET_KEY_FILE = None
JAVA_ENABLED = True
JULIA_ENABLED = False
GIT_HASH = False
PYTHON_ENABLED = True
ARM64 = False
MAKEJOBS = getenv("MAKEJOBS", "24")

def set_verbose(flag):
    global VERBOSE
    VERBOSE = flag

def is_verbose():
    return VERBOSE

def mk_dir(d):
    if not os.path.exists(d):
        if is_verbose():
            print("Make directory", d)
        os.makedirs(d)

def get_z3_name():
    version = "4"
    if ASSEMBLY_VERSION:
        version = ASSEMBLY_VERSION
    print("Assembly version:", version)
    if GIT_HASH:
        return 'z3-%s.%s' % (version, get_git_hash())
    else:
        return 'z3-%s' % (version)

def get_build_dir():
    return BUILD_DIR

def get_build_dist():
    return os.path.join(get_build_dir(), DIST_DIR)

def get_build_dist_path():
    return os.path.join(get_build_dist(), get_z3_name())

def set_build_dir(path):
    global BUILD_DIR
    BUILD_DIR = os.path.expanduser(os.path.normpath(path))
    mk_dir(BUILD_DIR)

def display_help():
    print("mk_unix_dist_cmake.py: Z3 Unix distribution generator\n")
    print("This script generates the zip files containing executables, shared objects, header files for Unix.")
    print("It must be executed from the Z3 root directory.")
    print("\nOptions:")
    print("  -h, --help                    display this message.")
    print("  -s, --silent                  do not print verbose messages.")
    print("  -b <subdir>, --build=<subdir> subdirectory where Z3 will be built (default: build-dist).")
    print("  -f, --force                   force script to regenerate Makefiles.")
    print("  --version=<version>           release version.")
    print("  --assembly-version            assembly version for dll")
    print("  --nodotnet                    do not include .NET bindings in the binary distribution files.")
    print("  --dotnet-key=<file>           strongname sign the .NET assembly with the private key in <file>.")
    print("  --nojava                      do not include Java bindings in the binary distribution files.")
    print("  --nopython                    do not include Python bindings in the binary distribution files.")
    print("  --julia                       build Julia bindings.")
    print("  --githash                     include git hash in the Zip file.")
    print("  --arm64                       build for ARM64 architecture.")
    exit(0)

# Parse configuration option for mk_make script
def parse_options():
    global FORCE_MK, JAVA_ENABLED, JULIA_ENABLED, GIT_HASH, DOTNET_CORE_ENABLED, DOTNET_KEY_FILE, ASSEMBLY_VERSION, PYTHON_ENABLED, ARM64
    path = BUILD_DIR
    options, remainder = getopt.gnu_getopt(sys.argv[1:], 'b:hsf', ['build=',
                                                                   'help',
                                                                   'silent',
                                                                   'force',
                                                                   'nojava',
                                                                   'nodotnet',
                                                                   'dotnet-key=',
                                                                   'assembly-version=',
                                                                   'githash',
                                                                   'nopython',
                                                                   'julia',
                                                                   'arm64'
                                                                   ])
    for opt, arg in options:
        if opt in ('-b', '--build'):
            if arg == 'src':
                raise MKException('The src directory should not be used to host the Makefile')
            path = arg
        elif opt in ('-s', '--silent'):
            set_verbose(False)
        elif opt in ('-h', '--help'):
            display_help()
        elif opt in ('-f', '--force'):
            FORCE_MK = True
        elif opt == '--nodotnet':
            DOTNET_CORE_ENABLED = False
        elif opt == '--assembly-version':
            ASSEMBLY_VERSION = arg
        elif opt == '--nopython':
            PYTHON_ENABLED = False
        elif opt == '--dotnet-key':
            DOTNET_KEY_FILE = arg
        elif opt == '--nojava':
            JAVA_ENABLED = False
        elif opt == '--julia':
            JULIA_ENABLED = True
        elif opt == '--githash':
            GIT_HASH = True
        elif opt == '--arm64':
            ARM64 = True
        else:
            raise MKException("Invalid command line option '%s'" % opt)
    set_build_dir(path)

def check_output(cmd):
    out = subprocess.Popen(cmd, stdout=subprocess.PIPE).communicate()[0]
    if out != None:
        enc = sys.getdefaultencoding()
        if enc != None: return out.decode(enc).rstrip('\r\n')
        else: return out.rstrip('\r\n')
    else:
        return ""

def get_git_hash():
    try:
        branch = check_output(['git', 'rev-parse', '--abbrev-ref', 'HEAD'])
        r = check_output(['git', 'show-ref', '--abbrev=12', 'refs/heads/%s' % branch])
    except:
        raise MKException("Failed to retrieve git hash")
    ls = r.split(' ')
    if len(ls) != 2:
        raise MKException("Unexpected git output " + r)
    return ls[0]

# Create a build directory using CMake
def mk_build_dir():
    build_path = get_build_dir()
    if not os.path.exists(build_path) or FORCE_MK:
        mk_dir(build_path)
        cmds = []
        cmds.append(f"cd {build_path}")
        cmd = []
        cmd.append("cmake -S .")
        if DOTNET_CORE_ENABLED:
            cmd.append(' -DZ3_BUILD_DOTNET_BINDINGS=ON')
        if JAVA_ENABLED:
            cmd.append(' -DZ3_BUILD_JAVA_BINDINGS=ON')
            cmd.append(' -DZ3_INSTALL_JAVA_BINDINGS=ON')
            cmd.append(' -DZ3_JAVA_JAR_INSTALLDIR=java')
            cmd.append(' -DZ3_JAVA_JNI_LIB_INSTALLDIR=bin/java')
        if PYTHON_ENABLED:
            cmd.append(' -DZ3_BUILD_PYTHON_BINDINGS=ON')
            cmd.append(' -DZ3_INSTALL_PYTHON_BINDINGS=ON')
            cmd.append(' -DCMAKE_INSTALL_PYTHON_PKG_DIR=bin/python')
        if JULIA_ENABLED:
            cmd.append(' -DZ3_BUILD_JULIA_BINDINGS=ON')
            cmd.append(' -DZ3_INSTALL_JULIA_BINDINGS=ON')
        if GIT_HASH:
            git_hash = get_git_hash()
            cmd.append(' -DGIT_HASH=' + git_hash)
        cmd.append(' -DZ3_USE_LIB_GMP=OFF')
        cmd.append(' -DZ3_BUILD_LIBZ3_SHARED=ON')
        cmd.append(' -DCMAKE_BUILD_TYPE=RelWithDebInfo')
        cmd.append(' -DCMAKE_INSTALL_PREFIX=' + get_build_dist_path())
        cmd.append(' -G "Ninja"')
        cmd.append(' ..\n')
        cmds.append("".join(cmd))
        print("CMAKE commands:", cmds)
        sys.stdout.flush()
        if exec_cmds(cmds) != 0:
            raise MKException("failed to run commands")

def exec_cmds(cmds):
    cmd_file = 'z3_tmp.sh'
    f = open(cmd_file, 'w')
    for cmd in cmds:
        f.write(cmd)
        f.write('\n')
    f.close()
    res = 0
    try:
        res = subprocess.call(['sh', cmd_file])
    except:
        res = 1
    try:
        os.remove(cmd_file)
    except:
        pass
    return res

def build_z3():
    if is_verbose():
        print("build z3")
    build_dir = get_build_dir()
    cmds = []
    cmds.append('cd %s' % build_dir)
    cmds.append('ninja install')
    if exec_cmds(cmds) != 0:
        raise MKException("Failed to make z3")

def mk_zip():
    build_dist = get_build_dist_path()
    dist_name = get_z3_name()
    old = os.getcwd()
    try:
        if is_verbose():
            print("dist path", build_dist)
        mk_dir(build_dist)
        zfname = '%s.zip' % dist_name
        zipout = zipfile.ZipFile(zfname, 'w', zipfile.ZIP_DEFLATED)
        os.chdir(get_build_dist())
        for root, dirs, files in os.walk("."):
            for f in files:
                if is_verbose():
                    print("adding ", os.path.join(root, f))
                zipout.write(os.path.join(root, f))
        if is_verbose():
            print("Generated '%s'" % zfname)
    except:
        pass
    os.chdir(old)

def cp_license():
    if is_verbose():
        print("copy licence")
    path = get_build_dist_path()
    mk_dir(path)
    shutil.copy("LICENSE.txt", path)

# Entry point
def main():
    parse_options()
    mk_build_dir()
    build_z3()
    cp_license()
    mk_zip()

main()
