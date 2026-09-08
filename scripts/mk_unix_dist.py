############################################
# Copyright (c) 2013 Microsoft Corporation
#
# Scripts for automatically generating
# Linux/OSX/BSD distribution zip files.
#
# Author: Leonardo de Moura (leonardo)
############################################

import os
import platform
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
ARCH = None
OS_NAME = None
MAKEJOBS = getenv("MAKEJOBS", "24")

def host_arch():
    machine = platform.machine().lower()
    if machine in ('arm64', 'aarch64'):
        return 'arm64'
    else:
        return 'x64'

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

def get_os_name():
    # Note that the platform/os names this function returns have to
    # work together with mk_nuget_task.py's package classification.
    if OS_NAME is not None:
        return OS_NAME
    basic = os.uname()[0].lower()
    if basic == 'linux':
        if ARCH == 'arm64' and host_arch() == 'x64':
            # cross-compiling: platform.libc_ver() reports the host's libc,
            # not the target's, so shell out to the cross toolchain's ldd instead
            # example: 'ldd (GNU) 2.34'
            lines = subprocess.check_output(["ldd", "--version"]).decode('ascii')
            first_line = lines.split("\n")[0]
            ldd_version = first_line.split()[-1]
            dist = ('glibc', ldd_version)
        else:
            dist = platform.libc_ver()
        if len(dist) == 2 and len(dist[0]) > 0 and len(dist[1]) > 0:
            return '%s-%s' % (dist[0].lower(), dist[1].lower())
        else:
            return basic
    elif basic == 'darwin':
        ver = platform.mac_ver()
        if len(ver) == 3 and len(ver[0]) > 0:
            return 'osx-%s' % ver[0]
        else:
            return 'osx'
    elif basic == 'freebsd':
        ver = platform.version()
        idx1 = ver.find(' ')
        idx2 = ver.find('-')
        if idx1 < 0 or idx2 < 0 or idx1 >= idx2:
            return basic
        else:
            return 'freebsd-%s' % ver[(idx1+1):idx2]
    else:
        return basic

def get_z3_name():
    version = "4"
    if ASSEMBLY_VERSION:
        version = ASSEMBLY_VERSION
    print("Assembly version:", version)
    platform_name = ARCH if ARCH is not None else host_arch()
    osname = get_os_name()
    if GIT_HASH:
        return 'z3-%s.%s-%s-%s' % (version, get_git_hash(), platform_name, osname)
    else:
        return 'z3-%s-%s-%s' % (version, platform_name, osname)

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
    print("mk_unix_dist.py: Z3 Unix distribution generator\n")
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
    print("  --arch=<arch>                 set architecture (arm64 or x64) to force cross-compilation")
    print("  --os=<os>                     set OS version.")
    exit(0)

# Parse configuration option for mk_make script
def parse_options():
    global FORCE_MK, JAVA_ENABLED, JULIA_ENABLED, GIT_HASH, DOTNET_CORE_ENABLED, DOTNET_KEY_FILE, ASSEMBLY_VERSION, PYTHON_ENABLED, ARCH, OS_NAME
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
                                                                   'arch=',
                                                                   'os='
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
        elif opt == '--arch':
            if arg not in ('arm64', 'x64'):
                raise MKException("Invalid architecture directive '%s'. Legal directives: arm64, x64" % arg)
            ARCH = arg
        elif opt == '--os':
            OS_NAME = arg
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

def check_build_dir(path):
    return os.path.exists(path) and os.path.exists(os.path.join(path, 'CMakeCache.txt'))

# Create a build directory using CMake
def mk_build_dir():
    build_path = get_build_dir()
    if not check_build_dir(build_path) or FORCE_MK:
        mk_dir(build_path)
        cmds = []
        cmd = []
        cmd.append(f'cmake -G "Ninja" -S . -B "{build_path}"')
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
        if ARCH is not None and ARCH != host_arch():
            if platform.system() == 'Linux' and ARCH == 'arm64':
                # cross-compiling on a Linux x64 host for arm64, using the
                # ARM GNU toolchain (expected to already be on PATH)
                cmd.append(' -DCMAKE_C_COMPILER=aarch64-none-linux-gnu-gcc')
                cmd.append(' -DCMAKE_CXX_COMPILER=aarch64-none-linux-gnu-g++')
            elif platform.system() == 'Darwin' and ARCH == 'x64':
                # cross-compiling on a macOS arm64 host for x64
                cmd.append(' -DCMAKE_OSX_ARCHITECTURES=x86_64')
        cmd.append(' -DZ3_USE_LIB_GMP=OFF')
        cmd.append(' -DBUILD_SHARED_LIBS=ON')
        cmd.append(' -DCMAKE_BUILD_TYPE=RelWithDebInfo')
        # mk_nuget_task.py expects libz3.{so,dylib} directly under bin/, matching
        # the flat layout the legacy dist scripts always produced. Overriding
        # CMAKE_INSTALL_LIBDIR (scoped to this throwaway packaging build tree
        # only) installs it there directly, with no post-install copying needed.
        cmd.append(' -DCMAKE_INSTALL_LIBDIR=bin')
        cmd.append(' -DCMAKE_INSTALL_PREFIX=' + get_build_dist_path())
        cmd.append('\n')
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
    cmds = ['cmake --build "%s" --target install' % build_dir]
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
        mk_dir(DIST_DIR)
        zfname = os.path.join(DIST_DIR, '%s.zip' % dist_name)
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

# The shared library already installs directly under bin/ (CMAKE_INSTALL_LIBDIR
# is overridden to "bin" in mk_build_dir()). The Java JNI library, when enabled,
# still lands one level down at bin/java/ (Z3_JAVA_JNI_LIB_INSTALLDIR), so flatten
# that to match the flat layout mk_nuget_task.py expects, mirroring mk_win_dist.py's
# cp_into_bin().
def cp_into_bin():
    if not JAVA_ENABLED:
        return
    if is_verbose():
        print("copy java")
    bin_dir = os.path.join(get_build_dist_path(), "bin")
    java_dir = os.path.join(bin_dir, "java")
    if os.path.exists(java_dir):
        for file in os.listdir(java_dir):
            shutil.copy2(os.path.join(java_dir, file), os.path.join(bin_dir, file))
        shutil.rmtree(java_dir)

# Entry point
def main():
    parse_options()
    mk_build_dir()
    build_z3()
    cp_license()
    cp_into_bin()
    mk_zip()

main()
