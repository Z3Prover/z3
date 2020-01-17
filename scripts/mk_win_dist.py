############################################
# Copyright (c) 2012 Microsoft Corporation
#
# Scripts for automatically generating
# Window distribution zip files.
#
# Author: Leonardo de Moura (leonardo)
############################################
import os
import glob
import re
import getopt
import sys
import shutil
import subprocess
import zipfile
from mk_exception import *
from mk_project import *
import mk_util

BUILD_DIR='build-dist'
BUILD_X64_DIR=os.path.join('build-dist', 'x64')
BUILD_X86_DIR=os.path.join('build-dist', 'x86')
VERBOSE=True
DIST_DIR='dist'
FORCE_MK=False
DOTNET_CORE_ENABLED=True
DOTNET_KEY_FILE=None
JAVA_ENABLED=True
ZIP_BUILD_OUTPUTS=False
GIT_HASH=False
PYTHON_ENABLED=True
X86ONLY=False
X64ONLY=False
MAKEJOBS=getenv("MAKEJOBS", "24")

def set_verbose(flag):
    global VERBOSE
    VERBOSE = flag

def is_verbose():
    return VERBOSE

def mk_dir(d):
    if not os.path.exists(d):
        os.makedirs(d)

def set_build_dir(path):
    global BUILD_DIR, BUILD_X86_DIR, BUILD_X64_DIR
    BUILD_DIR = mk_util.norm_path(path)
    BUILD_X86_DIR = os.path.join(path, 'x86')
    BUILD_X64_DIR = os.path.join(path, 'x64')
    mk_dir(BUILD_X86_DIR)
    mk_dir(BUILD_X64_DIR)

def display_help():
    print("mk_win_dist.py: Z3 Windows distribution generator\n")
    print("This script generates the zip files containing executables, dlls, header files for Windows.")
    print("It must be executed from the Z3 root directory.")
    print("\nOptions:")
    print("  -h, --help                    display this message.")
    print("  -s, --silent                  do not print verbose messages.")
    print("  -b <sudir>, --build=<subdir>  subdirectory where x86 and x64 Z3 versions will be built (default: build-dist).")
    print("  -f, --force                   force script to regenerate Makefiles.")
    print("  --nodotnet                    do not include .NET bindings in the binary distribution files.")
    print("  --dotnet-key=<file>           strongname sign the .NET assembly with the private key in <file>.")
    print("  --nojava                      do not include Java bindings in the binary distribution files.")
    print("  --nopython                    do not include Python bindings in the binary distribution files.")
    print("  --zip                         package build outputs in zip file.")
    print("  --githash                     include git hash in the Zip file.")
    print("  --x86-only                    x86 dist only.")
    print("  --x64-only                    x64 dist only.")
    exit(0)

# Parse configuration option for mk_make script
def parse_options():
    global FORCE_MK, JAVA_ENABLED, ZIP_BUILD_OUTPUTS, GIT_HASH, DOTNET_CORE_ENABLED, DOTNET_KEY_FILE, PYTHON_ENABLED, X86ONLY, X64ONLY
    path = BUILD_DIR
    options, remainder = getopt.gnu_getopt(sys.argv[1:], 'b:hsf', ['build=',
                                                                   'help',
                                                                   'silent',
                                                                   'force',
                                                                   'nojava',
                                                                   'nodotnet',
                                                                   'dotnet-key=',
                                                                   'zip',
                                                                   'githash',
                                                                   'nopython',
                                                                   'x86-only',
                                                                   'x64-only'
                                                                   ])
    print(options)
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
        elif opt == '--nopython':
            PYTHON_ENABLED = False
        elif opt == '--dotnet-key':
            DOTNET_KEY_FILE = arg
        elif opt == '--nojava':
            JAVA_ENABLED = False
        elif opt == '--zip':
            ZIP_BUILD_OUTPUTS = True
        elif opt == '--githash':
            GIT_HASH = True
        elif opt == '--x86-only' and not X64ONLY:
            X86ONLY = True
        elif opt == '--x64-only' and not X86ONLY:
            X64ONLY = True
        else:
            raise MKException("Invalid command line option '%s'" % opt)
    set_build_dir(path)

# Check whether build directory already exists or not
def check_build_dir(path):
    return os.path.exists(path) and os.path.exists(os.path.join(path, 'Makefile'))

# Create a build directory using mk_make.py
def mk_build_dir(path, x64):
    if not check_build_dir(path) or FORCE_MK:
        parallel = '--parallel=' + MAKEJOBS
        opts = ["python", os.path.join('scripts', 'mk_make.py'), parallel, "-b", path]
        if DOTNET_CORE_ENABLED:
            opts.append('--dotnet')
            if not DOTNET_KEY_FILE is None:
                opts.append('--dotnet-key=' + DOTNET_KEY_FILE)
        if JAVA_ENABLED:
            opts.append('--java')
        if x64:
            opts.append('-x')
        if GIT_HASH:
            opts.append('--githash=%s' % mk_util.git_hash())
            opts.append('--git-describe')
        if PYTHON_ENABLED:
            opts.append('--python')
        if subprocess.call(opts) != 0:
            raise MKException("Failed to generate build directory at '%s'" % path)

# Create build directories
def mk_build_dirs():
    mk_build_dir(BUILD_X86_DIR, False)
    mk_build_dir(BUILD_X64_DIR, True)

# Check if on Visual Studio command prompt
def check_vc_cmd_prompt():
    try:
        DEVNULL = open(os.devnull, 'wb')
        subprocess.call(['cl'], stdout=DEVNULL, stderr=DEVNULL)
    except:
        raise MKException("You must execute the mk_win_dist.py script on a Visual Studio Command Prompt")

def exec_cmds(cmds):
    cmd_file = 'z3_tmp.cmd'
    f = open(cmd_file, 'w')
    for cmd in cmds:
        f.write(cmd)
        f.write('\n')
    f.close()
    res = 0
    try:
        res = subprocess.call(cmd_file, shell=True)
    except:
        res = 1
    try:
        os.erase(cmd_file)
    except:
        pass
    return res

# Compile Z3 (if x64 == True, then it builds it in x64 mode).
def mk_z3(x64):
    cmds = []
    if x64:
        cmds.append('call "%VCINSTALLDIR%vcvarsall.bat" amd64')
        cmds.append('cd %s' % BUILD_X64_DIR)
    else:
        cmds.append('call "%VCINSTALLDIR%vcvarsall.bat" x86')
        cmds.append('cd %s' % BUILD_X86_DIR)
    cmds.append('nmake')
    if exec_cmds(cmds) != 0:
        raise MKException("Failed to make z3, x64: %s" % x64)

def mk_z3s():
    mk_z3(False)
    mk_z3(True)

def get_z3_name(x64):
    major, minor, build, revision = get_version()
    if x64:
        platform = "x64"
    else:
        platform = "x86"
    if GIT_HASH:
        return 'z3-%s.%s.%s.%s-%s-win' % (major, minor, build, mk_util.git_hash(), platform)
    else:
        return 'z3-%s.%s.%s-%s-win' % (major, minor, build, platform)

def mk_dist_dir(x64):
    if x64:
        platform = "x64"
        build_path = BUILD_X64_DIR
    else:
        platform = "x86"
        build_path = BUILD_X86_DIR
    dist_path = os.path.join(DIST_DIR, get_z3_name(x64))
    mk_dir(dist_path)
    mk_util.DOTNET_CORE_ENABLED = True
    mk_util.DOTNET_KEY_FILE = DOTNET_KEY_FILE
    mk_util.JAVA_ENABLED = JAVA_ENABLED
    mk_util.PYTHON_ENABLED = PYTHON_ENABLED
    mk_win_dist(build_path, dist_path)
    if is_verbose():
        print("Generated %s distribution folder at '%s'" % (platform, dist_path))

def mk_dist_dirs():
    mk_dist_dir(False)
    mk_dist_dir(True)

def get_dist_path(x64):
    return get_z3_name(x64)

def mk_zip(x64):
    dist_path = get_dist_path(x64)
    old = os.getcwd()
    try:
        os.chdir(DIST_DIR)
        zfname = '%s.zip' % dist_path
        zipout = zipfile.ZipFile(zfname, 'w', zipfile.ZIP_DEFLATED)
        for root, dirs, files in os.walk(dist_path):
            for f in files:
                zipout.write(os.path.join(root, f))
        if is_verbose():
            print("Generated '%s'" % zfname)
    except:
        pass
    os.chdir(old)

# Create a zip file for each platform
def mk_zips():
    mk_zip(False)
    mk_zip(True)


VS_RUNTIME_PATS = [re.compile('vcomp.*\.dll'),
                   re.compile('msvcp.*\.dll'),
                   re.compile('msvcr.*\.dll')]

# Copy Visual Studio Runtime libraries
def cp_vs_runtime(x64):
    if x64:
        platform = "x64"
    else:
        platform = "x86"
    vcdir = os.environ['VCINSTALLDIR']
    path  = '%sredist' % vcdir
    vs_runtime_files = []
    print("Walking %s" % path)
    # Everything changes with every release of VS
    # Prior versions of VS had DLLs under "redist\x64"
    # There are now several variants of redistributables
    # The naming convention defies my understanding so 
    # we use a "check_root" filter to find some hopefully suitable
    # redistributable.
    def check_root(root):
        return platform in root and ("CRT" in root or "MP" in root) and "onecore" not in root and "debug" not in root
    for root, dirs, files in os.walk(path):
        for filename in files:
            if fnmatch(filename, '*.dll') and check_root(root):
                print("Checking %s %s" % (root, filename))
                for pat in VS_RUNTIME_PATS:
                    if pat.match(filename):
                        fname = os.path.join(root, filename)
                        if not os.path.isdir(fname):
                            vs_runtime_files.append(fname)
    if not vs_runtime_files:
        raise MKException("Did not find any runtime files to include")       
    bin_dist_path = os.path.join(DIST_DIR, get_dist_path(x64), 'bin')
    for f in vs_runtime_files:
        shutil.copy(f, bin_dist_path)
        if is_verbose():
            print("Copied '%s' to '%s'" % (f, bin_dist_path))

def cp_vs_runtimes():
    cp_vs_runtime(True)
    cp_vs_runtime(False)

def cp_license(x64):
    shutil.copy("LICENSE.txt", os.path.join(DIST_DIR, get_dist_path(x64)))

def cp_licenses():
    cp_license(True)
    cp_license(False)

# Entry point
def main():
    if os.name != 'nt':
        raise MKException("This script is for Windows only")

    parse_options()
    check_vc_cmd_prompt()

    if X86ONLY:
        mk_build_dir(BUILD_X86_DIR, False)
        mk_z3(False)
        init_project_def()
        mk_dist_dir(False)
        cp_license(False)
        cp_vs_runtime(False)
        if ZIP_BUILD_OUTPUTS:
            mk_zip(False)
    elif X64ONLY:
        mk_build_dir(BUILD_X64_DIR, True)
        mk_z3(True)
        init_project_def()
        mk_dist_dir(True)
        cp_license(True)
        cp_vs_runtime(True)
        if ZIP_BUILD_OUTPUTS:
            mk_zip(True)
    else:
        mk_build_dirs()
        mk_z3s()
        init_project_def()
        mk_dist_dirs()
        cp_licenses()
        cp_vs_runtimes()
        if ZIP_BUILD_OUTPUTS:
            mk_zips()

main()

