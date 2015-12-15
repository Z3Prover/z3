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
DOTNET_ENABLED=True
JAVA_ENABLED=True
GIT_HASH=False

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
    BUILD_DIR = path
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
    print("  --nojava                      do not include Java bindings in the binary distribution files.")
    print("  --githash                     include git hash in the Zip file.")
    exit(0)

# Parse configuration option for mk_make script
def parse_options():
    global FORCE_MK, JAVA_ENABLED, GIT_HASH
    path = BUILD_DIR
    options, remainder = getopt.gnu_getopt(sys.argv[1:], 'b:hsf', ['build=', 
                                                                   'help',
                                                                   'silent',
                                                                   'force',
                                                                   'nojava',
                                                                   'nodotnet',
                                                                   'githash'
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
            DOTNET_ENABLED = False
        elif opt == '--nojava':
            JAVA_ENABLED = False
        elif opt == '--githash':
            GIT_HASH = True
        else:
            raise MKException("Invalid command line option '%s'" % opt)
    set_build_dir(path)

# Check whether build directory already exists or not
def check_build_dir(path):
    return os.path.exists(path) and os.path.exists(os.path.join(path, 'Makefile'))

# Create a build directory using mk_make.py
def mk_build_dir(path, x64):
    if not check_build_dir(path) or FORCE_MK:
        opts = ["python", os.path.join('scripts', 'mk_make.py'), "--parallel=24", "-b", path]
        if DOTNET_ENABLED:
            opts.append('--dotnet')
        if JAVA_ENABLED:
            opts.append('--java')
        if x64:
            opts.append('-x')
        if GIT_HASH:
            opts.append('--githash=%s' % mk_util.git_hash())
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
def mk_z3_core(x64):
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

def mk_z3():
    mk_z3_core(False)
    mk_z3_core(True)

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

def mk_dist_dir_core(x64):
    if x64:
        platform = "x64"
        build_path = BUILD_X64_DIR
    else:
        platform = "x86"
        build_path = BUILD_X86_DIR
    dist_path = os.path.join(DIST_DIR, get_z3_name(x64))
    mk_dir(dist_path)
    mk_util.DOTNET_ENABLED = DOTNET_ENABLED
    mk_util.JAVA_ENABLED = JAVA_ENABLED
    mk_win_dist(build_path, dist_path)
    if is_verbose():
        print("Generated %s distribution folder at '%s'" % (platform, dist_path))

def mk_dist_dir():
    mk_dist_dir_core(False)
    mk_dist_dir_core(True)

def get_dist_path(x64):
    return get_z3_name(x64)

def mk_zip_core(x64):
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
def mk_zip():
    mk_zip_core(False)
    mk_zip_core(True)


VS_RUNTIME_PATS = [re.compile('vcomp.*\.dll'),
                   re.compile('msvcp.*\.dll'),
                   re.compile('msvcr.*\.dll')]

VS_RUNTIME_FILES = []
                              
def cp_vs_runtime_visitor(pattern, dir, files):
    global VS_RUNTIME_FILES
    for filename in files:
        for pat in VS_RUNTIME_PATS:
            if pat.match(filename):
                if fnmatch(filename, pattern):
                    fname = os.path.join(dir, filename)
                    if not os.path.isdir(fname):
                        VS_RUNTIME_FILES.append(fname)
                break

# Copy Visual Studio Runtime libraries
def cp_vs_runtime_core(x64):
    global VS_RUNTIME_FILES
    if x64:
        platform = "x64"
        
    else:
        platform = "x86"
    vcdir = os.environ['VCINSTALLDIR']
    path  = '%sredist\\%s' % (vcdir, platform)
    VS_RUNTIME_FILES = []
    os.walk(path, cp_vs_runtime_visitor, '*.dll')
    bin_dist_path = os.path.join(DIST_DIR, get_dist_path(x64), 'bin')
    for f in VS_RUNTIME_FILES:
        shutil.copy(f, bin_dist_path)
        if is_verbose():
            print("Copied '%s' to '%s'" % (f, bin_dist_path))

def cp_vs_runtime():
    cp_vs_runtime_core(True)
    cp_vs_runtime_core(False)

def cp_license():
    shutil.copy("LICENSE.txt", os.path.join(DIST_DIR, get_dist_path(True)))
    shutil.copy("LICENSE.txt", os.path.join(DIST_DIR, get_dist_path(False)))

# Entry point
def main():
    if os.name != 'nt':
        raise MKException("This script is for Windows only")
    parse_options()
    check_vc_cmd_prompt()
    mk_build_dirs()
    mk_z3()
    init_project_def()
    mk_dist_dir()
    cp_license()
    cp_vs_runtime()
    mk_zip()

main()

