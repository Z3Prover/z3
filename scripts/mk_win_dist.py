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

BUILD_DIR='build-dist'
BUILD_X64_DIR='build-dist/x64'
BUILD_X86_DIR='build-dist/x86'
VERBOSE=True
DIST_DIR='dist'

def set_verbose(flag):
    global VERBOSE
    VERBOSE = flag

def is_verbose():
    return VERBOSE

def mk_dir(d):
    if not os.path.exists(d):
        os.makedirs(d)

def set_build_dir(path):
    global BUILD_DIR
    BUILD_DIR = path
    BUILD_X86_DIR = '%s/x86' % path
    BUILD_X64_DIR = '%s/x64' % path
    mk_dir(BUILD_X86_DIR)
    mk_dir(BUILD_X64_DIR)

def display_help():
    print "mk_win_dist.py: Z3 Windows distribution generator\n"
    print "This script generates the zip files containing executables, dlls, header files for Windows."
    print "It must be executed from the Z3 root directory."
    print "\nOptions:"
    print "  -h, --help                    display this message."
    print "  -s, --silent                  do not print verbose messages."
    print "  -b <sudir>, --build=<subdir>  subdirectory where x86 and x64 Z3 versions will be built (default: build-dist)."
    exit(0)

# Parse configuration option for mk_make script
def parse_options():
    path = BUILD_DIR
    options, remainder = getopt.gnu_getopt(sys.argv[1:], 'b:hs', ['build=', 
                                                                  'help',
                                                                  'silent',
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
        else:
            raise MKException("Invalid command line option '%s'" % opt)
    set_build_dir(path)

# Check whether build directory already exists or not
def check_build_dir(path):
    return os.path.exists(path) and os.path.exists('%s/Makefile' % path)

# Create a build directory using mk_make.py
def mk_build_dir(path, x64):
    if not check_build_dir(path):
        opts = ["python", "scripts/mk_make.py", "-b", path]
        if x64:
            opts.append('-x')
        if subprocess.call(opts) != 0:
            raise MKException("Failed to generate build directory at '%s'" % path)
    
# Create build directories
def mk_build_dirs():
    mk_build_dir(BUILD_X86_DIR, False)
    mk_build_dir(BUILD_X64_DIR, True)

# Check if on Visual Studio command prompt
def check_vc_cmd_prompt():
    try:
        subprocess.call(['cl'], stdin=subprocess.PIPE, stderr=subprocess.PIPE)
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
        cmds.append('"call %VCINSTALLDIR%vcvarsall.bat" x86')
        cmds.append('cd %s' % BUILD_X86_DIR)
    cmds.append('nmake')
    if exec_cmds(cmds) != 0:
        raise MKException("Failed to make z3, x64: %s" % x64)

def mk_z3():
    mk_z3_core(False)
    mk_z3_core(True)

def mk_dist_dir_core(x64):
    major, minor, build, revision = get_version()
    if x64:
        platform = "x64"
        build_path = BUILD_X64_DIR
    else:
        platform = "x86"
        build_path = BUILD_X86_DIR
    dist_path = '%s/z3-%s.%s.%s-%s' % (DIST_DIR, major, minor, build, platform)
    mk_dir(dist_path)
    mk_win_dist(build_path, dist_path)
    if is_verbose():
        print "Generated %s distribution folder at '%s'" % (platform, dist_path)

def mk_dist_dir():
    mk_dist_dir_core(False)
    mk_dist_dir_core(True)

ZIPOUT = None

def mk_zip_visitor(pattern, dir, files):
    for filename in files:
        if fnmatch(filename, pattern):
            fname = os.path.join(dir, filename)
            if not os.path.isdir(fname):
                ZIPOUT.write(fname)

def mk_zip_core(x64):
    global ZIPOUT
    major, minor, build, revision = get_version()
    if x64:
        platform = "x64"
    else:
        platform = "x86"
    dist_path = 'z3-%s.%s.%s-%s' % (major, minor, build, platform)
    old = os.getcwd()
    try:
        os.chdir(DIST_DIR)
        zfname = '%s.zip' % dist_path
        ZIPOUT = zipfile.ZipFile(zfname, 'w')
        os.path.walk(dist_path, mk_zip_visitor, '*')
        if is_verbose():
            print "Generated '%s'" % zfname
    except:
        pass
    ZIPOUT = None
    os.chdir(old)

# Create a zip file for each platform
def mk_zip():
    mk_zip_core(False)
    mk_zip_core(True)

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
    mk_zip()

main()

