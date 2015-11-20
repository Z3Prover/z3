############################################
# Copyright (c) 2013 Microsoft Corporation
# 
# Scripts for automatically generating 
# Linux/OSX/BSD distribution zip files.
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
VERBOSE=True
DIST_DIR='dist'
FORCE_MK=False
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
    global BUILD_DIR
    BUILD_DIR = path
    mk_dir(BUILD_DIR)

def display_help():
    print("mk_unix_dist.py: Z3 Linux/OSX/BSD distribution generator\n")
    print("This script generates the zip files containing executables, shared objects, header files for Linux/OSX/BSD.")
    print("It must be executed from the Z3 root directory.")
    print("\nOptions:")
    print("  -h, --help                    display this message.")
    print("  -s, --silent                  do not print verbose messages.")
    print("  -b <sudir>, --build=<subdir>  subdirectory where x86 and x64 Z3 versions will be built (default: build-dist).")
    print("  -f, --force                   force script to regenerate Makefiles.")
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
def mk_build_dir(path):
    if not check_build_dir(path) or FORCE_MK:
        opts = ["python", os.path.join('scripts', 'mk_make.py'), "-b", path, "--static"]
        if JAVA_ENABLED:
            opts.append('--java')
        if GIT_HASH:
            opts.append('--githash=%s' % mk_util.git_hash())
        if subprocess.call(opts) != 0:
            raise MKException("Failed to generate build directory at '%s'" % path)
    
# Create build directories
def mk_build_dirs():
    mk_build_dir(BUILD_DIR)

class cd:
    def __init__(self, newPath):
        self.newPath = newPath

    def __enter__(self):
        self.savedPath = os.getcwd()
        os.chdir(self.newPath)

    def __exit__(self, etype, value, traceback):
        os.chdir(self.savedPath)

def mk_z3():
    with cd(BUILD_DIR):
        try:
            return subprocess.call(['make', '-j', '8'])
        except:
            return 1

def get_os_name():
    import platform
    basic = os.uname()[0].lower()
    if basic == 'linux':
        dist = platform.linux_distribution()
        if len(dist) == 3 and len(dist[0]) > 0 and len(dist[1]) > 0:
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
    major, minor, build, revision = get_version()
    if sys.maxsize >= 2**32:
        platform = "x64"
    else:
        platform = "x86"
    osname = get_os_name()
    if GIT_HASH:
        return 'z3-%s.%s.%s.%s-%s-%s' % (major, minor, build, mk_util.git_hash(), platform, osname)
    else:
        return 'z3-%s.%s.%s-%s-%s' % (major, minor, build, platform, osname)

def mk_dist_dir():
    build_path = BUILD_DIR
    dist_path = os.path.join(DIST_DIR, get_z3_name())
    mk_dir(dist_path)
    if JAVA_ENABLED:
        # HACK: Propagate JAVA_ENABLED flag to mk_util
        # TODO: fix this hack
        mk_util.JAVA_ENABLED = JAVA_ENABLED
    mk_unix_dist(build_path, dist_path)
    if is_verbose():
        print("Generated distribution folder at '%s'" % dist_path)

def get_dist_path():
    return get_z3_name()

def mk_zip():
    dist_path = get_dist_path()
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

def cp_license():
    shutil.copy("LICENSE.txt", os.path.join(DIST_DIR, get_dist_path()))

# Entry point
def main():
    parse_options()
    mk_build_dirs()
    mk_z3()
    init_project_def()
    mk_dist_dir()
    cp_license()
    mk_zip()

main()

