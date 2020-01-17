# 
# Copyright (c) 2018 Microsoft Corporation
#

# 1. copy over dlls
# 2. copy over libz3.dll for the different architectures
# 3. copy over Microsoft.Z3.dll from suitable distribution
# 4. copy nuspec file from packages
# 5. call nuget pack
# 6. sign package

import json
import os
import zipfile
import sys
import os.path
import shutil
import subprocess

def mk_dir(d):
    if not os.path.exists(d):
        os.makedirs(d)


os_info = {"z64-ubuntu-14" : ('so', 'ubuntu.14.04-x64'),
           'ubuntu-16' : ('so', 'ubuntu-x64'),
           'x64-win' : ('dll', 'win-x64'),
# Skip x86 as I can't get dotnet build to produce AnyCPU TargetPlatform           
#          'x86-win' : ('dll', 'win-x86'),
           'osx' : ('dylib', 'macos'),
           'debian' : ('so', 'debian.8-x64') }

def classify_package(f):
    for os_name in os_info:
        if os_name in f:
            ext, dst = os_info[os_name]
            return os_name, f[:-4], ext, dst
    return None


def unpack(packages):
    # unzip files in packages
    # out
    # +- runtimes
    #    +- win-x64
    #    +- win-x86
    #    +- ubuntu.16.04-x64
    #    +- ubuntu.14.04-x64
    #    +- debian.8-x64
    #    +- macos
    # +
    for f in os.listdir(packages):
        print(f)
        if f.endswith(".zip") and classify_package(f):
            os_name, package_dir, ext, dst = classify_package(f)
            path = os.path.abspath(os.path.join(packages, f))
            zip_ref = zipfile.ZipFile(path, 'r')
            zip_ref.extract("%s/bin/libz3.%s" % (package_dir, ext), "tmp")
            mk_dir("out/runtimes/%s/native" % dst)
            shutil.move("tmp/%s/bin/libz3.%s" % (package_dir, ext), "out/runtimes/%s/native/." % dst)
            if "x64-win" in f:
                mk_dir("out/lib/netstandard1.4/")
                for b in ["Microsoft.Z3.dll"]:
                    zip_ref.extract("%s/bin/%s" % (package_dir, b), "tmp")
                    shutil.move("tmp/%s/bin/%s" % (package_dir, b), "out/lib/netstandard1.4/%s" % b)

def mk_targets(source_root):
    mk_dir("out/build")
    shutil.copy("{}/src/api/dotnet/Microsoft.Z3.targets.in".format(source_root), "out/build/Microsoft.Z3.x64.targets")

def mk_icon(source_root):
    mk_dir("out/content")
    shutil.copy("{}/resources/icon.jpg".format(source_root), "out/content/icon.jpg")

def mk_license(source_root):
    mk_dir("out/content")
    shutil.copy("{}/LICENSE.txt".format(source_root), "out/content/LICENSE.txt")
    
def create_nuget_spec(version, repo, branch, commit):
    contents = """<?xml version="1.0" encoding="utf-8"?>
<package xmlns="http://schemas.microsoft.com/packaging/2010/07/nuspec.xsd">
    <metadata>
        <id>Microsoft.Z3.x64</id>
        <version>{0}</version>
        <authors>Microsoft</authors>
        <description>
Z3 is a satisfiability modulo theories solver from Microsoft Research.

Linux Dependencies:
    libgomp.so.1 installed    
        </description>
        <copyright>&#169; Microsoft Corporation. All rights reserved.</copyright>
        <tags>smt constraint solver theorem prover</tags>
        <icon>content/icon.jpg</icon>
        <projectUrl>https://github.com/Z3Prover/z3</projectUrl>
        <license type="file">content/LICENSE.txt</license>
        <repository type="git" url="{1}" branch="{2}" commit="{3}" />
        <requireLicenseAcceptance>true</requireLicenseAcceptance>
        <language>en</language>
        <dependencies>
            <group targetFramework=".NETStandard1.4" />
        </dependencies>
    </metadata>
</package>""".format(version, repo, branch, commit)
    print(contents)
    with open("out/Microsoft.Z3.x64.nuspec", 'w') as f:
        f.write(contents)
        
def main():
    packages = sys.argv[1]
    version = sys.argv[2]
    repo = sys.argv[3]
    branch = sys.argv[4]
    commit = sys.argv[5]
    source_root = sys.argv[6]
    print(packages)
    mk_dir(packages)
    unpack(packages)
    mk_targets(source_root)
    mk_icon(source_root)
    mk_license(source_root)
    create_nuget_spec(version, repo, branch, commit)

main()
