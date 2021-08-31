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


os_info = {"z64-ubuntu-14" : ('so', 'linux-x64'),
           'ubuntu-18' : ('so', 'linux-x64'),
           'ubuntu-20' : ('so', 'linux-x64'),
           'glibc-2.31' : ('so', 'linux-x64'),
           'x64-win' : ('dll', 'win-x64'),
           'x86-win' : ('dll', 'win-x86'),
           'osx' : ('dylib', 'osx-x64'),
           'debian' : ('so', 'linux-x64') }

def classify_package(f):
    for os_name in os_info:
        if os_name in f:
            ext, dst = os_info[os_name]
            return os_name, f[:-4], ext, dst
    print("Could not classify", f)
    return None

def replace(src, dst):
    try:
        os.remove(dst)
    except:
        shutil.move(src, dst)
    
def unpack(packages, symbols):
    # unzip files in packages
    # out
    # +- runtimes
    #    +- win-x64
    #    +- win-x86
    #    +- linux-x64
    #    +- osx-x64
    # +
    tmp = "tmp" if not symbols else "tmpsym"
    for f in os.listdir(packages):
        print(f)
        if f.endswith(".zip") and classify_package(f):
            os_name, package_dir, ext, dst = classify_package(f)
            path = os.path.abspath(os.path.join(packages, f))
            zip_ref = zipfile.ZipFile(path, 'r')
            zip_ref.extract(f"{package_dir}/bin/libz3.{ext}", f"{tmp}")
            mk_dir(f"out/runtimes/{dst}/native")
            replace(f"{tmp}/{package_dir}/bin/libz3.{ext}", f"out/runtimes/{dst}/native/libz3.{ext}")            
            if "x64-win" in f:
                mk_dir("out/lib/netstandard1.4/")
                if symbols:
                    zip_ref.extract(f"{package_dir}/bin/libz3.pdb", f"{tmp}")
                    replace(f"{tmp}/{package_dir}/bin/libz3.pdb", f"out/runtimes/{dst}/native/libz3.pdb") 
                files = ["Microsoft.Z3.dll"]                
                if symbols:
                    files += ["Microsoft.Z3.pdb", "Microsoft.Z3.xml"]
                for b in files:
                    zip_ref.extract(f"{package_dir}/bin/{b}", f"{tmp}")
                    replace(f"{tmp}/{package_dir}/bin/{b}", f"out/lib/netstandard1.4/{b}")

def mk_targets(source_root):
    mk_dir("out/build")
    shutil.copy(f"{source_root}/src/api/dotnet/Microsoft.Z3.targets.in", "out/build/Microsoft.Z3.targets")

def mk_icon(source_root):
    mk_dir("out/content")
    shutil.copy(f"{source_root}/resources/icon.jpg", "out/content/icon.jpg")

    
def create_nuget_spec(version, repo, branch, commit, symbols):
    contents = """<?xml version="1.0" encoding="utf-8"?>
<package xmlns="http://schemas.microsoft.com/packaging/2010/07/nuspec.xsd">
    <metadata>
        <id>Microsoft.Z3</id>
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
        <license type="expression">MIT</license>
        <repository type="git" url="{1}" branch="{2}" commit="{3}" />
        <requireLicenseAcceptance>true</requireLicenseAcceptance>
        <language>en</language>
        <dependencies>
            <group targetFramework=".NETStandard1.4" />
        </dependencies>
    </metadata>
</package>""".format(version, repo, branch, commit)
    print(contents)
    sym = "sym." if symbols else ""
    file = f"out/Microsoft.Z3.{sym}nuspec"
    print(file)
    with open(file, 'w') as f:
        f.write(contents)
        
def main():
    packages = sys.argv[1]
    version = sys.argv[2]
    repo = sys.argv[3]
    branch = sys.argv[4]
    commit = sys.argv[5]
    source_root = sys.argv[6]
    symbols = False
    if len(sys.argv) > 7:
        print(sys.argv[7])
    if len(sys.argv) > 7 and "symbols" == sys.argv[7]:
        symbols = True
    print(packages)
    mk_dir(packages)
    unpack(packages, symbols)
    mk_targets(source_root)
    mk_icon(source_root)
    create_nuget_spec(version, repo, branch, commit, symbols)

main()
