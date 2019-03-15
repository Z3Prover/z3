# 
# Copyright (c) 2018 Microsoft Corporation
#

# 1. download releases from github
# 2. copy over libz3.dll for the different architectures
# 3. copy over Microsoft.Z3.dll from suitable distribution
# 4. copy nuspec file from packages
# 5. call nuget pack
# 6. sign package

import json
import os
import urllib.request
import zipfile
import sys
import os.path
import shutil
import subprocess
import mk_util
import mk_project

release_data = json.loads(urllib.request.urlopen("https://api.github.com/repos/Z3Prover/z3/releases/latest").read().decode())
release_tag_name = release_data['tag_name']
release_tag_ref_data = json.loads(urllib.request.urlopen("https://api.github.com/repos/Z3Prover/z3/git/refs/tags/%s" % release_tag_name).read().decode())
release_tag_sha = release_tag_ref_data['object']['sha']
release_tag_data = json.loads(urllib.request.urlopen("https://api.github.com/repos/Z3Prover/z3/git/tags/%s" % release_tag_sha).read().decode())

release_version = release_tag_name[3:]
release_commit = release_tag_data['object']['sha']

print(release_version)

def mk_dir(d):
    if not os.path.exists(d):
        os.makedirs(d)

def download_installs():
    for asset in release_data['assets']:
        url = asset['browser_download_url']
        name = asset['name']
        print("Downloading ", url)
        sys.stdout.flush()
        urllib.request.urlretrieve(url, "packages/%s" % name)

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


def unpack():
    shutil.rmtree("out", ignore_errors=True)
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
    for f in os.listdir("packages"):
        print(f)
        if f.endswith(".zip") and classify_package(f):
            os_name, package_dir, ext, dst = classify_package(f)
            path = os.path.abspath(os.path.join("packages", f))
            zip_ref = zipfile.ZipFile(path, 'r')
            zip_ref.extract("%s/bin/libz3.%s" % (package_dir, ext), "tmp")
            mk_dir("out/runtimes/%s/native" % dst)
            shutil.move("tmp/%s/bin/libz3.%s" % (package_dir, ext), "out/runtimes/%s/native/." % dst, "/y")
            if "x64-win" in f:
                mk_dir("out/lib/netstandard1.4/")
                for b in ["Microsoft.Z3.dll"]:
                    zip_ref.extract("%s/bin/%s" % (package_dir, b), "tmp")
                    shutil.move("tmp/%s/bin/%s" % (package_dir, b), "out/lib/netstandard1.4/%s" % b)

def mk_targets():
    mk_dir("out/build")
    shutil.copy("../src/api/dotnet/Microsoft.Z3.targets.in", "out/build/Microsoft.Z3.targets")
    
def create_nuget_spec():
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
        <iconUrl>https://raw.githubusercontent.com/Z3Prover/z3/{1}/package/icon.jpg</iconUrl>
        <projectUrl>https://github.com/Z3Prover/z3</projectUrl>
        <licenseUrl>https://raw.githubusercontent.com/Z3Prover/z3/{1}/LICENSE.txt</licenseUrl>
        <repository
            type="git"
            url="https://github.com/Z3Prover/z3.git"
            branch="master"
            commit="{1}"
        />
        <requireLicenseAcceptance>true</requireLicenseAcceptance>
        <language>en</language>
    </metadata>
</package>""".format(release_version, release_commit)

    with open("out/Microsoft.Z3.x64.nuspec", 'w') as f:
        f.write(contents)
        
def create_nuget_package():
    subprocess.call(["nuget", "pack"], cwd="out")

nuget_sign_input = """
{
  "Version": "1.0.0",
  "SignBatches"
  :
  [
   {
    "SourceLocationType": "UNC",
    "SourceRootDirectory": "%s",
    "DestinationLocationType": "UNC",
    "DestinationRootDirectory": "%s",
    "SignRequestFiles": [
     {
      "CustomerCorrelationId": "42fc9577-af9e-4ac9-995d-1788d8721d17",
      "SourceLocation": "Microsoft.Z3.x64.%s.nupkg",
      "DestinationLocation": "Microsoft.Z3.x64.%s.nupkg"
     }
    ],
    "SigningInfo": {
     "Operations": [
      {
       "KeyCode" : "CP-401405",
       "OperationCode" : "NuGetSign",
       "Parameters" : {},
       "ToolName" : "sign",
       "ToolVersion" : "1.0"
      },
      {
       "KeyCode" : "CP-401405",
       "OperationCode" : "NuGetVerify",
       "Parameters" : {},
       "ToolName" : "sign",
       "ToolVersion" : "1.0"
      }
     ]
    }
   }
  ]
}"""

def sign_nuget_package():
    package_name = "Microsoft.Z3.x64.%s.nupkg" % release_version
    input_file = "out/nuget_sign_input.json"
    output_path = os.path.abspath("out").replace("\\","\\\\") 
    with open(input_file, 'w') as f:
        f.write(nuget_sign_input % (output_path, output_path, release_version, release_version))
    subprocess.call(["EsrpClient.exe", "sign", "-a", "authorization.json", "-p", "policy.json", "-i", input_file, "-o", "out\\diagnostics.json"])
    
    
def main():
    mk_dir("packages")
    download_installs()
    unpack()
    mk_targets()
    create_nuget_spec()
    create_nuget_package()
    sign_nuget_package()


main()
