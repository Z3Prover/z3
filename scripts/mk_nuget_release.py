# 
# Copyright (c) 2018 Microsoft Corporation
#

# 1. download releases from github
# 2. copy over libz3.dll for the different architectures
# 3. copy over Microsoft.Z3.dll from suitable distribution
# 4. copy nuspec file from packages
# 5. call nuget pack

import json
import os
import urllib.request
import zipfile
import sys
import os.path

data = json.loads(urllib.request.urlopen("https://api.github.com/repos/Z3Prover/z3/releases/latest").read().decode())

version_str = data['tag_name']

def mk_dir(d):
    if not os.path.exists(d):
        os.makedirs(d)

def download_installs():
    for asset in data['assets']:
        url = asset['browser_download_url']
        name = asset['name']
        print("Downloading ", url)
        sys.stdout.flush()
        urllib.request.urlretrieve(url, "packages/%s" % name)

os_names = ["ubuntu-14", "ubuntu-16", "win", "debian", "osx"]

def unpack():
    for f in os.listdir("packages"):
        if f.endswith("zip") and "x64" in f:
            print(f)
            # determine os from os_names
            # instead of this string manipulation.
            
            name = os.path.splitext(f)[0]
            os_name = name[name.find("x64")+4:]
            os_name = os_name[:os_name.find("-")]
            print(os_name)
            
            zip_ref = zipfile.ZipFile("packages/%s" % f, 'r')
            path = "out/%s" % os_name
            zip_ref.extract("%s/bin/libz3.so" % name)
            
    # unzip files in packages
    pass

def main():
    mk_dir("packages")
#   download_installs()
#    create_nuget_dir()
    unpack()
#    create_nuget_package()
    
main()
