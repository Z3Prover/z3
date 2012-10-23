#!/bin/sh

#
# Update Z3 version
#

if [ $# -ne 1 ]; then
    echo "Usage: update-version.sh MAJOR.MINOR.BUILD.REVISION"
fi

sd edit lib/version.h
sd edit release.cmd
sd edit shell/shell.rc
sd edit dll/dll.rc
sd edit shell/main.cpp
sd edit Z3Inspector/Properties/AssemblyInfo.cs
sd edit Microsoft.Z3/Properties/AssemblyInfo.cs
sd edit Microsoft.Z3V3/AssemblyInfo.cpp

scripts/perl scripts/update-version.pl "$1"
