#!/bin/sh

mkdir build
ls
CSC=/usr/bin/csc GACUTIL=/usr/bin/gacutil CXX=clang++ CC=clang python scripts/mk_make.py -x --dotnet --java --python
cd build
make



