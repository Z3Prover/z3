#!/bin/sh

cd ..
mkdir build
CSC=/usr/bin/csc GACUTIL=/usr/bin/gacutil CXX=clang++ CC=clang python scripts/mk_make.py  --java --python
cd build
make
make test-z3
make cpp_example
make c_example
make java_example
make python_example
./cpp_example
./c_example



