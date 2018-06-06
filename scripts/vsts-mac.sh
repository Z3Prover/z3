#!/bin/sh

cd ..
mkdir build
CSC=/usr/bin/csc GACUTIL=/usr/bin/gacutil CXX=clang++ CC=clang python scripts/mk_make.py  --java --python
cd build
make
make test-z3
make cpp_example
make c_example
# make java_example
# make python_example
./cpp_example
./test_capi

git clone https://github.com/z3prover/z3test.git z3test
ls
python z3test/scripts/test_benchmarks.py ./z3 ./z3test/regressions/smt2