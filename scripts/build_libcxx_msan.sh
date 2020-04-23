#!/bin/sh

mkdir libcxx
cd libcxx
# Checkout LLVM, libc++ and libc++abi
svn co http://llvm.org/svn/llvm-project/llvm/trunk llvm
(cd llvm/projects && svn co http://llvm.org/svn/llvm-project/libcxx/trunk libcxx)
(cd llvm/projects && svn co http://llvm.org/svn/llvm-project/libcxxabi/trunk libcxxabi)

# Build libc++ with MSan:
mkdir libcxx_msan && cd libcxx_msan
cmake ../llvm -DCMAKE_BUILD_TYPE=Release -DLLVM_USE_SANITIZER=Memory -DCMAKE_C_COMPILER=clang -DCMAKE_CXX_COMPILER=clang++
make cxx -j4
cd ..