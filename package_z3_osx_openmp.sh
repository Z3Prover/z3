#!/usr/bin/env bash
set -x
export BREW_LLVM_PREFIX="$(brew --prefix llvm)"
export CC="${BREW_LLVM_PREFIX}/bin/clang"
export CXX="${BREW_LLVM_PREFIX}/bin/clang++"
export LD="${BREW_LLVM_PREFIX}/bin/llvm-ld"
export AR="${BREW_LLVM_PREFIX}/bin/llvm-ar"
export LDFLAGS="-L${BREW_LLVM_PREFIX}/lib -Wl,-rpath,${BREW_LLVM_PREFIX}/lib"
export EXTRA_LIB_SEARCH_PATH="-L${BREW_LLVM_PREFIX}/lib"
export CPPFLAGS="-I${BREW_LLVM_PREFIX}/include -I${BREW_LLVM_PREFIX}/include/c++/v1/"
set -e
./package_z3_osx.sh

