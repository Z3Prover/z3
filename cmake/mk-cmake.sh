#!/bin/bash
set -e -u -o pipefail
trap "kill 0" SIGINT SIGTERM

# brew installs of binutils put gnu readlink as greadlink
READLINK=readlink
if which greadlink &>/dev/null; then
  READLINK=greadlink
fi

cmake_dir=$($READLINK -f $(dirname $0))
z3_dir=$($READLINK -f $cmake_dir/..)

ln -fs $cmake_dir/CMakeLists.txt $z3_dir

find $z3_dir/src -type d > $cmake_dir/include-dirs.txt
find $z3_dir/src -name '*.cpp' | grep -v Native.cpp | grep -v src/shell | grep -v src/test > $cmake_dir/sources-libz3.txt
find $z3_dir/src/shell -name '*.cpp' > $cmake_dir/sources-z3.txt
