#!/usr/bin/env bash
REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE}")" && pwd)"
set -x
set -e
. "${REPO_ROOT}/common.sh"
Z3_GIT_VERSION="$(z3_git_version)"
if ! which python2.7; then
   echo Missing python2.7 1>&2
   exit 1
fi
if ! which java; then
   echo Missing java 1>&2
   exit 1
fi
if ! which javac; then
   echo Missing javac 1>&2
   exit 1
fi
OLD_PWD="${PWD}"
OLD_UMASK="$(umask)"
OSX_VERSION="$(sw_vers | grep ProductVersion | awk '{ print $2; }')"
if [ -z "${BREW_LLVM_PREFIX}" ]; then
   NO_OPENMP_SUFFIX="-without-openmp"
else
   NO_OPENMP_SUFFIX=
fi
Z3_VERSION="z3-${Z3_GIT_VERSION}-x64-osx-${OSX_VERSION}${NO_OPENMP_SUFFIX}"
Z3_ZIP="${Z3_VERSION}.zip"
cd "${REPO_ROOT}"
rm -rf build
python scripts/mk_make.py --java USE_OPENMP=1
cd build
BUILD_DIR="${PWD}"
make -j$(sysctl -n hw.ncpu)
WORKING="$(mktemp -d)"
cd "${WORKING}"
umask 0022
mkdir -p "${Z3_VERSION}/bin" "${Z3_VERSION}/lib"
cp "${BUILD_DIR}/z3" "${Z3_VERSION}/bin/z3"
chmod 0755 "${Z3_VERSION}/bin/z3"
cp "${BUILD_DIR}/libz3.dylib" "${Z3_VERSION}/lib/libz3.dylib"
chmod 0644 "${Z3_VERSION}/lib/libz3.dylib"
cp "${BUILD_DIR}/libz3java.dylib" "${Z3_VERSION}/lib/libz3java.dylib"
chmod 0644 "${Z3_VERSION}/lib/libz3java.dylib"
cp "${BUILD_DIR}/../LICENSE.txt" "${Z3_VERSION}/LICENSE"
chmod 0644 "${Z3_VERSION}/LICENSE"
if [ -n "${BREW_LLVM_PREFIX}" ]; then
  install_name_tool -change "${BREW_LLVM_PREFIX}/lib/libc++.1.dylib" "/usr/lib/libc++.1.dylib" "${Z3_VERSION}/bin/z3"
  install_name_tool -change "${BREW_LLVM_PREFIX}/lib/libomp.dylib" "libomp.dylib" "${Z3_VERSION}/bin/z3"
  install_name_tool -change "${BREW_LLVM_PREFIX}/lib/libc++.1.dylib" "/usr/lib/libc++.1.dylib" "${Z3_VERSION}/lib/libz3.dylib"
  install_name_tool -change "${BREW_LLVM_PREFIX}/lib/libomp.dylib" "libomp.dylib" "${Z3_VERSION}/lib/libz3.dylib"
  curl -L "http://llvm.org/svn/llvm-project/openmp/trunk/LICENSE.txt" > "${Z3_VERSION}/LICENSE.libomp"
  chmod 0644 "${Z3_VERSION}/LICENSE.libomp"
  cp "${BREW_LLVM_PREFIX}/lib/libomp.dylib" "${Z3_VERSION}/lib/libomp.dylib"
  chmod 0644 "${Z3_VERSION}/lib/libomp.dylib"
fi
mkdir -p "${BUILD_DIR}/generated-packages"
zip -r "${BUILD_DIR}/generated-packages/${Z3_ZIP}" "${Z3_VERSION}"
cd "${BUILD_DIR}"
rm -rf "${WORKING}"

