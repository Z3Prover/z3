#!/usr/bin/env bash

build_z3() {
   cd "${REPO_ROOT}"
   rm -rf build
   python scripts/mk_make.py --java
   cd build
   BUILD_DIR="${PWD}"
   make -j$(grep -i processor /proc/cpuinfo | wc -l)
   WORKING="$(mktemp -d)"
   cd "${WORKING}"
   umask 0022
   mkdir -p "${Z3_VERSION}/bin" "${Z3_VERSION}/lib"
   cp "${BUILD_DIR}/z3" "${Z3_VERSION}/bin/z3"
   chmod 0755 "${Z3_VERSION}/bin/z3"
   cp "${BUILD_DIR}/libz3.so" "${Z3_VERSION}/lib/libz3.so"
   chmod 0644 "${Z3_VERSION}/lib/libz3.so"
   cp "${BUILD_DIR}/libz3java.so" "${Z3_VERSION}/lib/libz3java.so"
   chmod 0644 "${Z3_VERSION}/lib/libz3java.so"
   cp "${BUILD_DIR}/../LICENSE.txt" "${Z3_VERSION}/LICENSE"
   chmod 0644 "${Z3_VERSION}/LICENSE"
   zip -r "${BUILD_DIR}/${Z3_ZIP}" "${Z3_VERSION}"
   cd "${BUILD_DIR}"
   rm -rf "${WORKING}"
}

package_z3_ubuntu() {
   UBUNTU_VERSION_STRING="x64-ubuntu-$(lsb_release -rs)"
   Z3_VERSION="z3-${VERSION}-${UBUNTU_VERSION_STRING}"
   Z3_ZIP="${Z3_VERSION}.zip"
   build_z3
}

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE}")" && pwd)"
if [ -z "${COMMIT_HASH}" ]; then
  COMMIT_HASH="$(git rev-parse HEAD)"
fi
if [ -z "${COMMIT_HASH}" ]; then
   echo "Not a git repository" 1>&2
   exit 1
fi
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
set -x
set -e
VERSION="$(date "+%Y-%m-%d")-${COMMIT_HASH}"
PLATFORM_STRING="$(python -mplatform)"
if [[ "${PLATFORM_STRING}" = *"Ubuntu"* ]]; then
   package_z3_ubuntu
else
   echo "Unsupported platform: ${PLATFORM_STRING}" 1>&2
   exit 1
fi

