#!/bin/bash

SCRIPT_DIR="$( cd ${BASH_SOURCE[0]%/*} ; echo $PWD )"

set -x
set -e
set -o pipefail

: ${TEST_INSTALL?"TEST_INSTALL must be specified"}
: ${Z3_BUILD_DIR?"Z3_BUILD_DIR must be specified"}

if [ "X${TEST_INSTALL}" != "X1" ]; then
  echo "Skipping install"
  exit 0
fi

# Set CMake generator args
source ${SCRIPT_DIR}/set_generator_args.sh

cd "${Z3_BUILD_DIR}"

sudo cmake --build $(pwd) --target install "${GENERATOR_ARGS[@]}"

# TODO: Test the installed version in some way
