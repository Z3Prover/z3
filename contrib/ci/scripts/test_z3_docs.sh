#!/bin/bash

SCRIPT_DIR="$( cd ${BASH_SOURCE[0]%/*} ; echo $PWD )"
. ${SCRIPT_DIR}/run_quiet.sh

set -x
set -e
set -o pipefail

: ${Z3_BUILD_DIR?"Z3_BUILD_DIR must be specified"}
: ${BUILD_DOCS?"BUILD_DOCS must be specified"}

# Set CMake generator args
source ${SCRIPT_DIR}/set_generator_args.sh

cd "${Z3_BUILD_DIR}"

# Generate documentation
if [ "X${BUILD_DOCS}" = "X1" ]; then
  # TODO: Make quiet once we've fixed the build
  run_quiet cmake --build $(pwd) --target api_docs "${GENERATOR_ARGS[@]}"
fi

# TODO: Test or perhaps deploy the built docs?
