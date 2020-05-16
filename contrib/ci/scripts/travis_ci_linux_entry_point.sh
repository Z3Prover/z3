#!/bin/bash

SCRIPT_DIR="$( cd ${BASH_SOURCE[0]%/*} ; echo $PWD )"

set -x
set -e
set -o pipefail

DOCKER_FILE_DIR="$(cd ${SCRIPT_DIR}/../Dockerfiles; echo $PWD)"

: ${LINUX_BASE?"LINUX_BASE must be specified"}


# Sanity check. Current working directory should be repo root
if [ ! -f "./README.md" ]; then
  echo "Current working directory should be repo root"
  exit 1
fi

# Get defaults
source "${SCRIPT_DIR}/ci_defaults.sh"

BUILD_OPTS=()
# Pass Docker build arguments
if [ -n "${Z3_BUILD_TYPE}" ]; then
  BUILD_OPTS+=("--build-arg" "Z3_BUILD_TYPE=${Z3_BUILD_TYPE}")
fi

if [ -n "${Z3_CMAKE_GENERATOR}" ]; then
  BUILD_OPTS+=("--build-arg" "Z3_CMAKE_GENERATOR=${Z3_CMAKE_GENERATOR}")
fi

if [ -n "${Z3_USE_LIBGMP}" ]; then
  BUILD_OPTS+=("--build-arg" "Z3_USE_LIBGMP=${Z3_USE_LIBGMP}")
fi

if [ -n "${BUILD_DOCS}" ]; then
  BUILD_OPTS+=("--build-arg" "BUILD_DOCS=${BUILD_DOCS}")
fi

if [ -n "${PYTHON_EXECUTABLE}" ]; then
  BUILD_OPTS+=("--build-arg" "PYTHON_EXECUTABLE=${PYTHON_EXECUTABLE}")
fi

if [ -n "${PYTHON_BINDINGS}" ]; then
  BUILD_OPTS+=("--build-arg" "PYTHON_BINDINGS=${PYTHON_BINDINGS}")
fi

if [ -n "${DOTNET_BINDINGS}" ]; then
  BUILD_OPTS+=("--build-arg" "DOTNET_BINDINGS=${DOTNET_BINDINGS}")
fi

if [ -n "${JAVA_BINDINGS}" ]; then
  BUILD_OPTS+=("--build-arg" "JAVA_BINDINGS=${JAVA_BINDINGS}")
fi

if [ -n "${USE_LTO}" ]; then
  BUILD_OPTS+=("--build-arg" "USE_LTO=${USE_LTO}")
fi

if [ -n "${Z3_INSTALL_PREFIX}" ]; then
  BUILD_OPTS+=("--build-arg" "Z3_INSTALL_PREFIX=${Z3_INSTALL_PREFIX}")
fi

# TravisCI reserves CC for itself so use a different name
if [ -n "${C_COMPILER}" ]; then
  BUILD_OPTS+=("--build-arg" "CC=${C_COMPILER}")
fi

# TravisCI reserves CXX for itself so use a different name
if [ -n "${CXX_COMPILER}" ]; then
  BUILD_OPTS+=("--build-arg" "CXX=${CXX_COMPILER}")
fi

if [ -n "${TARGET_ARCH}" ]; then
  BUILD_OPTS+=("--build-arg" "TARGET_ARCH=${TARGET_ARCH}")
fi

if [ -n "${ASAN_BUILD}" ]; then
  BUILD_OPTS+=("--build-arg" "ASAN_BUILD=${ASAN_BUILD}")
fi

if [ -n "${ASAN_DSO}" ]; then
  BUILD_OPTS+=("--build-arg" "ASAN_DSO=${ASAN_DSO}")
fi

if [ -n "${SANITIZER_PRINT_SUPPRESSIONS}" ]; then
  BUILD_OPTS+=("--build-arg" "SANITIZER_PRINT_SUPPRESSIONS=${SANITIZER_PRINT_SUPPRESSIONS}")
fi

if [ -n "${UBSAN_BUILD}" ]; then
  BUILD_OPTS+=("--build-arg" "UBSAN_BUILD=${UBSAN_BUILD}")
fi

if [ -n "${TEST_INSTALL}" ]; then
  BUILD_OPTS+=("--build-arg" "TEST_INSTALL=${TEST_INSTALL}")
fi

if [ -n "${RUN_API_EXAMPLES}" ]; then
  BUILD_OPTS+=("--build-arg" "RUN_API_EXAMPLES=${RUN_API_EXAMPLES}")
fi

if [ -n "${RUN_SYSTEM_TESTS}" ]; then
  BUILD_OPTS+=("--build-arg" "RUN_SYSTEM_TESTS=${RUN_SYSTEM_TESTS}")
fi

if [ -n "${Z3_SYSTEM_TEST_GIT_REVISION}" ]; then
  BUILD_OPTS+=( \
    "--build-arg" \
    "Z3_SYSTEM_TEST_GIT_REVISION=${Z3_SYSTEM_TEST_GIT_REVISION}" \
  )
fi

if [ -n "${RUN_UNIT_TESTS}" ]; then
  BUILD_OPTS+=("--build-arg" "RUN_UNIT_TESTS=${RUN_UNIT_TESTS}")
fi

if [ -n "${Z3_VERBOSE_BUILD_OUTPUT}" ]; then
  BUILD_OPTS+=( \
    "--build-arg" \
    "Z3_VERBOSE_BUILD_OUTPUT=${Z3_VERBOSE_BUILD_OUTPUT}" \
  )
fi

if [ -n "${Z3_STATIC_BUILD}" ]; then
  BUILD_OPTS+=("--build-arg" "Z3_STATIC_BUILD=${Z3_STATIC_BUILD}")
fi

if [ -n "${NO_SUPPRESS_OUTPUT}" ]; then
  BUILD_OPTS+=( \
    "--build-arg" \
    "NO_SUPPRESS_OUTPUT=${NO_SUPPRESS_OUTPUT}" \
  )
fi

if [ -n "${Z3_WARNINGS_AS_ERRORS}" ]; then
  BUILD_OPTS+=( \
    "--build-arg" \
    "Z3_WARNINGS_AS_ERRORS=${Z3_WARNINGS_AS_ERRORS}" \
  )
fi

case ${LINUX_BASE} in
  ubuntu_14.04)
    BASE_DOCKER_FILE="${DOCKER_FILE_DIR}/z3_base_ubuntu_14.04.Dockerfile"
    BASE_DOCKER_IMAGE_NAME="z3_base_ubuntu:14.04"
    ;;
  ubuntu_16.04)
    BASE_DOCKER_FILE="${DOCKER_FILE_DIR}/z3_base_ubuntu_16.04.Dockerfile"
    BASE_DOCKER_IMAGE_NAME="z3_base_ubuntu:16.04"
    ;;
  ubuntu32_16.04)
    BASE_DOCKER_FILE="${DOCKER_FILE_DIR}/z3_base_ubuntu32_16.04.Dockerfile"
    BASE_DOCKER_IMAGE_NAME="z3_base_ubuntu32:16.04"
    ;;
  *)
    echo "Unknown Linux base ${LINUX_BASE}"
    exit 1
    ;;
esac

# Initially assume that we need to build the base Docker image
MUST_BUILD=1

# Travis CI persistent cache.
#
# This inspired by http://rundef.com/fast-travis-ci-docker-build .
# The idea is to cache the built image for subsequent builds to
# reduce build time.
if [ -n "${DOCKER_TRAVIS_CI_CACHE_DIR}" ]; then
  CHECKSUM_FILE="${DOCKER_TRAVIS_CI_CACHE_DIR}/${BASE_DOCKER_IMAGE_NAME}.chksum"
  CACHED_DOCKER_IMAGE="${DOCKER_TRAVIS_CI_CACHE_DIR}/${BASE_DOCKER_IMAGE_NAME}.gz"
  if [ -f "${CACHED_DOCKER_IMAGE}" ]; then
    # There's a cached image to use. Check the checksums of the Dockerfile
    # match. If they don't that implies we need to build a fresh image.
    if [ -f "${CHECKSUM_FILE}" ]; then
      CURRENT_DOCKERFILE_CHECKSUM=$(sha256sum "${BASE_DOCKER_FILE}" | awk '{ print $1 }')
      CACHED_DOCKERFILE_CHECKSUM=$(cat "${CHECKSUM_FILE}")
      if [ "X${CURRENT_DOCKERFILE_CHECKSUM}" = "X${CACHED_DOCKERFILE_CHECKSUM}" ]; then
        # Load the cached image
        MUST_BUILD=0
        gunzip --stdout "${CACHED_DOCKER_IMAGE}" | docker load
      fi
    fi
  fi
fi

if [ "${MUST_BUILD}" -eq 1 ]; then
  # The base image contains all the dependencies we want to build
  # Z3.
  docker build -t "${BASE_DOCKER_IMAGE_NAME}" - < "${BASE_DOCKER_FILE}"

  if [ -n "${DOCKER_TRAVIS_CI_CACHE_DIR}" ]; then
    # Write image and checksum to cache
    docker save "${BASE_DOCKER_IMAGE_NAME}" | \
      gzip > "${CACHED_DOCKER_IMAGE}"
    sha256sum "${BASE_DOCKER_FILE}" | awk '{ print $1 }' > \
      "${CHECKSUM_FILE}"
  fi
fi


DOCKER_MAJOR_VERSION=$(docker info --format '{{.ServerVersion}}' | sed 's/^\([0-9]\+\)\.\([0-9]\+\).*$/\1/')
DOCKER_MINOR_VERSION=$(docker info --format '{{.ServerVersion}}' | sed 's/^\([0-9]\+\)\.\([0-9]\+\).*$/\2/')
DOCKER_BUILD_FILE="${DOCKER_FILE_DIR}/z3_build.Dockerfile"

if [ "${DOCKER_MAJOR_VERSION}${DOCKER_MINOR_VERSION}" -lt 1705 ]; then
  # Workaround limitation in older Docker versions where the FROM
  # command cannot be parameterized with an ARG.
  sed \
    -e '/^ARG DOCKER_IMAGE_BASE/d' \
    -e 's/${DOCKER_IMAGE_BASE}/'"${BASE_DOCKER_IMAGE_NAME}/" \
    "${DOCKER_BUILD_FILE}" > "${DOCKER_BUILD_FILE}.patched"
  DOCKER_BUILD_FILE="${DOCKER_BUILD_FILE}.patched"
else
  # This feature landed in Docker 17.05
  # See https://github.com/moby/moby/pull/31352
  BUILD_OPTS+=( \
    "--build-arg" \
    "DOCKER_IMAGE_BASE=${BASE_DOCKER_IMAGE_NAME}" \
  )
fi

# Now build Z3 and test it using the created base image
docker build \
  -f "${DOCKER_BUILD_FILE}" \
  "${BUILD_OPTS[@]}" \
  .
