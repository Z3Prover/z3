ARG DOCKER_IMAGE_BASE
FROM ${DOCKER_IMAGE_BASE}


# Build arguments. This can be changed when invoking
# `docker build`.
ARG ASAN_BUILD
ARG ASAN_DSO
ARG BUILD_DOCS
ARG CC
ARG CXX
ARG DOTNET_BINDINGS
ARG JAVA_BINDINGS
ARG NO_SUPPRESS_OUTPUT
ARG PYTHON_BINDINGS
ARG PYTHON_EXECUTABLE=/usr/bin/python2.7
ARG RUN_API_EXAMPLES
ARG RUN_SYSTEM_TESTS
ARG RUN_UNIT_TESTS
ARG SANITIZER_PRINT_SUPPRESSIONS
ARG TARGET_ARCH
ARG TEST_INSTALL
ARG UBSAN_BUILD
ARG USE_LIBGMP
ARG USE_LTO
ARG USE_OPENMP
ARG Z3_SRC_DIR=/home/user/z3_src
ARG Z3_BUILD_TYPE
ARG Z3_CMAKE_GENERATOR
ARG Z3_INSTALL_PREFIX
ARG Z3_STATIC_BUILD
ARG Z3_SYSTEM_TEST_GIT_REVISION
ARG Z3_WARNINGS_AS_ERRORS
ARG Z3_VERBOSE_BUILD_OUTPUT

ENV \
  ASAN_BUILD=${ASAN_BUILD} \
  ASAN_DSO=${ASAN_DSO} \
  BUILD_DOCS=${BUILD_DOCS} \
  CC=${CC} \
  CXX=${CXX} \
  DOTNET_BINDINGS=${DOTNET_BINDINGS} \
  JAVA_BINDINGS=${JAVA_BINDINGS} \
  NO_SUPPRESS_OUTPUT=${NO_SUPPRESS_OUTPUT} \
  PYTHON_BINDINGS=${PYTHON_BINDINGS} \
  PYTHON_EXECUTABLE=${PYTHON_EXECUTABLE} \
  SANITIZER_PRINT_SUPPRESSIONS=${SANITIZER_PRINT_SUPPRESSIONS} \
  RUN_API_EXAMPLES=${RUN_API_EXAMPLES} \
  RUN_SYSTEM_TESTS=${RUN_SYSTEM_TESTS} \
  RUN_UNIT_TESTS=${RUN_UNIT_TESTS} \
  TARGET_ARCH=${TARGET_ARCH} \
  TEST_INSTALL=${TEST_INSTALL} \
  UBSAN_BUILD=${UBSAN_BUILD} \
  USE_LIBGMP=${USE_LIBGMP} \
  USE_LTO=${USE_LTO} \
  USE_OPENMP=${USE_OPENMP} \
  Z3_SRC_DIR=${Z3_SRC_DIR} \
  Z3_BUILD_DIR=/home/user/z3_build \
  Z3_BUILD_TYPE=${Z3_BUILD_TYPE} \
  Z3_CMAKE_GENERATOR=${Z3_CMAKE_GENERATOR} \
  Z3_VERBOSE_BUILD_OUTPUT=${Z3_VERBOSE_BUILD_OUTPUT} \
  Z3_STATIC_BUILD=${Z3_STATIC_BUILD} \
  Z3_SYSTEM_TEST_DIR=/home/user/z3_system_test \
  Z3_SYSTEM_TEST_GIT_REVISION=${Z3_SYSTEM_TEST_GIT_REVISION} \
  Z3_WARNINGS_AS_ERRORS=${Z3_WARNINGS_AS_ERRORS} \
  Z3_INSTALL_PREFIX=${Z3_INSTALL_PREFIX}

# We add context across incrementally to maximal cache reuse

# Build Z3
RUN mkdir -p "${Z3_SRC_DIR}" && \
  mkdir -p "${Z3_SRC_DIR}/contrib/ci/scripts" && \
  mkdir -p "${Z3_SRC_DIR}/contrib/suppressions/sanitizers"
# Deliberately leave out `contrib`
ADD /cmake ${Z3_SRC_DIR}/cmake/
ADD /doc ${Z3_SRC_DIR}/doc/
ADD /examples ${Z3_SRC_DIR}/examples/
ADD /scripts ${Z3_SRC_DIR}/scripts/
ADD /src ${Z3_SRC_DIR}/src/
ADD *.txt *.md RELEASE_NOTES ${Z3_SRC_DIR}/

ADD \
  /contrib/ci/scripts/build_z3_cmake.sh \
  /contrib/ci/scripts/ci_defaults.sh \
  /contrib/ci/scripts/set_compiler_flags.sh \
  /contrib/ci/scripts/set_generator_args.sh \
  ${Z3_SRC_DIR}/contrib/ci/scripts/
RUN ${Z3_SRC_DIR}/contrib/ci/scripts/build_z3_cmake.sh

# Test building docs
ADD \
  /contrib/ci/scripts/test_z3_docs.sh \
  /contrib/ci/scripts/run_quiet.sh \
  ${Z3_SRC_DIR}/contrib/ci/scripts/
RUN ${Z3_SRC_DIR}/contrib/ci/scripts/test_z3_docs.sh

# Test examples
ADD \
  /contrib/ci/scripts/test_z3_examples_cmake.sh \
  /contrib/ci/scripts/sanitizer_env.sh \
  ${Z3_SRC_DIR}/contrib/ci/scripts/
ADD \
  /contrib/suppressions/sanitizers/asan.txt \
  /contrib/suppressions/sanitizers/lsan.txt \
  /contrib/suppressions/sanitizers/ubsan.txt \
  ${Z3_SRC_DIR}/contrib/suppressions/sanitizers/
RUN ${Z3_SRC_DIR}/contrib/ci/scripts/test_z3_examples_cmake.sh

# Run unit tests
ADD \
  /contrib/ci/scripts/test_z3_unit_tests_cmake.sh \
  ${Z3_SRC_DIR}/contrib/ci/scripts/
RUN ${Z3_SRC_DIR}/contrib/ci/scripts/test_z3_unit_tests_cmake.sh

# Run system tests
ADD \
  /contrib/ci/scripts/test_z3_system_tests.sh \
  ${Z3_SRC_DIR}/contrib/ci/scripts/
RUN ${Z3_SRC_DIR}/contrib/ci/scripts/test_z3_system_tests.sh

# Test install
ADD \
  /contrib/ci/scripts/test_z3_install_cmake.sh \
  ${Z3_SRC_DIR}/contrib/ci/scripts/
RUN ${Z3_SRC_DIR}/contrib/ci/scripts/test_z3_install_cmake.sh
