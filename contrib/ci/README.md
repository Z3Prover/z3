# Continuous integration scripts

## TravisCI

For testing on Linux and macOS we use [TravisCI](https://travis-ci.org/)

TravisCI consumes the `.travis.yml` file in the root of the repository
to tell it how to build and test Z3.

However the logic for building and test Z3 is kept out of this file
and instead in a set of scripts in `scripts/`. This avoids
coupling the build to TravisCI tightly so we can migrate to another
service if required in the future.

The scripts rely on a set of environment variables to control the configuration
of the build. The `.travis.yml` declares a list of configuration with each
configuration setting different environment variables.

Note that the build scripts currently only support Z3 built with CMake. Support
for building Z3 using the older Python/Makefile build system might be added in
the future.

### Configuration variables

* `ASAN_BUILD` - Do [AddressSanitizer](https://github.com/google/sanitizers/wiki/AddressSanitizer) build (`0` or `1`)
* `BUILD_DOCS` - Build API documentation (`0` or `1`)
* `C_COMPILER` - Path to C Compiler
* `CXX_COMPILER` - Path to C++ Compiler
* `DOTNET_BINDINGS` - Build and test .NET API bindings (`0` or `1`)
* `JAVA_BINDINGS` - Build and test Java API bindings (`0` or `1`)
* `NO_SUPPRESS_OUTPUT` - Don't suppress output of some commands (`0` or `1`)
* `PYTHON_BINDINGS` - Build and test Python API bindings (`0` or `1`)
* `RUN_API_EXAMPLES` - Build and run API examples (`0` or `1`)
* `RUN_SYSTEM_TESTS` - Run system tests (`0` or `1`)
* `RUN_UNIT_TESTS` - Run unit tests (`BUILD_ONLY` or `BUILD_AND_RUN` or `SKIP`)
* `SANITIZER_PRINT_SUPPRESSIONS` - Show ASan/UBSan suppressions (`0` or `1`)
* `TARGET_ARCH` - Target architecture (`x86_64` or `i686`)
* `TEST_INSTALL` - Test running `install` target (`0` or `1`)
* `UBSAN_BUILD` - Do [UndefinedBehaviourSanitizer](https://clang.llvm.org/docs/UndefinedBehaviorSanitizer.html) build (`0` or `1`)
* `USE_LIBGMP` - Use [GNU multiple precision library](https://gmplib.org/) (`0` or `1`)
* `USE_LTO` - Link binaries using link time optimization (`0` or `1`)
* `USE_OPENMP` - Use OpenMP (`0` or `1`)
* `Z3_BUILD_TYPE` - CMake build type (`RelWithDebInfo`, `Release`, `Debug`, or `MinSizeRel`)
* `Z3_CMAKE_GENERATOR` - CMake generator (`Ninja` or `Unix Makefiles`)
* `Z3_VERBOSE_BUILD_OUTPUT` - Show compile commands in CMake builds (`0` or `1`)
* `Z3_STATIC_BUILD` - Build Z3 binaries and libraries statically (`0` or `1`)
* `Z3_SYSTEM_TEST_GIT_REVISION` - Git revision of [z3test](https://github.com/Z3Prover/z3test). If empty lastest revision will be used.
* `Z3_WARNINGS_AS_ERRORS` - Set the `WARNINGS_AS_ERRORS` CMake option passed to Z3 (`OFF`, `ON`, or `SERIOUS_ONLY`)

### Linux

For Linux we use Docker to perform the build so that it easily reproducible
on a local machine and so that we can avoid depending on TravisCI's environment
and instead use a Linux distribution of our choice.

The `scripts/travis_ci_linux_entry_point.sh` script

1. Creates a base image containing all the dependencies needed to build and test Z3
2. Builds and tests Z3 using the base image propagating configuration environment
   variables (if set) into the build using the `--build-arg` argument of the `docker run`
   command.

The default values of the configuration environment variables
can be found in
[`scripts/ci_defaults.sh`](scripts/ci_defaults.sh).

#### Linux specific configuration variables

* `LINUX_BASE` - The base docker image identifier to use (`ubuntu_16.04`, `ubuntu32_16.04`, or `ubuntu_14.04`).

#### Reproducing a build locally

A build can be reproduced locally by using the
`scripts/travis_ci_linux_entry_point.sh` script and setting the appropriate
environment variable.

For example lets say we wanted to reproduce the build below.

```yaml

  - LINUX_BASE=ubuntu_16.04 C_COMPILER=/usr/bin/gcc-5 CXX_COMPILER=/usr/bin/g++-5 TARGET_ARCH=x86_64 Z3_BUILD_TYPE=RelWithDebInfo
```

This can be done by running the command

```bash
LINUX_BASE=ubuntu_16.04 C_COMPILER=/usr/bin/gcc-5 CXX_COMPILER=/usr/bin/g++-5 TARGET_ARCH=x86_64 Z3_BUILD_TYPE=RelWithDebInfo scripts/travis_ci_linux_entry_point.sh
```

The `docker build` command which we use internally supports caching. What this
means in practice is that re-running the above command will re-use successfully
completed stages of the build provided they haven't changed. This requires that
the `Dockerfiles/z3_build.Dockerfile` is carefully crafted to avoid invalidating
the cache when unrelated files sent to the build context change.

#### TravisCI docker image cache

To improve build times the Z3 base docker images are cached using
[TravisCI's cache directory feature](https://docs.travis-ci.com/user/caching).
If the `DOCKER_TRAVIS_CI_CACHE_DIR` environment variable is set (see `.travis.yml`)
then the directory pointed to by the environment variable is used as a cache
for Docker images.

The logic for this can be found in `scripts/travis_ci_linux_entry_point.sh`.
The build time improvements are rather modest (~ 2 minutes) and the cache is
rather large due to TravisCI giving each configuration its own cache. So this
feature might be removed in the future.

It may be better to just build the base image once (outside of TravisCI), upload
it to [DockerHub](https://hub.docker.com/) and have the build pull down the pre-built
image every time.

An [organization](https://hub.docker.com/u/z3prover/) has been created on
DockerHub for this.

### macOS

For macOS we execute directly on TravisCI's macOS environment.  The entry point
for the TravisCI builds is the
[`scripts/travis_ci_osx_entry_point.sh`](scripts/travis_ci_osx_entry_point.sh)
scripts.

#### macOS specific configuration variables

* `MACOS_SKIP_DEPS_UPDATE` - If set to `1` installing the necessary build dependencies
  is skipped. This is useful for local testing if the dependencies are already installed.
* `MACOS_UPDATE_CMAKE` - If set to `1` the installed version of CMake will be upgraded.

#### Reproducing a build locally

To reproduce a build (e.g. like the one shown below)

```yaml
- os: osx
  osx_image: xcode8.3
  # Note: Apple Clang does not support OpenMP
  env: Z3_BUILD_TYPE=RelWithDebInfo USE_OPENMP=0
```

Run the following:

```bash
TRAVIS_BUILD_DIR=$(pwd) \
Z3_BUILD_TYPE=RelWithDebInfo \
USE_OPEN_MP=0 \
contrib/ci/scripts/travis_ci_osx_entry_point.sh
```

Note this assumes that the current working directory is the root of the Z3
git repository.
