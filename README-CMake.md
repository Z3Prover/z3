# Building and using Z3 with CMake

CMake is the preferred build system for most Z3 build and integration tasks.
It supports the Z3 executable and library, tests, examples, documentation, and
the Python, .NET, Java, Go, OCaml, and Julia bindings.

Z3 requires CMake 3.30 or newer, Python 3, and a compiler with C++20 support.
Additional language bindings require their corresponding toolchains.

## Build Z3

Run these commands from the root of the Z3 source tree:

```sh
cmake -S . -B build -DCMAKE_BUILD_TYPE=Release
cmake --build build --parallel
```

CMake always uses a separate build directory; `build` is only a conventional
name. To start over or keep configurations separate, remove the directory or
choose another one.

The default generator is usually appropriate. To use Ninja explicitly:

```sh
cmake -G Ninja -S . -B build -DCMAKE_BUILD_TYPE=Release
cmake --build build
```

To select a compiler, set `CC` and `CXX` during the first configuration of a
build directory:

```sh
CC=clang CXX=clang++ cmake -G Ninja -S . -B build \
  -DCMAKE_BUILD_TYPE=Release
```

After changing CMake options, rerun the configure command. CMake preserves
options in the build directory and regenerates the native build system as
needed.

### Single- and multi-config generators

Single-config generators such as Ninja and Unix Makefiles select the
configuration at configure time:

```sh
cmake -G Ninja -S . -B build -DCMAKE_BUILD_TYPE=Debug
cmake --build build
```

Multi-config generators such as Visual Studio, Xcode, and Ninja Multi-Config
select it at build and install time:

```sh
cmake -G "Ninja Multi-Config" -S . -B build
cmake --build build --config Release
cmake --install build --config Release
```

Supported configurations are `Debug`, `Release`, `RelWithDebInfo`, and
`MinSizeRel`. If `CMAKE_BUILD_TYPE` is omitted for a top-level single-config
build, Z3 defaults to `RelWithDebInfo`.

### Build selected targets

The default top-level build includes the `z3` executable and `libz3`. It also
makes the examples and `test-z3` executable available as explicit targets:

```sh
cmake --build build --target shell --parallel
cmake --build build --target test-z3 --parallel
./build/test-z3 -a
```

Use `cmake --build build --target help` to list targets supported by the
selected generator.

## Install Z3

Set the default installation prefix while configuring, or override it when
installing:

```sh
cmake -S . -B build -DCMAKE_BUILD_TYPE=Release \
  -DCMAKE_INSTALL_PREFIX=/path/to/prefix
cmake --build build --parallel
cmake --install build
```

Alternatively:

```sh
cmake --install build --prefix /path/to/prefix
```

For staged packaging, use `DESTDIR`:

```sh
DESTDIR=/path/to/staging cmake --install build
```

Z3 also provides an uninstall target for top-level builds:

```sh
cmake --build build --target uninstall
```

The standard GNU installation variables are supported, including
`CMAKE_INSTALL_BINDIR`, `CMAKE_INSTALL_INCLUDEDIR`, and
`CMAKE_INSTALL_LIBDIR`. Z3 additionally provides
`CMAKE_INSTALL_PKGCONFIGDIR` and `CMAKE_INSTALL_Z3_CMAKE_PACKAGE_DIR`.

### Install shared and static libraries together

Z3's shared and static CMake packages can be installed into the same prefix.
To build both variants in place, install the shared variant and then
reconfigure the same build tree for the static variant:

```sh
cmake -G Ninja -S . -B build \
  -DCMAKE_BUILD_TYPE=Release \
  -DCMAKE_INSTALL_PREFIX=/path/to/prefix \
  -DBUILD_SHARED_LIBS=ON
cmake --build build --target libz3 shell
cmake --install build

cmake -G Ninja -S . -B build -DBUILD_SHARED_LIBS=OFF
cmake --build build --target libz3 shell
cmake --install build
```

Z3 builds both variants with position-independent code. The second install
adds the static package beside the shared package without removing it.

## Common configuration options

CMake options are passed during configuration with `-D<name>=<value>`:

```sh
cmake -S . -B build -DBUILD_SHARED_LIBS=OFF -DZ3_USE_LIB_GMP=ON
```

The most commonly useful options are:

| Option | Default | Purpose |
| --- | --- | --- |
| `BUILD_SHARED_LIBS` | `ON` | Build shared rather than static libraries. |
| `Z3_BUILD_EXECUTABLE` | `ON` at top level | Build the `z3` command-line executable. |
| `Z3_BUILD_TEST_EXECUTABLES` | `ON` at top level | Build Z3's test executables. |
| `Z3_ENABLE_EXAMPLE_TARGETS` | `ON` at top level | Add targets for the API examples. |
| `Z3_USE_LIB_GMP` | `OFF` | Use GMP instead of Z3's internal multiprecision implementation. |
| `Z3_SINGLE_THREADED` | `OFF` | Build without thread-safety support. |
| `Z3_BUILD_DOCUMENTATION` | `OFF` | Add the `api_docs` documentation target. |
| `Z3_LINK_TIME_OPTIMIZATION` | `OFF` | Enable link-time optimization. |
| `WARNINGS_AS_ERRORS` | `SERIOUS_ONLY` | Control whether compiler warnings are errors. |

`Z3_BUILD_LIBZ3_SHARED` remains accepted for compatibility, but new builds
should use CMake's standard `BUILD_SHARED_LIBS` option.

To inspect all options and cached values in an existing build tree, use a
CMake UI (`ccmake` or `cmake-gui`) or run:

```sh
cmake -LAH -N build
```

## Language bindings

Bindings are disabled by default. Enable any desired bindings when
configuring:

```sh
cmake -S . -B build -DCMAKE_BUILD_TYPE=Release \
  -DZ3_BUILD_PYTHON_BINDINGS=ON \
  -DZ3_BUILD_DOTNET_BINDINGS=ON \
  -DZ3_BUILD_JAVA_BINDINGS=ON \
  -DZ3_BUILD_GO_BINDINGS=ON \
  -DZ3_BUILD_OCAML_BINDINGS=ON \
  -DZ3_BUILD_JULIA_BINDINGS=ON
cmake --build build --parallel
```

Enable only the bindings for which the required toolchains are installed.
All bindings currently require a shared `libz3`, which is the default. Where a
binding has a separate `Z3_INSTALL_<LANG>_BINDINGS` option, it defaults to `ON`:

| Binding | Build option | Additional configuration |
| --- | --- | --- |
| Python | `Z3_BUILD_PYTHON_BINDINGS` | `Python3_EXECUTABLE`, `CMAKE_INSTALL_PYTHON_PKG_DIR` |
| .NET | `Z3_BUILD_DOTNET_BINDINGS` | .NET SDK |
| Java | `Z3_BUILD_JAVA_BINDINGS` | `JAVA_HOME`, `Z3_JAVA_JAR_INSTALLDIR` |
| Go | `Z3_BUILD_GO_BINDINGS` | Go 1.20 or newer |
| OCaml | `Z3_BUILD_OCAML_BINDINGS` | OCaml, Findlib, and Zarith |
| Julia | `Z3_BUILD_JULIA_BINDINGS` | `JlCxx_DIR` or `CMAKE_PREFIX_PATH` for libcxxwrap-julia |

### Build only Python bindings against an installed Z3

Packagers can build bindings for several Python versions without rebuilding
the core library. First install a shared Z3 library and CMake package:

```sh
cmake -S . -B build-libz3 -DCMAKE_BUILD_TYPE=Release \
  -DBUILD_SHARED_LIBS=ON -DCMAKE_INSTALL_PREFIX=/path/to/prefix
cmake --build build-libz3 --parallel
cmake --install build-libz3
```

Then configure each Python build against that installation:

```sh
Z3_ROOT=/path/to/prefix cmake -S . -B build-py310 \
  -DZ3_BUILD_LIBZ3_CORE=OFF \
  -DZ3_BUILD_PYTHON_BINDINGS=ON \
  -DCMAKE_INSTALL_PREFIX=/path/to/prefix \
  -DPython3_EXECUTABLE=/path/to/python3.10
cmake --build build-py310 --parallel
cmake --install build-py310
```

## Consume an installed Z3 package

A CMake installation exports the target `z3::libz3`. Downstream projects
should use the target instead of manually specifying include directories or
library paths:

```cmake
find_package(Z3 CONFIG REQUIRED)

add_executable(my_solver main.cpp)
target_link_libraries(my_solver PRIVATE z3::libz3)
```

If Z3 is installed in a nonstandard prefix, set `Z3_ROOT` to that prefix. It
may be a CMake cache variable or an environment variable:

```sh
cmake -S . -B build -DZ3_ROOT=/path/to/prefix
# or
Z3_ROOT=/path/to/prefix cmake -S . -B build
```

### Select a static or shared installation

Static and shared Z3 libraries can be installed into the same prefix. Request
a particular variant with a package component:

```cmake
find_package(Z3 CONFIG REQUIRED COMPONENTS static)
# or
find_package(Z3 CONFIG REQUIRED COMPONENTS shared)
```

Without a component, the package follows `Z3_SHARED_LIBS`, then
`BUILD_SHARED_LIBS`, when either is set. Otherwise it prefers an installed
shared library and falls back to a static one. The package target carries the
include paths and transitive dependencies required by the selected variant.

The compatibility variables `Z3_LIBRARIES`, `Z3_C_INCLUDE_DIRS`,
`Z3_CXX_INCLUDE_DIRS`, and `Z3_VERSION_STRING` are also provided, but the
imported target is preferred.

## Embed Z3 in another CMake build

Z3 can be included directly with `FetchContent`:

```cmake
include(FetchContent)
FetchContent_Declare(
  Z3
  GIT_REPOSITORY https://github.com/Z3Prover/z3.git
  GIT_TAG z3-4.15.3
)
FetchContent_MakeAvailable(Z3)

target_link_libraries(my_solver PRIVATE z3::libz3)
```

Or from a source checkout:

```cmake
add_subdirectory(path/to/z3)
target_link_libraries(my_solver PRIVATE z3::libz3)
```

When Z3 is embedded, the executable, tests, and examples default to disabled.
Set their options before `FetchContent_MakeAvailable()` or
`add_subdirectory()` if the parent project needs them. Other Z3 options, such
as `BUILD_SHARED_LIBS`, can be set in the same way.

## Troubleshooting

### Files generated by the Python build system

The Python build system writes generated files into the source tree. CMake
rejects such a source tree to prevent stale files from affecting the build.
From a Git checkout, preview the untracked files under `src` before removing
them:

```sh
git clean -nx src
git clean -fx src
```

The second command deletes untracked files, so inspect the first command's
output carefully.

### Reconfigure with a different compiler

CMake chooses the compiler on the first configuration of a build directory.
To change it, use a fresh build directory:

```sh
CC=gcc CXX=g++ cmake -G Ninja -S . -B build-gcc
CC=clang CXX=clang++ cmake -G Ninja -S . -B build-clang
```
