# Z3's CMake build system

[CMake](https://cmake.org/) is a "meta build system" that reads a description
of the project written in the ``CMakeLists.txt`` files and emits a build
system for that project of your choice using one of CMake's "generators".
This allows CMake to support many different platforms and build tools.
You can run ``cmake --help`` to see the list of supported "generators"
on your platform. Example generators include "UNIX Makefiles" and "Visual Studio
12 2013".

## Getting started

### Fixing a polluted source tree

If you have never used the python build system you can skip this step.

The existing Python build system creates generated source files in
the source tree. The CMake build system will refuse to work if it
detects this so you need to clean your source tree first.

To do this run the following in the root of the repository

```
git clean -nx src
```

This will list everything that will be removed. If you are happy
with this then run.

```
git clean -fx src
```

which will remove the generated source files.

### Unix Makefiles

Run the following in the top level directory of the Z3 repository.

```
mkdir build
cd build
cmake -G "Unix Makefiles" ../
make -j4 # Replace 4 with an appropriate number
```

Note that on some platforms "Unix Makefiles" is the default generator so on those
platforms you don't need to pass ``-G "Unix Makefiles"`` command line option to
``cmake``.

Note there is nothing special about the ``build`` directory name here. You can call
it whatever you like.

Note the "Unix Makefile" generator is a "single" configuration generator which
means you pick the build type (e.g. ``Debug``, ``Release``) when you invoke CMake.
You can set the build type by passing it to the ``cmake`` invocation like so:

```
cmake -G "Unix Makefiles" -DCMAKE_BUILD_TYPE=Release ../
```

See the section on "Build Types" for the different CMake build types.

If you wish to use a different compiler set the CXX and CC environment variables
passed to cmake. This must be done at the very first invocation to ``cmake``
in the build directory because once configuration has happened the compiler
is fixed. If you want to use a different compiler to the one you have already
configured you either need to make a new build directory or delete the contents
of the current build directory and start again.

For example to use clang the ``cmake `` line would be

```
CC=clang CXX=clang++ cmake ../
```

Note that CMake build will detect the target architecture that compiler is set up
to build for and the generated build system will build for that architecture.
If there is a way to tell your compiler to build for a different architecture via
compiler flags then you can set the ``CFLAGS`` and ``CXXFLAGS`` environment variables
to have the build target that architecture.

For example if you are on a x86_64 machine and you want to do a 32-bit build and have
a multilib version of GCC you can run ``cmake`` like this

```
CFLAGS="-m32" CXXFLAGS="-m32" CC=gcc CXX=g++ cmake ../
```

Note like with the ``CC`` and ``CXX`` flags this must be done on the very first invocation
to CMake in the build directory.

### Adding Z3 as a dependency to a CMAKE Project

CMake's [FetchContent](https://cmake.org/cmake/help/latest/module/FetchContent.html) allows
the fetching and populating of an external project. This is useful when a certain version
of z3 is required that may not match with the system version. With the following code in the 
cmake file of your project, z3 version 4.12.1 is downloaded to the build directory and the
cmake targets are added to the project:

```cmake
include(FetchContent)
FetchContent_Declare(Z3
        GIT_REPOSITORY https://github.com/Z3Prover/z3
        GIT_TAG        z3-4.15.3
)
FetchContent_MakeAvailable(Z3)

# Add the C++ API include directory for z3++.h
if(TARGET libz3)
    target_include_directories(libz3 INTERFACE
        $<BUILD_INTERFACE:${z3_SOURCE_DIR}/src/api/c++>
    )
endif()
```

Once fetched, you can link the z3 library to your target:

```cmake
target_link_libraries(yourTarget PRIVATE libz3)
```

**Important notes for FetchContent approach**:
- The target name is `libz3` (referring to the library target from `src/CMakeLists.txt`)
- An additional include directory for `src/api/c++` is added to enable `#include "z3++.h"` in C++ code
- Without the additional include directory, you would need `#include "c++/z3++.h"` instead

**Recommended: Create an alias for consistency with system installs**:

```cmake
# Create an alias for consistency with system install
if(NOT TARGET z3::libz3)
    add_library(z3::libz3 ALIAS libz3)
endif()
target_link_libraries(yourTarget PRIVATE z3::libz3)
```

#### Using system-installed Z3

If you have Z3 installed on your system (e.g., via package manager or by building and installing Z3 yourself), you can use CMake's `find_package` to locate it:

```cmake
set(Z3_MIN_VERSION "4.15.3")
find_package(Z3 ${Z3_MIN_VERSION} REQUIRED CONFIG)
```

Once found, you can link to Z3 using the exported target (recommended):

```cmake
target_link_libraries(yourTarget PRIVATE z3::libz3)
```

**Alternative using variables** (for compatibility with older CMake code):

```cmake
# For C projects
target_include_directories(yourTarget PRIVATE ${Z3_C_INCLUDE_DIRS})
target_link_libraries(yourTarget PRIVATE ${Z3_LIBRARIES})

# For C++ projects  
target_include_directories(yourTarget PRIVATE ${Z3_CXX_INCLUDE_DIRS})
target_link_libraries(yourTarget PRIVATE ${Z3_LIBRARIES})
```

The `find_package(Z3 CONFIG)` approach uses Z3's provided `Z3Config.cmake` file, which is installed to a standard location (typically `<prefix>/lib/cmake/z3/`). If CMake cannot automatically find Z3, you can help it by setting `-DZ3_DIR=<path>` where `<path>` is the directory containing the `Z3Config.cmake` file.

**Note**: This approach requires that Z3 was built and installed using CMake. Z3 installations from the Python build system may not provide the necessary CMake configuration files. The exported target `z3::libz3` automatically provides the correct include directories and linking flags.

#### Using system-installed Z3 with FetchContent fallback

This approach combines the benefits of both methods above: it uses a system-installed Z3 if available and meets the minimum version requirement, otherwise falls back to fetching Z3 from the repository. This is often the most practical approach for projects.

```cmake
set(Z3_MIN_VERSION "4.15.3")

# First, try to find Z3 on the system
find_package(Z3 ${Z3_MIN_VERSION} CONFIG QUIET)

if(Z3_FOUND)
    message(STATUS "Found system Z3 version ${Z3_VERSION_STRING}")
    # Z3_LIBRARIES will contain z3::libz3
else()
    message(STATUS "System Z3 not found or version too old, fetching Z3 ${Z3_MIN_VERSION}")
    
    # Fallback to FetchContent
    include(FetchContent)
    FetchContent_Declare(Z3
        GIT_REPOSITORY https://github.com/Z3Prover/z3
        GIT_TAG        z3-${Z3_MIN_VERSION}
    )
    FetchContent_MakeAvailable(Z3)
    
    # Add the C++ API include directory for z3++.h
    if(TARGET libz3)
        target_include_directories(libz3 INTERFACE
            $<BUILD_INTERFACE:${z3_SOURCE_DIR}/src/api/c++>
        )
    endif()
    
    # Create an alias to match the system install target name
    if(NOT TARGET z3::libz3)
        add_library(z3::libz3 ALIAS libz3)
    endif()
endif()

# Now use Z3 consistently regardless of how it was found
target_link_libraries(yourTarget PRIVATE z3::libz3)
```

**Key benefits of this approach:**

- **Consistent interface**: Both paths result in the same `z3::libz3` target
- **Version control**: Ensures minimum version requirements are met
- **Flexible deployment**: Works whether Z3 is pre-installed or not
- **Proper linking**: Uses CMake targets which handle include directories and linking automatically

**Important notes:**

- Use `z3::libz3` target instead of raw library names for better CMake integration
- The target automatically provides the correct include directories, so no need for manual `target_include_directories`
- When using FetchContent, an alias is created to ensure target name consistency
- Set `QUIET` in `find_package` to avoid error messages when Z3 isn't found


### Ninja

[Ninja](https://ninja-build.org/) is a simple build system that is built for speed.
It can be significantly faster than "UNIX Makefile"s because it is not a recursive
build system and thus doesn't create a new process every time it traverses into a directory.
Ninja is particularly appropriate if you want fast incremental building.

Basic usage is as follows:

```
mkdir build
cd build
cmake -G "Ninja" ../
ninja
```

Note the discussion of the ``CC``, ``CXX``, ``CFLAGS`` and ``CXXFLAGS`` for "Unix Makefiles"
also applies here.

Note also that like the "Unix Makefiles" generator, the "Ninja" generator is a single configuration
generator so you pick the build type when you invoke ``cmake`` by passing ``CMAKE_BUILD_TYPE=<build_type>``
to ``cmake``. See the section on "Build Types".

Note that Ninja runs in parallel by default. Use the ``-j`` flag to change this.

Note that Ninja also runs on Windows. You just need to run ``cmake`` in an
environment where the compiler can be found. If you have Visual Studio
installed it typically ships with a "Developer Command Prompt Window" that you
can use which has the environment variables setup for you.

### NMake

NMake is a build system that ships with Visual Studio. You are advised to use
Ninja instead which is significantly faster due to supporting concurrent
builds. However CMake does support NMake if you wish to use it. Note that
NMake is a single configuration generator so you must set ``CMAKE_BUILD_TYPE``
to set the build type.

Basic usage:

1. Launch the "Developer Command Prompt Windows"
2. Change to the root of the Z3 repository

```
mkdir build
cd build
cmake -G "NMake Makefiles" ../
nmake
```

### Visual Studio

Visual Studio 19 comes with integrated support for CMake.
It suffices to open the (z3) folder where this file and the Z3 project CMakeLists.txt resides, 
and Visual Studio does the rest.

For legacy versions of Visual Studio a process is as follows:
For the Visual Studio generators you need to know which version of 
Visual Studio you wish to use and also what architecture you want to build for.

We'll use the ``cmake-gui`` here as it is easier to pick the right generator but this can
be scripted if need be.

Here are the basic steps:

1. Create an empty build directory
2. Start the cmake-gui program
3. Set "where is the source code" to the root of the Z3 project repository. You can do this by pressing
   the "Browse Source..." button and picking the directory.
4. Set "where to build the binaries" to the empty build directory you just created. You can do this
   by pressing the "Browse build..." button and picking the directory.
5. Press the "Configure" button
6. A window will appear asking you to pick the generator to use. Pick the
   generator that matches the version of Visual Studio you are using. Note also
   that some of the generator names contain ``Win64`` (e.g. ``Visual Studio 12
   2013 Win64``) this indicates a x86 64-bit build. Generator names without
   this (e.g. ``Visual Studio 12 2013``) are x86 32-bit build.
7. Press the "Finish" button and wait for CMake to finish it's first configure.
8. A set of configuration options will appear which will affect various aspects of the build.
   Change them as you desire. If you change a set of options press the "Configure"
   again. Additional options may appear when you do this.
9. When you have finished changing configuration options press the "Generate" button.
10. When generation is done close cmake-gui.
11. In the build directory open the generated ``Z3.sln`` solution file created by CMake with
    Visual Studio.
12. In Visual Studio pick the build type (e.g. ``Debug``, ``Release``) you want.
13. Click "BUILD > Build Solution".

Note that unlike the "Unix Makefile" and "Ninja" generators the Visual Studio generators
are multi-configuration generators which means you don't set the build type when invoking
CMake. Instead you set the build type inside Visual Studio. See the "Build Type" section
for more information.

### General workflow

The general workflow when using CMake is the following

1. Create a new build directory
2. Configure the project
3. Generate the build system
4. Invoke the build system to build the project

To perform steps 2 and 3 you can choose from three different tools

* cmake
* ccmake
* cmake-gui

``cmake`` is a command line tool and is what you should use if you are
writing a script to build Z3. This tool performs steps 1 and 2 in one
go without user interaction. The ``ccmake`` and ``cmake-gui`` tools are
more interactive and allow you to change various options. In both these
tools the basic steps to follow are:

1. Configure.
2. Change any options you wish. Every time you change a set of options
   You should configure again. This may cause new options to appear
3. Generate.

For information see https://cmake.org/runningcmake/

Note when invoking CMake you give it the path to the source directory.
This is the top-level directory in the Z3 repository containing a
``CMakeLists.txt``. That file should contain the line ``project(Z3 C CXX)``.
If you give it a path deeper into the Z3 repository (e.g. the ``src`` directory)
the configure step will fail.

## Build Types

Several build types are supported.

* Release
* Debug
* RelWithDebInfo
* MinSizeRel

For the single configuration generators (e.g. "Unix Makefile" and "Ninja") you set the
build type when invoking ``cmake`` by passing ``-DCMAKE_BUILD_TYPE=<build_type>`` where
``<build_type>`` is one of the build types specified above.

For multi-configuration generators (e.g. Visual Studio) you don't set the build type
when invoking CMake and instead set the build type within Visual Studio itself.

## MSVC Security Features

When building with Microsoft Visual C++ (MSVC), Z3 automatically enables several security features by default:

### Control Flow Guard (CFG)
- **CMake Option**: `Z3_ENABLE_CFG` - Defaults to `ON` for MSVC builds
- **Compiler flag**: `/guard:cf` - Automatically enabled when `Z3_ENABLE_CFG=ON`
- **Linker flag**: `/GUARD:CF` - Automatically enabled when `Z3_ENABLE_CFG=ON`
- **Purpose**: Control Flow Guard analyzes control flow for indirect call targets at compile time and inserts runtime verification code to detect attempts to compromise your code by redirecting control flow to attacker-controlled locations
- **Note**: Automatically enables `/DYNAMICBASE` as required by `/GUARD:CF`

### Address Space Layout Randomization (ASLR)
- **Linker flag**: `/DYNAMICBASE` - Enabled when Control Flow Guard is active
- **Purpose**: Randomizes memory layout to make exploitation more difficult
- **Note**: Required for Control Flow Guard to function properly

### Incompatibilities
Control Flow Guard is incompatible with:
- `/ZI` (Edit and Continue debug information format)
- `/clr` (Common Language Runtime compilation)

When these incompatible options are detected, Control Flow Guard will be automatically disabled with a warning message.

### Disabling Control Flow Guard
To disable Control Flow Guard, set the CMake option:
```bash
cmake -DZ3_ENABLE_CFG=OFF ../
```

## Useful options

The following useful options can be passed to CMake whilst configuring.

* ``CMAKE_BUILD_TYPE`` - STRING. The build type to use. Only relevant for single configuration generators (e.g. "Unix Makefile" and "Ninja").
* ``CMAKE_INSTALL_BINDIR`` - STRING. The path to install z3 binaries (relative to ``CMAKE_INSTALL_PREFIX``), e.g. ``bin``.
* ``CMAKE_INSTALL_INCLUDEDIR`` - STRING. The path to install z3 include files (relative to ``CMAKE_INSTALL_PREFIX``), e.g. ``include``.
* ``CMAKE_INSTALL_LIBDIR`` - STRING. The path to install z3 libraries (relative to ``CMAKE_INSTALL_PREFIX``), e.g. ``lib``.
* ``CMAKE_INSTALL_PREFIX`` - STRING. The install prefix to use (e.g. ``/usr/local/``).
* ``CMAKE_INSTALL_PKGCONFIGDIR`` - STRING. The path to install pkgconfig files.
* ``CMAKE_INSTALL_PYTHON_PKG_DIR`` - STRING. The path to install the z3 python bindings. This can be relative (to ``CMAKE_INSTALL_PREFIX``) or absolute.
* ``CMAKE_INSTALL_Z3_CMAKE_PACKAGE_DIR`` - STRING. The path to install CMake package files (e.g. ``/usr/lib/cmake/z3``).
* ``CMAKE_INSTALL_API_BINDINGS_DOC`` - STRING. The path to install documentation for API bindings.
* ``Python3_EXECUTABLE`` - STRING. The python executable to use during the build.
* ``Z3_ENABLE_TRACING_FOR_NON_DEBUG`` - BOOL. If set to ``TRUE`` enable tracing in non-debug builds, if set to ``FALSE`` disable tracing in non-debug builds. Note in debug builds tracing is always enabled.
* ``Z3_BUILD_LIBZ3_SHARED`` - BOOL. If set to ``TRUE`` build libz3 as a shared library otherwise build as a static library.
* ``Z3_BUILD_LIBZ3_CORE`` - BOOL. If set to ``TRUE`` (default) build the core libz3 library. If set to ``FALSE``, skip building libz3 and look for a pre-installed library instead. This is useful when building only Python bindings on top of an already-installed libz3.
* ``Z3_ENABLE_EXAMPLE_TARGETS`` - BOOL. If set to ``TRUE`` add the build targets for building the API examples.
* ``Z3_USE_LIB_GMP`` - BOOL. If set to ``TRUE`` use the GNU multiple precision library. If set to ``FALSE`` use an internal implementation.
* ``Z3_BUILD_PYTHON_BINDINGS`` - BOOL. If set to ``TRUE`` then Z3's python bindings will be built. When ``Z3_BUILD_LIBZ3_CORE`` is ``FALSE``, this will build only the Python bindings using a pre-installed libz3.
* ``Z3_INSTALL_PYTHON_BINDINGS`` - BOOL. If set to ``TRUE`` and ``Z3_BUILD_PYTHON_BINDINGS`` is ``TRUE`` then running the ``install`` target will install Z3's Python bindings.
* ``Z3_BUILD_DOTNET_BINDINGS`` - BOOL. If set to ``TRUE`` then Z3's .NET bindings will be built.
* ``Z3_INSTALL_DOTNET_BINDINGS`` - BOOL. If set to ``TRUE`` and ``Z3_BUILD_DOTNET_BINDINGS`` is ``TRUE`` then running the ``install`` target will install Z3's .NET bindings.
* ``Z3_DOTNET_CSC_EXECUTABLE`` - STRING. The path to the C# compiler to use. Only relevant if ``Z3_BUILD_DOTNET_BINDINGS`` is set to ``TRUE``.
* ``Z3_DOTNET_GACUTIL_EXECUTABLE`` - STRING. The path to the gacutil program to use. Only relevant if ``BUILD_DOTNET_BINDINGS`` is set to ``TRUE``.
* ``Z3_BUILD_JAVA_BINDINGS`` - BOOL. If set to ``TRUE`` then Z3's Java bindings will be built.
* ``Z3_INSTALL_JAVA_BINDINGS`` - BOOL. If set to ``TRUE`` and ``Z3_BUILD_JAVA_BINDINGS`` is ``TRUE`` then running the ``install`` target will install Z3's Java bindings.
* ``Z3_JAVA_JAR_INSTALLDIR`` - STRING. The path to directory to install the Z3 Java ``.jar`` file. This path should be relative to ``CMAKE_INSTALL_PREFIX``.
* ``Z3_JAVA_JNI_LIB_INSTALLDIRR`` - STRING. The path to directory to install the Z3 Java JNI bridge library. This path should be relative to ``CMAKE_INSTALL_PREFIX``.
* ``Z3_BUILD_GO_BINDINGS`` - BOOL. If set to ``TRUE`` then Z3's Go bindings will be built. Requires Go 1.20+ and ``Z3_BUILD_LIBZ3_SHARED=ON``.
* ``Z3_BUILD_OCAML_BINDINGS`` - BOOL. If set to ``TRUE`` then Z3's OCaml bindings will be built.
* ``Z3_BUILD_JULIA_BINDINGS`` - BOOL. If set to ``TRUE`` then Z3's Julia bindings will be built.
* ``Z3_INSTALL_JULIA_BINDINGS`` - BOOL. If set to ``TRUE`` and ``Z3_BUILD_JULIA_BINDINGS`` is ``TRUE`` then running the ``install`` target will install Z3's Julia bindings.
* ``Z3_INCLUDE_GIT_DESCRIBE`` - BOOL. If set to ``TRUE`` and the source tree of Z3 is a git repository then the output of ``git describe`` will be included in the build.
* ``Z3_INCLUDE_GIT_HASH`` - BOOL. If set to ``TRUE`` and the source tree of Z3 is a git repository then the git hash will be included in the build.
* ``Z3_BUILD_DOCUMENTATION`` - BOOL. If set to ``TRUE`` then documentation for the API bindings can be built by invoking the ``api_docs`` target.
* ``Z3_INSTALL_API_BINDINGS_DOCUMENTATION`` - BOOL. If set to ``TRUE`` and ``Z3_BUILD_DOCUMENTATION` is ``TRUE`` then documentation for API bindings will be installed
    when running the ``install`` target.
* ``Z3_ALWAYS_BUILD_DOCS`` - BOOL. If set to ``TRUE`` and ``Z3_BUILD_DOCUMENTATION`` is ``TRUE`` then documentation for API bindings will always be built.
    Disabling this is useful for faster incremental builds. The documentation can be manually built by invoking the ``api_docs`` target.
* ``Z3_LINK_TIME_OPTIMIZATION`` - BOOL. If set to ``TRUE`` link time optimization will be enabled.
* ``Z3_ENABLE_CFI`` - BOOL. If set to ``TRUE`` will enable Control Flow Integrity security checks. This is only supported by Clang and will
    fail on other compilers. This requires Z3_LINK_TIME_OPTIMIZATION to also be enabled.
* ``Z3_ENABLE_CFG`` - BOOL. If set to ``TRUE`` will enable Control Flow Guard security checks. This is only supported by MSVC and will
    fail on other compilers. This does not require link time optimization. Control Flow Guard is enabled by default for MSVC builds.
    Note: Control Flow Guard is incompatible with ``/ZI`` (Edit and Continue debug information) and ``/clr`` (Common Language Runtime compilation).
* ``Z3_API_LOG_SYNC`` - BOOL. If set to ``TRUE`` will enable experimental API log sync feature.
* ``WARNINGS_AS_ERRORS`` - STRING. If set to ``ON`` compiler warnings will be treated as errors. If set to ``OFF`` compiler warnings will not be treated as errors.
    If set to ``SERIOUS_ONLY`` a subset of compiler warnings will be treated as errors.
* ``Z3_C_EXAMPLES_FORCE_CXX_LINKER`` - BOOL. If set to ``TRUE`` the C API examples will request that the C++ linker is used rather than the C linker.
* ``Z3_BUILD_EXECUTABLE`` - BOOL. If set to ``TRUE`` build the z3 executable. Defaults to ``TRUE`` unless z3 is being built as a submodule in which case it defaults to ``FALSE``.
* ``Z3_BUILD_TEST_EXECUTABLES`` - BOOL. If set to ``TRUE`` build the z3 test executables. Defaults to ``TRUE`` unless z3 is being built as a submodule in which case it defaults to ``FALSE``.
* ``Z3_SAVE_CLANG_OPTIMIZATION_RECORDS`` - BOOL. If set to ``TRUE`` saves Clang optimization records by setting the compiler flag ``-fsave-optimization-record``.
* ``Z3_SINGLE_THREADED`` - BOOL. If set to ``TRUE`` compiles Z3 for single threaded mode.
* ``Z3_POLLING_TIMER`` - BOOL. If set to ``TRUE`` compiles Z3 to use polling based timer instead of requiring a thread. This is useful for wasm builds and avoids spawning threads that interfere with how WASM is run.
* ``Z3_ADDRESS_SANITIZE`` - BOOL. If set to ``TRUE`` compiles Z3 with address sanitization enabled. 


On the command line these can be passed to ``cmake`` using the ``-D`` option. In ``ccmake`` and ``cmake-gui`` these can be set in the user interface.

Example

```
cmake -DCMAKE_BUILD_TYPE=Release -DZ3_ENABLE_TRACING_FOR_NON_DEBUG=FALSE ../

```

## Z3 API Bindings

Z3 exposes various language bindings for its API. Below are some notes on building
and/or installing these bindings when building Z3 with CMake.

### Python bindings

#### Building Python bindings with libz3

The default behavior when ``Z3_BUILD_PYTHON_BINDINGS=ON`` is to build both the libz3 library
and the Python bindings together:

```
mkdir build
cd build
cmake -DZ3_BUILD_PYTHON_BINDINGS=ON -DZ3_BUILD_LIBZ3_SHARED=ON ../
make
```

#### Building only Python bindings (using pre-installed libz3)

For package managers like conda-forge that want to avoid rebuilding libz3 for each Python version,
you can build only the Python bindings by setting ``Z3_BUILD_LIBZ3_CORE=OFF``. This assumes
libz3 is already installed on your system:

```
# First, build and install libz3 (once)
mkdir build-libz3
cd build-libz3
cmake -DZ3_BUILD_LIBZ3_SHARED=ON -DCMAKE_INSTALL_PREFIX=/path/to/prefix ../
make
make install

# Then, build Python bindings for each Python version (quickly, without rebuilding libz3)
cd ..
mkdir build-py310
cd build-py310
cmake -DZ3_BUILD_LIBZ3_CORE=OFF \
      -DZ3_BUILD_PYTHON_BINDINGS=ON \
      -DCMAKE_INSTALL_PREFIX=/path/to/prefix \
      -DPython3_EXECUTABLE=/path/to/python3.10 ../
make
make install
```

This approach significantly reduces build time when packaging for multiple Python versions,
as the expensive libz3 compilation happens only once.

### Java bindings

The CMake build uses the ``FindJava`` and ``FindJNI`` cmake modules to detect the
installation of Java. If CMake fails to find your installation of Java set the
``JAVA_HOME`` environment variable when invoking CMake so that it points at the
correct location. For example

```
JAVA_HOME=/usr/lib/jvm/default cmake -DZ3_BUILD_JAVA_BINDINGS=ON ../
```
Note that the built ``.jar`` file is named ``com.microsoft.z3-VERSION.jar``
where ``VERSION`` is the Z3 version. Under non Windows systems a
symbolic link named ``com.microsoft.z3.jar`` is provided. This symbolic
link is not created when building under Windows.

### Go bindings

Go bindings can be built by setting ``Z3_BUILD_GO_BINDINGS=ON``. The Go bindings use CGO to wrap
the Z3 C API, so you'll need:

* Go 1.20 or later installed on your system
* ``Z3_BUILD_LIBZ3_SHARED=ON`` (Go bindings require the shared library)

Example:

```
mkdir build
cd build
cmake -DZ3_BUILD_GO_BINDINGS=ON -DZ3_BUILD_LIBZ3_SHARED=ON ../
make
```

If CMake detects a Go installation (via ``go`` executable in PATH), it will create two optional targets:

* ``go-bindings`` - Builds the Go bindings
* ``test-go-examples`` - Runs the Go examples

Note that the Go bindings are installed as source files (not compiled) since Go packages are
typically distributed as source and compiled by the user's Go toolchain.

To use the installed Go bindings, set the appropriate CGO flags:

```
export CGO_CFLAGS="-I/path/to/z3/include"
export CGO_LDFLAGS="-L/path/to/z3/lib -lz3"
export LD_LIBRARY_PATH="/path/to/z3/lib:$LD_LIBRARY_PATH"  # Linux/macOS
```

For detailed usage examples and API documentation, see ``src/api/go/README.md`` and ``examples/go/``.

## Developer/packager notes

These notes are help developers and packagers of Z3.

### Install/Uninstall

Install and uninstall targets are supported. Use ``CMAKE_INSTALL_PREFIX`` to
set the install prefix. If you also need to control which directories are
used for install set the documented ``CMAKE_INSTALL_*`` options.

To install run

```
make install
```

To uninstall run

```
make uninstall
```

Note that ``DESTDIR`` is supported for [staged installs](https://www.gnu.org/prep/standards/html_node/DESTDIR.html).

To install

```
mkdir staged
make install DESTDIR=/full/path/to/staged/
```

to uninstall

```
make uninstall DESTDIR=/full/path/to/staged
```

The above also works for Ninja but ``DESTDIR`` must be an environment variable instead.

### Examining invoked commands

If you are using the "UNIX Makefiles" generator and want to see exactly the commands that are
being run you can pass ``VERBOSE=1`` to make.

```
make VERBOSE=1
```

If you are using Ninja you can use the ``-v`` flag.

### Additional targets

To see the list of targets run

```
make help
```

There are a few special targets:

* ``clean`` all the built targets in the current directory and below
* ``edit_cache`` will invoke one of the CMake tools (depending on which is available) to let you change configuration options.
* ``rebuild_cache`` will reinvoke ``cmake`` for the project.
* ``api_docs`` will build the documentation for the API bindings.

### Setting build type specific flags

The build system supports single configuration and multi-configuration generators. This means
it is not possible to know the build type at configure time and therefore ``${CMAKE_BUILD_TYPE}``
should not be conditionally used to set compiler flags or definitions. Instead you should use Generator expressions which are evaluated by the generator.

For example

```
$<$<CONFIG:Debug>:Z3DEBUG>
```

If the build type at build time is ``Debug`` this evaluates to ``Z3DEBUG`` but evaluates to nothing for all other configurations. You can see examples of this in the ``CMakeLists.txt`` files.

### File-globbing

It is tempting use file-globbing in ``CMakeLists.txt`` to find a set for files matching a pattern and
use them as the sources to build a target. This however is a bad idea because it prevents CMake from knowing when it needs to rerun itself. This is why source file names are explicitly listed in the ``CMakeLists.txt`` so that when changes are made the source files used to build a target automatically triggers a rerun of CMake.

Long story short. Don't use file globbing.

### Serious warning flags

By default the `WARNINGS_AS_ERRORS` flag is set to `SERIOUS_ONLY` which means
some warnings will be treated as errors. These warnings are controlled by the
relevant `*_WARNINGS_AS_ERRORS` list defined in
`cmake/compiler_warnings.cmake`.

Additional warnings should only be added here if the warnings has no false
positives.

### Building TPTP with CMAKE


Build instructions:

1. cd z3
2. mkdir release
3. cd release
4. cmake3 -DZ3_BUILD_LIBZ3_SHARED=FALSE -DCMAKE_BUILD_TYPE=RelWithDebInfo -G "Unix Makefiles" ../
5. make
6. make z3_tptp5
7. cp examples/tptp_build_dir/z3_tptp5 ../../bin/z3_tptp