# Enforce some CMake policies
cmake_minimum_required(VERSION 3.30)

file(STRINGS scripts/VERSION.txt Z3_VERSION)
project(Z3 VERSION ${Z3_VERSION} LANGUAGES CXX)

################################################################################
# Project version
################################################################################
set(Z3_FULL_VERSION_STR "${Z3_VERSION}") # Note this might be modified
message(STATUS "Z3 version ${Z3_VERSION}")

################################################################################
# Message for polluted source tree sanity checks
################################################################################
set(z3_polluted_tree_msg
  " should not exist and is polluting the source tree."
  " It is likely that this file came from the Python build system which"
  " generates files inside the source tree. This is bad practice and the CMake"
  " build system is setup to make sure that the source tree is clean during"
  " its configure step. If you are using git you can remove all untracked files"
  " using ``git clean -fx``. Be careful when doing this. You should probably use"
  " this with ``-n`` first to check which file(s) would be removed."
)

################################################################################
# Sanity check - Disallow building in source
################################################################################
if (PROJECT_SOURCE_DIR STREQUAL PROJECT_BINARY_DIR)
  message(FATAL_ERROR "In source builds are not allowed. You should invoke "
          "CMake from a different directory.")
endif()

################################################################################
# Add our CMake module directory to the list of module search directories
################################################################################
list(APPEND CMAKE_MODULE_PATH "${PROJECT_SOURCE_DIR}/cmake/modules")

################################################################################
# Handle git hash and description
################################################################################
include(${PROJECT_SOURCE_DIR}/cmake/git_utils.cmake)
option(Z3_INCLUDE_GIT_HASH "Include git hash in version output" ON)
option(Z3_INCLUDE_GIT_DESCRIBE "Include git describe output in version output" ON)

if (Z3_INCLUDE_GIT_HASH OR Z3_INCLUDE_GIT_DESCRIBE)
  # Reconfigure automatically when the git HEAD changes (e.g. a new commit
  # or checkout) so this version information stays up to date.
  add_git_dir_dependency(ADD_GIT_DEP_SUCCESS)
  if (NOT ADD_GIT_DEP_SUCCESS)
    message(WARNING "Could not track git HEAD for automatic reconfiguration")
  endif()

  if (Z3_INCLUDE_GIT_HASH)
    call_git(Z3GITHASH rev-parse -q HEAD)
    if (Z3GITHASH)
      message(STATUS "Using Git hash in version output: ${Z3GITHASH}")
      # This mimics the behaviour of the old build system.
      set(Z3_FULL_VERSION_STR "${Z3_FULL_VERSION_STR} ${Z3GITHASH}")
    else()
      message(WARNING "Failed to get Git hash; disabling Z3_INCLUDE_GIT_HASH")
      set(Z3_INCLUDE_GIT_HASH OFF CACHE BOOL "Include git hash in version output" FORCE)
    endif()
  endif()

  if (Z3_INCLUDE_GIT_DESCRIBE)
    call_git(Z3_GIT_DESCRIPTION describe --tags)
    if (Z3_GIT_DESCRIPTION)
      message(STATUS "Using Git description in version output: ${Z3_GIT_DESCRIPTION}")
      # This mimics the behaviour of the old build system.
      set(Z3_FULL_VERSION_STR "${Z3_FULL_VERSION_STR} ${Z3_GIT_DESCRIPTION}")
    else()
      message(WARNING "Failed to get Git description; disabling Z3_INCLUDE_GIT_DESCRIBE")
      set(Z3_INCLUDE_GIT_DESCRIBE OFF CACHE BOOL "Include git describe output in version output" FORCE)
    endif()
  endif()
endif()

if (NOT Z3_INCLUDE_GIT_HASH)
  unset(Z3GITHASH) # Used in configure_file()
endif()

################################################################################
# Useful CMake functions/Macros
################################################################################
include(CheckCXXSourceCompiles)
include(CMakeDependentOption)

################################################################################
# Core library options
################################################################################
# Z3_BUILD_LIBZ3_SHARED was Z3's historical spelling. Honor it when supplied
# by existing build scripts, but use CMake's standard switch internally.
if (DEFINED Z3_BUILD_LIBZ3_SHARED)
  set(BUILD_SHARED_LIBS "${Z3_BUILD_LIBZ3_SHARED}")
endif()
option(BUILD_SHARED_LIBS "Build libraries as shared libraries" ON)
option(Z3_BUILD_LIBZ3_CORE "Build the core libz3 library" ON)
option(Z3_BUILD_PYTHON_BINDINGS "Build Python bindings for Z3" OFF)
option(Z3_BUILD_LIBZ3_MSVC_STATIC
  "Build libz3 as a statically-linked runtime library" OFF)

if (BUILD_SHARED_LIBS)
  set(Z3_LIBZ3_VARIANT shared)
else()
  set(Z3_LIBZ3_VARIANT static)
endif()

if (MSVC AND Z3_BUILD_LIBZ3_MSVC_STATIC)
  set(CMAKE_MSVC_RUNTIME_LIBRARY
    "MultiThreaded$<$<CONFIG:Debug>:Debug>")
endif()

################################################################################
# Internal build requirements.  This target is deliberately not exported:
# these settings are required to build Z3, not to consume its public API.
################################################################################
add_library(z3_internal_options INTERFACE)
target_compile_features(z3_internal_options INTERFACE cxx_std_20)

# Common requirements for Z3's targets. Build-only compiler and linker policy
# disappears from exports, leaving only dependencies needed by static users.
add_library(z3_common INTERFACE)
set_target_properties(z3_common PROPERTIES EXPORT_NAME _common)
target_link_libraries(z3_common INTERFACE
  "$<BUILD_LOCAL_INTERFACE:z3_internal_options>")

################################################################################
# Build type
################################################################################
message(STATUS "CMake generator: ${CMAKE_GENERATOR}")
set(available_build_types Debug Release RelWithDebInfo MinSizeRel)
get_property(Z3_MULTI_CONFIG GLOBAL PROPERTY GENERATOR_IS_MULTI_CONFIG)
if (Z3_MULTI_CONFIG)
  # Multi-configuration build (e.g. Visual Studio and Xcode). Here
  # CMAKE_BUILD_TYPE doesn't matter
  message(STATUS "Available configurations: ${CMAKE_CONFIGURATION_TYPES}")
else()
  # Single configuration generator (e.g. Unix Makefiles, Ninja)
  if (PROJECT_IS_TOP_LEVEL AND NOT CMAKE_BUILD_TYPE)
    message(STATUS "CMAKE_BUILD_TYPE is not set. Setting default")
    message(STATUS "The available build types are: ${available_build_types}")
    set(CMAKE_BUILD_TYPE RelWithDebInfo CACHE STRING
      "Options are ${available_build_types}"
      FORCE
    )
    # Provide drop down menu options in cmake-gui
    set_property(CACHE CMAKE_BUILD_TYPE PROPERTY STRINGS ${available_build_types})
  endif()
  if (CMAKE_BUILD_TYPE)
    message(STATUS "Build type: ${CMAKE_BUILD_TYPE}")
  endif()
endif()

# CMAKE_BUILD_TYPE has no meaning for multi-configuration generators
# (e.g. Visual Studio) so use generator expressions instead to add
# the right definitions when doing a particular build type.
#
# Note for some reason we have to leave off ``-D`` here otherwise
# we get ``-D-DZ3DEBUG`` passed to the compiler
target_compile_definitions(z3_internal_options INTERFACE
  $<$<CONFIG:Debug>:Z3DEBUG>
  $<$<CONFIG:Release>:_EXTERNAL_RELEASE>
  $<$<CONFIG:RelWithDebInfo>:_EXTERNAL_RELEASE>
)

################################################################################
# Find Python
################################################################################
find_package(Python3 REQUIRED COMPONENTS Interpreter)
message(STATUS "Python3_EXECUTABLE: ${Python3_EXECUTABLE}")

################################################################################
# Target architecture detection
################################################################################
include(${PROJECT_SOURCE_DIR}/cmake/target_arch_detect.cmake)
detect_target_architecture(TARGET_ARCHITECTURE)
message(STATUS "Detected target architecture: ${TARGET_ARCHITECTURE}")


################################################################################
# Function for detecting C++ compiler flag support
################################################################################
include(${PROJECT_SOURCE_DIR}/cmake/z3_add_cxx_flag.cmake)

if (CMAKE_SYSTEM_NAME STREQUAL "Darwin"
    AND TARGET_ARCHITECTURE STREQUAL "arm64")
  # Set this before creating targets because it initializes their
  # OSX_ARCHITECTURES property.
  set(CMAKE_OSX_ARCHITECTURES "arm64")
endif()

if (Z3_BUILD_LIBZ3_CORE)
  # Components add their object files to this target as they are declared
  # below. Public headers are attached as file sets in src/CMakeLists.txt.
  add_library(libz3)
  add_library(z3::libz3 ALIAS libz3)
  # z3++.h requires C++11. Use a granular feature because the cxx_std_11
  # meta-feature is newer than the minimum CMake version for package consumers.
  target_compile_features(libz3 INTERFACE cxx_noexcept)
endif()

################################################################################
# Platform detection
################################################################################
if (WIN32)
  message(STATUS "Platform: Windows")
  target_compile_definitions(z3_internal_options INTERFACE _WINDOWS)
  # workaround for #7420
  target_compile_definitions(z3_internal_options INTERFACE
    _DISABLE_CONSTEXPR_MUTEX_CONSTRUCTOR)
  # dbghelp is used in debug.cpp for stack backtraces on Windows.
  # With MSVC this is handled by #pragma comment(lib, "dbghelp.lib") in debug.cpp,
  # but MinGW does not support that pragma, so we add it explicitly here.
  target_link_libraries(z3_common INTERFACE dbghelp)
elseif (EMSCRIPTEN)
  message(STATUS "Platform: Emscripten")
  target_link_options(z3_internal_options INTERFACE
    "-Os"
    "SHELL:-s ALLOW_MEMORY_GROWTH=1"
    "SHELL:-s ASSERTIONS=0"
    # Use native wasm exception handling + wasm longjmp to match the ABI of the
    # Pyodide / modern-emscripten main module. The legacy JS-based EH (which the
    # removed "-s DISABLE_EXCEPTION_CATCHING=0" selected) makes libz3 import
    # invoke_* trampolines the Pyodide runtime no longer provides.
    "-fwasm-exceptions"
    "SHELL:-s SUPPORT_LONGJMP=wasm"
    "SHELL:-s ERROR_ON_UNDEFINED_SYMBOLS=1"
  )
endif()

target_include_directories(z3_internal_options INTERFACE
  "${PROJECT_BINARY_DIR}/src"
  "${PROJECT_SOURCE_DIR}/src"
)

################################################################################
# GNU multiple precision library support
################################################################################
option(Z3_USE_LIB_GMP "Use GNU Multiple Precision Library" OFF)
if (Z3_USE_LIB_GMP)
  # Because this is off by default we will make the configure fail if libgmp
  # can't be found
  find_package(GMP REQUIRED)
  message(STATUS "Using libgmp")
  target_link_libraries(z3_common INTERFACE GMP::GMP)
  target_compile_definitions(z3_internal_options INTERFACE _MP_GMP)
else()
  target_compile_definitions(z3_internal_options INTERFACE _MP_INTERNAL)
  message(STATUS "Not using libgmp")
endif()


################################################################################
# API Log sync
################################################################################
option(Z3_API_LOG_SYNC
  "Use locking when logging Z3 API calls (experimental)"
  OFF
)
if (Z3_API_LOG_SYNC)
  target_compile_definitions(z3_internal_options INTERFACE Z3_LOG_SYNC)
  message(STATUS "Using Z3_API_LOG_SYNC")
else()
  message(STATUS "Not using Z3_API_LOG_SYNC")
endif()

################################################################################
# Thread safe or not?
################################################################################
option(Z3_SINGLE_THREADED
  "Non-thread-safe build"
  OFF
)
if (Z3_SINGLE_THREADED)
  if (Z3_API_LOG_SYNC)
    message(FATAL_ERROR "Z3_API_LOG_SYNC requires threading support and cannot be combined with Z3_SINGLE_THREADED")
  endif()
  target_compile_definitions(z3_internal_options INTERFACE SINGLE_THREAD)
  message(STATUS "Non-thread-safe build")
else()
  message(STATUS "Thread-safe build")
endif()


################################################################################
# Use polling based timeout. This avoids spawning threads for timer tasks
################################################################################
option(Z3_POLLING_TIMER
  "Use polling based timeout checks"
  OFF
)
if (Z3_POLLING_TIMER)
  target_compile_definitions(z3_internal_options INTERFACE POLLING_TIMER)
  message(STATUS "Polling based timer")
endif()



################################################################################
# FP math
################################################################################
# FIXME: Support ARM "-mfpu=vfp -mfloat-abi=hard"
if ((TARGET_ARCHITECTURE STREQUAL "x86_64") OR (TARGET_ARCHITECTURE STREQUAL "i686"))
  if ((CMAKE_CXX_COMPILER_ID MATCHES "GNU") OR (CMAKE_CXX_COMPILER_ID MATCHES "Clang") OR (CMAKE_CXX_COMPILER_ID MATCHES "Intel"))
    set(SSE_FLAGS "-mfpmath=sse" "-msse" "-msse2")
  elseif (CMAKE_CXX_COMPILER_ID STREQUAL "MSVC")
    set(SSE_FLAGS "/arch:SSE2")
  else()
    message(FATAL_ERROR "Unknown compiler ${CMAKE_CXX_COMPILER_ID}")
  endif()
  CHECK_CXX_COMPILER_FLAG("${SSE_FLAGS}" HAS_SSE2)
  if (HAS_SSE2)
    target_compile_options(z3_internal_options INTERFACE ${SSE_FLAGS})
  endif()
  unset(SSE_FLAGS)
endif()

################################################################################
# Threading support
################################################################################
set(THREADS_PREFER_PTHREAD_FLAG TRUE)
find_package(Threads REQUIRED)
target_link_libraries(z3_common INTERFACE Threads::Threads)

################################################################################
# Compiler warnings
################################################################################
include(${PROJECT_SOURCE_DIR}/cmake/compiler_warnings.cmake)


################################################################################
# Address sanitization
################################################################################
option(Z3_ADDRESS_SANITIZE "Set address sanitization." OFF)

if (Z3_ADDRESS_SANITIZE)
  z3_add_cxx_flag("-fsanitize=address" REQUIRED GLOBAL)
endif()

################################################################################
# Save Clang optimization records
################################################################################
option(Z3_SAVE_CLANG_OPTIMIZATION_RECORDS "Enable saving Clang optimization records." OFF)

if (Z3_SAVE_CLANG_OPTIMIZATION_RECORDS)
  z3_add_cxx_flag("-fsave-optimization-record" REQUIRED)
endif()

################################################################################
# If using Ninja, force color output for Clang (and gcc, disabled to check build).
################################################################################
if (UNIX AND CMAKE_GENERATOR STREQUAL "Ninja")
  if (CMAKE_CXX_COMPILER_ID STREQUAL "Clang")
    target_compile_options(z3_internal_options INTERFACE -fcolor-diagnostics)
  endif()
endif()

################################################################################
# Tracing
################################################################################
option(Z3_ENABLE_TRACING_FOR_NON_DEBUG "Enable tracing in non-debug builds." OFF)
if (Z3_ENABLE_TRACING_FOR_NON_DEBUG)
  target_compile_definitions(z3_internal_options INTERFACE _TRACE)
else()
  # Tracing is always enabled in debug builds
  target_compile_definitions(z3_internal_options INTERFACE
    $<$<CONFIG:Debug>:_TRACE>)
endif()

################################################################################
# Link time optimization
################################################################################
include(${PROJECT_SOURCE_DIR}/cmake/compiler_lto.cmake)

################################################################################
# Control flow integrity (Clang only)
################################################################################
option(Z3_ENABLE_CFI "Enable Control Flow Integrity security checks" OFF)
if (Z3_ENABLE_CFI)
  if (NOT CMAKE_CXX_COMPILER_ID MATCHES "Clang")
    message(FATAL_ERROR "Z3_ENABLE_CFI is only supported with Clang compiler. "
      "Current compiler: ${CMAKE_CXX_COMPILER_ID}. "
      "You should set Z3_ENABLE_CFI to OFF or use Clang to compile.")
  endif()

  if (NOT Z3_LINK_TIME_OPTIMIZATION)
    message(FATAL_ERROR "Cannot enable Control Flow Integrity without link-time optimization. "
      "You should set Z3_LINK_TIME_OPTIMIZATION to ON or Z3_ENABLE_CFI to OFF.")
  endif()

  set(build_types_with_cfi "RELEASE" "RELWITHDEBINFO")
  if (Z3_MULTI_CONFIG)
    # Multi configuration generator
    message(STATUS "Note CFI is only enabled for the following configurations: ${build_types_with_cfi}")
    # No need for else because this is the same as the set that LTO requires.
  endif()

  message(STATUS "Enabling Control Flow Integrity (CFI) for Clang")
  z3_add_cxx_flag("-fsanitize=cfi" REQUIRED GLOBAL)
  z3_add_cxx_flag("-fsanitize-cfi-cross-dso" REQUIRED GLOBAL)
endif()
# End CFI section

################################################################################
# Control Flow Guard (MSVC only)
################################################################################
# Default CFG to ON for MSVC, OFF for other compilers.
if (CMAKE_CXX_COMPILER_ID STREQUAL "MSVC")
  option(Z3_ENABLE_CFG "Enable Control Flow Guard security checks" ON)
else()
  option(Z3_ENABLE_CFG "Enable Control Flow Guard security checks" OFF)
endif()

if (Z3_ENABLE_CFG)
  if (NOT CMAKE_CXX_COMPILER_ID STREQUAL "MSVC")
    message(FATAL_ERROR "Z3_ENABLE_CFG is only supported with MSVC compiler. "
      "Current compiler: ${CMAKE_CXX_COMPILER_ID}. "
      "You should remove Z3_ENABLE_CFG or set it to OFF or use MSVC to compile.")
  endif()

  # Check for incompatible options (handle both / and - forms for robustness)
  string(REGEX MATCH "[-/]ZI" _has_ZI "${CMAKE_CXX_FLAGS} ${CMAKE_CXX_FLAGS_DEBUG} ${CMAKE_CXX_FLAGS_RELEASE} ${CMAKE_CXX_FLAGS_RELWITHDEBINFO} ${CMAKE_CXX_FLAGS_MINSIZEREL}")
  string(REGEX MATCH "[-/]clr" _has_clr "${CMAKE_CXX_FLAGS} ${CMAKE_CXX_FLAGS_DEBUG} ${CMAKE_CXX_FLAGS_RELEASE} ${CMAKE_CXX_FLAGS_RELWITHDEBINFO} ${CMAKE_CXX_FLAGS_MINSIZEREL}")

  if(_has_ZI)
    message(WARNING "/guard:cf is incompatible with /ZI (Edit and Continue debug information). "
                   "Control Flow Guard will be disabled due to /ZI option.")
  elseif(_has_clr)
    message(WARNING "/guard:cf is incompatible with /clr (Common Language Runtime compilation). "
                   "Control Flow Guard will be disabled due to /clr option.")
  else()
    # Enable Control Flow Guard if no incompatible options are present
    message(STATUS "Enabling Control Flow Guard (/guard:cf) and ASLR (/DYNAMICBASE) for MSVC")
    z3_add_cxx_flag("/guard:cf" REQUIRED)
    target_link_options(z3_internal_options INTERFACE /GUARD:CF /DYNAMICBASE)
  endif()
else()
  if (CMAKE_CXX_COMPILER_ID STREQUAL "MSVC")
    # Explicitly disable Control Flow Guard when Z3_ENABLE_CFG is OFF
    message(STATUS "Disabling Control Flow Guard (/guard:cf-) for MSVC")
    z3_add_cxx_flag("/guard:cf-" REQUIRED)
    target_link_options(z3_internal_options INTERFACE /GUARD:NO)
  endif()
endif()

################################################################################
# MSVC specific flags inherited from old build system
################################################################################
if (CMAKE_CXX_COMPILER_ID STREQUAL "MSVC")
  include(${PROJECT_SOURCE_DIR}/cmake/msvc_legacy_quirks.cmake)
endif()

################################################################################
# Pass /RELEASE to the linker so that checksums in PE files are calculated.
################################################################################
if (CMAKE_CXX_COMPILER_ID STREQUAL "MSVC")
  target_link_options(z3_internal_options INTERFACE /RELEASE)
endif()

################################################################################
# Check atomic linking as needed
################################################################################
include(${PROJECT_SOURCE_DIR}/cmake/check_link_atomic.cmake)

################################################################################
# Report default CMake flags
################################################################################
# This is mainly for debugging.
message(STATUS "CMAKE_CXX_FLAGS: \"${CMAKE_CXX_FLAGS}\"")
message(STATUS "CMAKE_EXE_LINKER_FLAGS: \"${CMAKE_EXE_LINKER_FLAGS}\"")
message(STATUS "CMAKE_STATIC_LINKER_FLAGS: \"${CMAKE_STATIC_LINKER_FLAGS}\"")
message(STATUS "CMAKE_SHARED_LINKER_FLAGS: \"${CMAKE_SHARED_LINKER_FLAGS}\"")
if (Z3_MULTI_CONFIG)
  # Multi configuration generator
  string(TOUPPER "${available_build_types}" build_types_to_report)
else()
  # Single configuration generator
  string(TOUPPER "${CMAKE_BUILD_TYPE}" build_types_to_report)
endif()
foreach (_build_type ${build_types_to_report})
  message(STATUS "CMAKE_CXX_FLAGS_${_build_type}: \"${CMAKE_CXX_FLAGS_${_build_type}}\"")
  message(STATUS "CMAKE_EXE_LINKER_FLAGS_${_build_type}: \"${CMAKE_EXE_LINKER_FLAGS_${_build_type}}\"")
  message(STATUS "CMAKE_SHARED_LINKER_FLAGS_${_build_type}: \"${CMAKE_SHARED_LINKER_FLAGS_${_build_type}}\"")
  message(STATUS "CMAKE_STATIC_LINKER_FLAGS_${_build_type}: \"${CMAKE_STATIC_LINKER_FLAGS_${_build_type}}\"")
endforeach()

################################################################################
# Z3 installation locations
################################################################################
include(GNUInstallDirs)
set(CMAKE_INSTALL_PKGCONFIGDIR
  "${CMAKE_INSTALL_LIBDIR}/pkgconfig"
  CACHE
  PATH
  "Directory to install pkgconfig files"
)

set(CMAKE_INSTALL_Z3_CMAKE_PACKAGE_DIR
  "${CMAKE_INSTALL_LIBDIR}/cmake/z3"
  CACHE
  PATH
  "Directory to install Z3 CMake package files"
)
message(STATUS "CMAKE_INSTALL_LIBDIR: \"${CMAKE_INSTALL_LIBDIR}\"")
message(STATUS "CMAKE_INSTALL_BINDIR: \"${CMAKE_INSTALL_BINDIR}\"")
message(STATUS "CMAKE_INSTALL_INCLUDEDIR: \"${CMAKE_INSTALL_INCLUDEDIR}\"")
message(STATUS "CMAKE_INSTALL_PKGCONFIGDIR: \"${CMAKE_INSTALL_PKGCONFIGDIR}\"")
message(STATUS "CMAKE_INSTALL_Z3_CMAKE_PACKAGE_DIR: \"${CMAKE_INSTALL_Z3_CMAKE_PACKAGE_DIR}\"")

if (PROJECT_IS_TOP_LEVEL)
  ##############################################################################
  # Uninstall rule
  ##############################################################################
  configure_file(
    "${PROJECT_SOURCE_DIR}/cmake/cmake_uninstall.cmake.in"
    "${CMAKE_CURRENT_BINARY_DIR}/cmake_uninstall.cmake"
    @ONLY
  )

  add_custom_target(uninstall
    COMMAND
    "${CMAKE_COMMAND}" -P "${CMAKE_CURRENT_BINARY_DIR}/cmake_uninstall.cmake"
    COMMENT "Uninstalling..."
    USES_TERMINAL
    VERBATIM
  )
endif()

################################################################################
# CMake build file locations
################################################################################
# To mimic the python build system output these into the root of the build
# directory
set(CMAKE_LIBRARY_OUTPUT_DIRECTORY "${PROJECT_BINARY_DIR}")
set(CMAKE_ARCHIVE_OUTPUT_DIRECTORY "${PROJECT_BINARY_DIR}")
set(CMAKE_RUNTIME_OUTPUT_DIRECTORY "${PROJECT_BINARY_DIR}")

################################################################################
# Extra dependencies for build rules that use the Python infrastructure to
# generate files used for Z3's build. Changes to these files will trigger
# a rebuild of all the generated files.
################################################################################
# Note: ``update_api.py`` is deliberately not here because it is not used
# to generate every generated file. The targets that need it list it explicitly.
set(Z3_GENERATED_FILE_EXTRA_DEPENDENCIES
  "${PROJECT_SOURCE_DIR}/scripts/mk_genfile_common.py"
)

################################################################################
# API header files
################################################################################
# This lists the API header files that are scanned by
# some of the build rules to generate some files needed
# by the build; needs to come before add_subdirectory(src)
set(Z3_API_HEADER_FILES_TO_SCAN
  z3_api.h
  z3_ast_containers.h
  z3_algebraic.h
  z3_polynomial.h
  z3_rcf.h
  z3_fixedpoint.h
  z3_optimization.h
  z3_fpa.h
  z3_spacer.h
)
set(Z3_FULL_PATH_API_HEADER_FILES_TO_SCAN "")
foreach (header_file ${Z3_API_HEADER_FILES_TO_SCAN})
  set(full_path_api_header_file "${CMAKE_CURRENT_SOURCE_DIR}/src/api/${header_file}")
  list(APPEND Z3_FULL_PATH_API_HEADER_FILES_TO_SCAN "${full_path_api_header_file}")
  if (NOT EXISTS "${full_path_api_header_file}")
    message(FATAL_ERROR "API header file \"${full_path_api_header_file}\" does not exist")
  endif()
endforeach()

################################################################################
# Create `Z3Config.cmake` and related files for the build tree so clients can
# use Z3 via CMake.
################################################################################
include(CMakePackageConfigHelpers)

# Only export targets if we built libz3
if (Z3_BUILD_LIBZ3_CORE)
  ################################################################################
  # Z3 components, library and executables
  ################################################################################
  include(${PROJECT_SOURCE_DIR}/cmake/z3_add_component.cmake)
  add_subdirectory(src)

  export(EXPORT Z3_EXPORTED_TARGETS
     NAMESPACE z3::
     FILE "${PROJECT_BINARY_DIR}/Z3-${Z3_LIBZ3_VARIANT}-targets.cmake"
  )
else()
  message(STATUS "Not building libz3; looking for the installed Z3 package")
  # Keep variables set by find_package() from replacing the source tree's
  # version variables. Imported targets are not scoped to variable blocks.
  block(SCOPE_FOR VARIABLES)
    find_package(Z3 ${Z3_VERSION} EXACT CONFIG REQUIRED COMPONENTS shared)
  endblock()
endif()

################################################################################
# Standalone Z3 Python bindings
################################################################################
if (Z3_BUILD_PYTHON_BINDINGS AND NOT Z3_BUILD_LIBZ3_CORE)
  message(STATUS "Building Python bindings with pre-installed libz3")
  add_subdirectory(src/api/python)
endif()

set(Z3_FIRST_PACKAGE_INCLUDE_DIR "${PROJECT_BINARY_DIR}/src/api")
set(Z3_SECOND_PACKAGE_INCLUDE_DIR "${PROJECT_SOURCE_DIR}/src/api")
set(Z3_CXX_PACKAGE_INCLUDE_DIR "${PROJECT_SOURCE_DIR}/src/api/c++")
set(AUTO_GEN_MSG "Automatically generated. DO NOT EDIT")
set(CONFIG_FILE_TYPE "build tree")
configure_package_config_file("${PROJECT_SOURCE_DIR}/cmake/Z3Config.cmake.in"
  "Z3Config.cmake"
  INSTALL_DESTINATION "${PROJECT_BINARY_DIR}"
  PATH_VARS
    Z3_FIRST_PACKAGE_INCLUDE_DIR
    Z3_SECOND_PACKAGE_INCLUDE_DIR
    Z3_CXX_PACKAGE_INCLUDE_DIR
)
unset(Z3_FIRST_PACKAGE_INCLUDE_DIR)
unset(Z3_SECOND_PACKAGE_INCLUDE_DIR)
unset(Z3_CXX_PACKAGE_INCLUDE_DIR)
unset(AUTO_GEN_MSG)
unset(CONFIG_FILE_TYPE)

write_basic_package_version_file("${PROJECT_BINARY_DIR}/Z3ConfigVersion.cmake"
  COMPATIBILITY SameMajorVersion
)

set(Z3_FIND_GMP_MODULE_DIR "${PROJECT_SOURCE_DIR}/cmake/modules")
configure_file(
  "${PROJECT_SOURCE_DIR}/cmake/Z3StaticDependencies.cmake.in"
  "${PROJECT_BINARY_DIR}/Z3-static-dependencies.cmake"
  @ONLY
)
set(Z3_FIND_GMP_MODULE_DIR "\${CMAKE_CURRENT_LIST_DIR}")
configure_file(
  "${PROJECT_SOURCE_DIR}/cmake/Z3StaticDependencies.cmake.in"
  "${PROJECT_BINARY_DIR}/cmake/Z3-static-dependencies.cmake"
  @ONLY
)
unset(Z3_FIND_GMP_MODULE_DIR)

set(Z3_PKGCONFIG_DIR "${CMAKE_INSTALL_PKGCONFIGDIR}")
cmake_path(ABSOLUTE_PATH Z3_PKGCONFIG_DIR
  BASE_DIRECTORY "${CMAKE_INSTALL_PREFIX}"
  NORMALIZE)
set(Z3_PKGCONFIG_PREFIX "${CMAKE_INSTALL_PREFIX}")
cmake_path(RELATIVE_PATH Z3_PKGCONFIG_PREFIX
  BASE_DIRECTORY "${Z3_PKGCONFIG_DIR}")

set(Z3_PKGCONFIG_REQUIRES_PRIVATE "")
if (Z3_USE_LIB_GMP)
  set(Z3_PKGCONFIG_REQUIRES_PRIVATE gmp)
endif()

set(Z3_PKGCONFIG_LIBS_PRIVATE "")
if (CMAKE_THREAD_LIBS_INIT)
  list(APPEND Z3_PKGCONFIG_LIBS_PRIVATE "${CMAKE_THREAD_LIBS_INIT}")
endif()
if (ATOMICS_REQUIRE_LIBATOMIC)
  list(APPEND Z3_PKGCONFIG_LIBS_PRIVATE -latomic)
endif()
if (MINGW)
  list(APPEND Z3_PKGCONFIG_LIBS_PRIVATE -ldbghelp)
endif()
foreach (implicit_lib IN LISTS CMAKE_CXX_IMPLICIT_LINK_LIBRARIES)
  if (implicit_lib MATCHES "^(c\\+\\+|stdc\\+\\+|m)$")
    list(APPEND Z3_PKGCONFIG_LIBS_PRIVATE "-l${implicit_lib}")
  endif()
endforeach()
list(REMOVE_DUPLICATES Z3_PKGCONFIG_LIBS_PRIVATE)
list(JOIN Z3_PKGCONFIG_LIBS_PRIVATE " " Z3_PKGCONFIG_LIBS_PRIVATE)

configure_file("${CMAKE_CURRENT_SOURCE_DIR}/z3.pc.cmake.in"
  "${CMAKE_CURRENT_BINARY_DIR}/z3.pc.configured" @ONLY)
file(GENERATE OUTPUT "${CMAKE_CURRENT_BINARY_DIR}/z3.pc"
  INPUT "${CMAKE_CURRENT_BINARY_DIR}/z3.pc.configured")

################################################################################
# Create `Z3Config.cmake` and related files for install tree so clients can use
# Z3 via CMake.
################################################################################
if (Z3_BUILD_LIBZ3_CORE)
  install(EXPORT
    Z3_EXPORTED_TARGETS
    FILE "Z3-${Z3_LIBZ3_VARIANT}-targets.cmake"
    NAMESPACE z3::
    DESTINATION "${CMAKE_INSTALL_Z3_CMAKE_PACKAGE_DIR}"
  )
  if (NOT BUILD_SHARED_LIBS)
    install(
      FILES "${PROJECT_BINARY_DIR}/cmake/Z3-static-dependencies.cmake"
      DESTINATION "${CMAKE_INSTALL_Z3_CMAKE_PACKAGE_DIR}"
    )
    if (Z3_USE_LIB_GMP)
      install(
        FILES "${PROJECT_SOURCE_DIR}/cmake/modules/FindGMP.cmake"
        DESTINATION "${CMAKE_INSTALL_Z3_CMAKE_PACKAGE_DIR}"
      )
    endif()
  endif()
endif()
set(Z3_INSTALL_TREE_CMAKE_CONFIG_FILE "${PROJECT_BINARY_DIR}/cmake/Z3Config.cmake")
set(Z3_FIRST_PACKAGE_INCLUDE_DIR "${CMAKE_INSTALL_INCLUDEDIR}")
set(Z3_SECOND_INCLUDE_DIR "")
set(Z3_CXX_PACKAGE_INCLUDE_DIR "")
set(AUTO_GEN_MSG "Automatically generated. DO NOT EDIT")
set(CONFIG_FILE_TYPE "install tree")
# We use `configure_package_config_file()` to try and create CMake files
# that are re-locatable so that it doesn't matter if the files aren't placed
# in the original install prefix.
configure_package_config_file("${PROJECT_SOURCE_DIR}/cmake/Z3Config.cmake.in"
  "${Z3_INSTALL_TREE_CMAKE_CONFIG_FILE}"
  INSTALL_DESTINATION "${CMAKE_INSTALL_Z3_CMAKE_PACKAGE_DIR}"
  PATH_VARS Z3_FIRST_PACKAGE_INCLUDE_DIR
)
unset(Z3_FIRST_PACKAGE_INCLUDE_DIR)
unset(Z3_SECOND_PACKAGE_INCLUDE_DIR)
unset(Z3_CXX_PACKAGE_INCLUDE_DIR)
unset(AUTO_GEN_MSG)
unset(CONFIG_FILE_TYPE)

if (Z3_BUILD_LIBZ3_CORE)
  # Add install rule to install ${Z3_INSTALL_TREE_CMAKE_CONFIG_FILE}
  install(
    FILES "${Z3_INSTALL_TREE_CMAKE_CONFIG_FILE}"
    DESTINATION "${CMAKE_INSTALL_Z3_CMAKE_PACKAGE_DIR}"
  )

  # Add install rule to install ${PROJECT_BINARY_DIR}/Z3ConfigVersion.cmake
  install(
    FILES "${PROJECT_BINARY_DIR}/Z3ConfigVersion.cmake"
    DESTINATION "${CMAKE_INSTALL_Z3_CMAKE_PACKAGE_DIR}"
  )

  # Add install rule to install ${PROJECT_BINARY_DIR}/z3.pc
  install(
    FILES "${PROJECT_BINARY_DIR}/z3.pc"
    DESTINATION "${CMAKE_INSTALL_PKGCONFIGDIR}"
  )
endif()

################################################################################
# Examples
################################################################################
cmake_dependent_option(Z3_ENABLE_EXAMPLE_TARGETS
    "Build Z3 api examples" ON
    "PROJECT_IS_TOP_LEVEL;Z3_BUILD_LIBZ3_CORE" OFF)
if (Z3_ENABLE_EXAMPLE_TARGETS)
  add_subdirectory(examples)
endif()

################################################################################
# Documentation
################################################################################
option(Z3_BUILD_DOCUMENTATION "Build API documentation" OFF)
if (Z3_BUILD_DOCUMENTATION)
  message(STATUS "Building documentation enabled")
  add_subdirectory(doc)
else()
  message(STATUS "Building documentation disabled")
endif()
