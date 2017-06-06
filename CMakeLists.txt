# Enforce some CMake policies
cmake_minimum_required(VERSION 2.8.12)
if (POLICY CMP0054)
  # FIXME: This is horrible. With the old behaviour,
  # quoted strings like "MSVC" in if() conditionals
  # get implicitly dereferenced. The NEW behaviour
  # doesn't do this but CMP0054 was only introduced
  # in CMake 3.1 and we support lower versions as the
  # minimum. We could set NEW here but it would be very
  # confusing to use NEW for some builds and OLD for others
  # which could lead to some subtle bugs. Instead when the
  # minimum version is 3.1 change this policy to NEW and remove
  # the hacks in place to work around it.
  cmake_policy(SET CMP0054 OLD)
endif()

# Provide a friendly message if the user hasn't run the bootstrap script
# to copy all the CMake files into their correct location.
# It is unfortunate that we have to do this, see #461 for the discussion
# on this.
if (NOT (EXISTS "${CMAKE_SOURCE_DIR}/src/CMakeLists.txt"))
  message(FATAL_ERROR "Cannot find \"${CMAKE_SOURCE_DIR}/src/CMakeLists.txt\""
          ". This probably means you need to run"
          "``python contrib/cmake/bootstrap.py create``")
endif()

set(CMAKE_USER_MAKE_RULES_OVERRIDE_CXX "${CMAKE_CURRENT_SOURCE_DIR}/cmake/cxx_compiler_flags_overrides.cmake")
project(Z3 CXX)

################################################################################
# Project version
################################################################################
set(Z3_VERSION_MAJOR 4)
set(Z3_VERSION_MINOR 5)
set(Z3_VERSION_PATCH 1)
set(Z3_VERSION_TWEAK 0)
set(Z3_VERSION "${Z3_VERSION_MAJOR}.${Z3_VERSION_MINOR}.${Z3_VERSION_PATCH}.${Z3_VERSION_TWEAK}")
set(Z3_FULL_VERSION_STR "${Z3_VERSION}") # Note this might be modified
message(STATUS "Z3 version ${Z3_VERSION}")

################################################################################
# Set various useful variables depending on CMake version
################################################################################
if (("${CMAKE_VERSION}" VERSION_EQUAL "3.2") OR ("${CMAKE_VERSION}" VERSION_GREATER "3.2"))
  # In CMake >= 3.2 add_custom_command() and add_custom_target()
  # supports a ``USES_TERMINAL`` argument
  set(ADD_CUSTOM_COMMAND_USES_TERMINAL_ARG "USES_TERMINAL")
  set(ADD_CUSTOM_TARGET_USES_TERMINAL_ARG "USES_TERMINAL")
else()
  set(ADD_CUSTOM_COMMAND_USES_TERMINAL_ARG "")
  set(ADD_CUSTOM_TARGET_USES_TERMINAL_ARG "")
endif()

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
if ("${CMAKE_SOURCE_DIR}" STREQUAL "${CMAKE_BINARY_DIR}")
  message(FATAL_ERROR "In source builds are not allowed. You should invoke "
          "CMake from a different directory.")
endif()

################################################################################
# Add our CMake module directory to the list of module search directories
################################################################################
list(APPEND CMAKE_MODULE_PATH "${CMAKE_SOURCE_DIR}/cmake/modules")

################################################################################
# Handle git hash and description
################################################################################
include(${CMAKE_SOURCE_DIR}/cmake/git_utils.cmake)
macro(disable_git_describe)
  message(WARNING "Disabling INCLUDE_GIT_DESCRIBE")
  set(INCLUDE_GIT_DESCRIBE OFF CACHE BOOL "Include git describe output in version output" FORCE)
endmacro()
macro(disable_git_hash)
  message(WARNING "Disabling INCLUDE_GIT_HASH")
  set(INCLUDE_GIT_HASH OFF CACHE BOOL "Include git hash in version output" FORCE)
  unset(Z3GITHASH) # Used in configure_file()
endmacro()
option(INCLUDE_GIT_HASH "Include git hash in version output" ON)
option(INCLUDE_GIT_DESCRIBE "Include git describe output in version output" ON)

set(GIT_DIR "${CMAKE_SOURCE_DIR}/.git")
if (EXISTS "${GIT_DIR}")
  # Try to make CMake configure depend on the current git HEAD so that
  # a re-configure is triggered when the HEAD changes.
  add_git_dir_dependency("${GIT_DIR}" ADD_GIT_DEP_SUCCESS)
  if (ADD_GIT_DEP_SUCCESS)
    if (INCLUDE_GIT_HASH)
      get_git_head_hash("${GIT_DIR}" Z3GITHASH)
      if (NOT Z3GITHASH)
        message(WARNING "Failed to get Git hash")
        disable_git_hash()
      endif()
      message(STATUS "Using Git hash in version output: ${Z3GITHASH}")
      # This mimics the behaviour of the old build system.
      string(APPEND Z3_FULL_VERSION_STR " ${Z3GITHASH}")
    else()
      message(STATUS "Not using Git hash in version output")
      unset(Z3GITHASH) # Used in configure_file()
    endif()
    if (INCLUDE_GIT_DESCRIBE)
      get_git_head_describe("${GIT_DIR}" Z3_GIT_DESCRIPTION)
      if (NOT Z3_GIT_DESCRIPTION)
        message(WARNING "Failed to get Git description")
        disable_git_describe()
      endif()
      message(STATUS "Using Git description in version output: ${Z3_GIT_DESCRIPTION}")
      # This mimics the behaviour of the old build system.
      string(APPEND Z3_FULL_VERSION_STR " ${Z3_GIT_DESCRIPTION}")
    else()
      message(STATUS "Not including git descrption in version")
    endif()
  else()
    message(WARNING "Failed to add git dependency.")
    disable_git_describe()
    disable_git_hash()
  endif()
else()
  message(STATUS "Failed to find git directory.")
  disable_git_describe()
  disable_git_hash()
endif()

################################################################################
# Useful CMake functions/Macros
################################################################################
include(CheckCXXSourceCompiles)

################################################################################
# Compiler flags for Z3 components.
# Subsequent commands will append to this
################################################################################
set(Z3_COMPONENT_CXX_DEFINES "")
set(Z3_COMPONENT_CXX_FLAGS "")
set(Z3_COMPONENT_EXTRA_INCLUDE_DIRS "")
set(Z3_DEPENDENT_LIBS "")
set(Z3_DEPENDENT_EXTRA_CXX_LINK_FLAGS "")

################################################################################
# Build type
################################################################################
message(STATUS "CMake generator: ${CMAKE_GENERATOR}")
set(available_build_types Debug Release RelWithDebInfo MinSizeRel)
if (DEFINED CMAKE_CONFIGURATION_TYPES)
  # Multi-configuration build (e.g. Visual Studio and Xcode). Here
  # CMAKE_BUILD_TYPE doesn't matter
  message(STATUS "Available configurations: ${CMAKE_CONFIGURATION_TYPES}")
else()
  # Single configuration generator (e.g. Unix Makefiles, Ninja)
  if(NOT CMAKE_BUILD_TYPE)
    message(STATUS "CMAKE_BUILD_TYPE is not set. Setting default")
    message(STATUS "The available build types are: ${available_build_types}")
    set(CMAKE_BUILD_TYPE RelWithDebInfo CACHE String
        "Options are ${available_build_types}"
        FORCE)
    # Provide drop down menu options in cmake-gui
    set_property(CACHE CMAKE_BUILD_TYPE PROPERTY STRINGS ${available_build_types})
  endif()
  message(STATUS "Build type: ${CMAKE_BUILD_TYPE}")

  # Check the selected build type is valid
  list(FIND available_build_types "${CMAKE_BUILD_TYPE}" _build_type_index)
  if ("${_build_type_index}" EQUAL "-1")
    message(FATAL_ERROR "\"${CMAKE_BUILD_TYPE}\" is an invalid build type.\n"
      "Use one of the following build types ${available_build_types}")
  endif()
endif()

# CMAKE_BUILD_TYPE has no meaning for multi-configuration generators
# (e.g. Visual Studio) so use generator expressions instead to add
# the right definitions when doing a particular build type.
#
# Note for some reason we have to leave off ``-D`` here otherwise
# we get ``-D-DZ3DEBUG`` passed to the compiler
list(APPEND Z3_COMPONENT_CXX_DEFINES $<$<CONFIG:Debug>:Z3DEBUG>)
list(APPEND Z3_COMPONENT_CXX_DEFINES $<$<CONFIG:Debug>:LEAN_DEBUG>)
list(APPEND Z3_COMPONENT_CXX_DEFINES $<$<CONFIG:Release>:_EXTERNAL_RELEASE>)
list(APPEND Z3_COMPONENT_CXX_DEFINES $<$<CONFIG:RelWithDebInfo>:_EXTERNAL_RELEASE>)

################################################################################
# Find Python
################################################################################
find_package(PythonInterp REQUIRED)
message(STATUS "PYTHON_EXECUTABLE: ${PYTHON_EXECUTABLE}")

################################################################################
# Target architecture detection
################################################################################
include(${CMAKE_SOURCE_DIR}/cmake/target_arch_detect.cmake)
detect_target_architecture(TARGET_ARCHITECTURE)
message(STATUS "Detected target architecture: ${TARGET_ARCHITECTURE}")
if ("${TARGET_ARCHITECTURE}" STREQUAL "x86_64")
  list(APPEND Z3_COMPONENT_CXX_DEFINES "-D_AMD64_")
endif()


################################################################################
# Function for detecting C++ compiler flag support
################################################################################
include(${CMAKE_SOURCE_DIR}/cmake/z3_add_cxx_flag.cmake)

################################################################################
# C++ language version
################################################################################
# FIXME: Use CMake's own mechanism for selecting language version
if (("${CMAKE_CXX_COMPILER_ID}" MATCHES "GNU") OR ("${CMAKE_CXX_COMPILER_ID}" MATCHES "Clang"))
  z3_add_cxx_flag("-std=c++11" REQUIRED)
else()
  message(AUTHOR_WARNING "Not setting C++ language version for compiler")
endif()

################################################################################
# Platform detection
################################################################################
if ("${CMAKE_SYSTEM_NAME}" STREQUAL "Linux")
  message(STATUS "Platform: Linux")
  list(APPEND Z3_COMPONENT_CXX_DEFINES "-D_LINUX_")
  if ("${TARGET_ARCHITECTURE}" STREQUAL "x86_64")
    list(APPEND Z3_COMPONENT_CXX_DEFINES "-D_USE_THREAD_LOCAL")
  endif()
  z3_add_cxx_flag("-fno-strict-aliasing" REQUIRED)
elseif ("${CMAKE_SYSTEM_NAME}" STREQUAL "Darwin")
  # Does OSX really not need any special flags?
  message(STATUS "Platform: Darwin")
elseif ("${CMAKE_SYSTEM_NAME}" MATCHES "FreeBSD")
  message(STATUS "Platform: FreeBSD")
  list(APPEND Z3_COMPONENT_CXX_DEFINES "-D_FREEBSD_")
  z3_add_cxx_flag("-fno-strict-aliasing" REQUIRED)
elseif ("${CMAKE_SYSTEM_NAME}" MATCHES "OpenBSD")
  message(STATUS "Platform: OpenBSD")
  list(APPEND Z3_COMPONENT_CXX_DEFINES "-D_OPENBSD_")
  z3_add_cxx_flag("-fno-strict-aliasing" REQUIRED)
elseif (CYGWIN)
  message(STATUS "Platform: Cygwin")
  list(APPEND Z3_COMPONENT_CXX_DEFINES "-D_CYGWIN")
  z3_add_cxx_flag("-fno-strict-aliasing" REQUIRED)
elseif (WIN32)
  message(STATUS "Platform: Windows")
  list(APPEND Z3_COMPONENT_CXX_DEFINES "-D_WINDOWS")
else()
  message(FATAL_ERROR "Platform \"${CMAKE_SYSTEM_NAME}\" not recognised")
endif()

list(APPEND Z3_COMPONENT_EXTRA_INCLUDE_DIRS "${CMAKE_SOURCE_DIR}/src")

################################################################################
# GNU multiple precision library support
################################################################################
option(USE_LIB_GMP "Use GNU Multiple Precision Library" OFF)
if (USE_LIB_GMP)
  # Because this is off by default we will make the configure fail if libgmp
  # can't be found
  find_package(GMP REQUIRED)
  message(STATUS "Using libgmp")
  list(APPEND Z3_DEPENDENT_LIBS ${GMP_C_LIBRARIES})
  list(APPEND Z3_COMPONENT_EXTRA_INCLUDE_DIRS ${GMP_INCLUDE_DIRS})
  list(APPEND Z3_COMPONENT_CXX_DEFINES "-D_MP_GMP")
else()
  list(APPEND Z3_COMPONENT_CXX_DEFINES "-D_MP_INTERNAL")
  message(STATUS "Not using libgmp")
endif()

################################################################################
# OpenMP support
################################################################################
option(USE_OPENMP "Use OpenMP" ON)
set(OPENMP_FOUND FALSE)
if (USE_OPENMP)
  # Because this is on by default we make the configure succeed with a warning
  # if OpenMP support is not detected.
  find_package(OpenMP)
  if (NOT OPENMP_FOUND)
    message(WARNING "OpenMP support was requested but your compiler doesn't support it")
  endif()
endif()

if (OPENMP_FOUND)
    list(APPEND Z3_COMPONENT_CXX_FLAGS ${OpenMP_CXX_FLAGS})
    # GCC and Clang need to have additional flags passed to the linker.
    # We can't do ``target_link_libraries(libz3 INTERFACE ${OpenMP_CXX_FLAGS})``
    # because ``/openmp`` is interpreted as file name rather than a linker
    # flag by MSVC and breaks the build
    if (("${CMAKE_CXX_COMPILER_ID}" MATCHES "Clang") OR
        ("${CMAKE_CXX_COMPILER_ID}" MATCHES "GNU"))
      list(APPEND Z3_DEPENDENT_EXTRA_CXX_LINK_FLAGS ${OpenMP_CXX_FLAGS})
    endif()
    unset(CMAKE_REQUIRED_FLAGS)
    message(STATUS "Using OpenMP")
else()
  list(APPEND Z3_COMPONENT_CXX_DEFINES "-D_NO_OMP_")
  message(STATUS "Not using OpenMP")
  set(USE_OPENMP OFF CACHE BOOL "Use OpenMP" FORCE)
endif()

################################################################################
# API Log sync
################################################################################
option(API_LOG_SYNC
  "Use locking when logging Z3 API calls (experimental)"
  OFF
)
if (API_LOG_SYNC)
  if (NOT USE_OPENMP)
    message(FATAL_ERROR "API_LOG_SYNC feature requires OpenMP")
  endif()
  list(APPEND Z3_COMPONENT_CXX_DEFINES "-DZ3_LOG_SYNC")
  message(STATUS "Using API_LOG_SYNC")
else()
  message(STATUS "Not using API_LOG_SYNC")
endif()

################################################################################
# FP math
################################################################################
# FIXME: Support ARM "-mfpu=vfp -mfloat-abi=hard"
if (("${TARGET_ARCHITECTURE}" STREQUAL "x86_64") OR ("${TARGET_ARCHITECTURE}" STREQUAL "i686"))
  if (("${CMAKE_CXX_COMPILER_ID}" MATCHES "GNU") OR ("${CMAKE_CXX_COMPILER_ID}" MATCHES "Clang"))
    set(SSE_FLAGS "-mfpmath=sse" "-msse" "-msse2")
    # FIXME: Remove "x.." when CMP0054 is set to NEW
  elseif ("x${CMAKE_CXX_COMPILER_ID}" STREQUAL "xMSVC")
    set(SSE_FLAGS "/arch:SSE2")
  else()
    message(FATAL_ERROR "Unknown compiler ${CMAKE_CXX_COMPILER_ID}")
  endif()
  CHECK_CXX_COMPILER_FLAG("${SSE_FLAGS}" HAS_SSE2)
  if (HAS_SSE2)
    list(APPEND Z3_COMPONENT_CXX_FLAGS ${SSE_FLAGS})
  endif()
  unset(SSE_FLAGS)
endif()



# FIXME: Remove "x.." when CMP0054 is set to NEW
if ("x${CMAKE_CXX_COMPILER_ID}" STREQUAL "xMSVC")
  # This is the default for MSVC already but to replicate the
  # python/Makefile build system behaviour this flag is set
  # explicitly.
  z3_add_cxx_flag("/fp:precise" REQUIRED)
endif()
# There doesn't seem to be an equivalent for clang/gcc

################################################################################
# Threading support
################################################################################
find_package(Threads)
list(APPEND Z3_DEPENDENT_LIBS ${CMAKE_THREAD_LIBS_INIT})

################################################################################
# Compiler warnings
################################################################################
include(${CMAKE_SOURCE_DIR}/cmake/compiler_warnings.cmake)

################################################################################
# Option to control what type of library we build
################################################################################
option(BUILD_LIBZ3_SHARED "Build libz3 as a shared library if true, otherwise build a static library" ON)


################################################################################
# Symbol visibility
################################################################################
if (NOT MSVC)
  z3_add_cxx_flag("-fvisibility=hidden" REQUIRED)
endif()

################################################################################
# Tracing
################################################################################
option(ENABLE_TRACING_FOR_NON_DEBUG "Enable tracing in non-debug builds." OFF)
if (ENABLE_TRACING_FOR_NON_DEBUG)
  list(APPEND Z3_COMPONENT_CXX_DEFINES "-D_TRACE")
else()
  # Tracing is always enabled in debug builds
  list(APPEND Z3_COMPONENT_CXX_DEFINES $<$<CONFIG:Debug>:_TRACE>)
endif()

################################################################################
# Postion independent code
################################################################################
# This is required because code built in the components will end up in a shared
# library. If not building a shared library ``-fPIC`` isn't needed and would add
# unnecessary overhead.
if (BUILD_LIBZ3_SHARED)
  # Avoid adding -fPIC compiler switch if we compile with MSVC (which does not
  # support the flag) or if we target Windows, which generally does not use
  # position independent code for native code shared libraries (DLLs).
  if (NOT (MSVC OR MINGW OR WIN32))
    z3_add_cxx_flag("-fPIC" REQUIRED)
  endif()
endif()

################################################################################
# Link time optimization
################################################################################
include(${CMAKE_SOURCE_DIR}/cmake/compiler_lto.cmake)

################################################################################
# MSVC specific flags inherited from old build system
################################################################################
# FIXME: Remove "x.." when CMP0054 is set to NEW
if ("x${CMAKE_CXX_COMPILER_ID}" STREQUAL "xMSVC")
  include(${CMAKE_SOURCE_DIR}/cmake/msvc_legacy_quirks.cmake)
endif()

################################################################################
# Report default CMake flags
################################################################################
# This is mainly for debugging.
message(STATUS "CMAKE_CXX_FLAGS: \"${CMAKE_CXX_FLAGS}\"")
message(STATUS "CMAKE_EXE_LINKER_FLAGS: \"${CMAKE_EXE_LINKER_FLAGS}\"")
message(STATUS "CMAKE_STATIC_LINKER_FLAGS: \"${CMAKE_STATIC_LINKER_FLAGS}\"")
message(STATUS "CMAKE_SHARED_LINKER_FLAGS: \"${CMAKE_SHARED_LINKER_FLAGS}\"")
if (DEFINED CMAKE_CONFIGURATION_TYPES)
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
# Report Z3_COMPONENT flags
################################################################################
message(STATUS "Z3_COMPONENT_CXX_DEFINES: ${Z3_COMPONENT_CXX_DEFINES}")
message(STATUS "Z3_COMPONENT_CXX_FLAGS: ${Z3_COMPONENT_CXX_FLAGS}")
message(STATUS "Z3_DEPENDENT_LIBS: ${Z3_DEPENDENT_LIBS}")
message(STATUS "Z3_COMPONENT_EXTRA_INCLUDE_DIRS: ${Z3_COMPONENT_EXTRA_INCLUDE_DIRS}")
message(STATUS "Z3_DEPENDENT_EXTRA_CXX_LINK_FLAGS: ${Z3_DEPENDENT_EXTRA_CXX_LINK_FLAGS}")

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

################################################################################
# Uninstall rule
################################################################################
configure_file(
  "${CMAKE_SOURCE_DIR}/cmake/cmake_uninstall.cmake.in"
  "${CMAKE_CURRENT_BINARY_DIR}/cmake_uninstall.cmake"
  @ONLY
)

# Target needs to be declared before the components so that they can add
# dependencies to this target so they can run their own custom uninstall rules.
add_custom_target(uninstall
  COMMAND
  "${CMAKE_COMMAND}" -P "${CMAKE_CURRENT_BINARY_DIR}/cmake_uninstall.cmake"
  COMMENT "Uninstalling..."
  ${ADD_CUSTOM_COMMAND_USES_TERMINAL_ARG}
  VERBATIM
)

################################################################################
# CMake build file locations
################################################################################
# To mimic the python build system output these into the root of the build
# directory
set(CMAKE_LIBRARY_OUTPUT_DIRECTORY "${CMAKE_BINARY_DIR}")
set(CMAKE_ARCHIVE_OUTPUT_DIRECTORY "${CMAKE_BINARY_DIR}")
set(CMAKE_RUNTIME_OUTPUT_DIRECTORY "${CMAKE_BINARY_DIR}")

################################################################################
# Extra dependencies for build rules that use the Python infrastructure to
# generate files used for Z3's build. Changes to these files will trigger
# a rebuild of all the generated files.
################################################################################
# Note: ``update_api.py`` is deliberately not here because it not used
# to generate every generated file. The targets that need it list it explicitly.
set(Z3_GENERATED_FILE_EXTRA_DEPENDENCIES
  "${CMAKE_SOURCE_DIR}/scripts/mk_genfile_common.py"
)

################################################################################
# Z3 components, library and executables
################################################################################
include(${CMAKE_SOURCE_DIR}/cmake/z3_add_component.cmake)
include(${CMAKE_SOURCE_DIR}/cmake/z3_append_linker_flag_list_to_target.cmake)
add_subdirectory(src)

################################################################################
# Create `Z3Config.cmake` and related files for the build tree so clients can
# use Z3 via CMake.
################################################################################
include(CMakePackageConfigHelpers)
export(EXPORT Z3_EXPORTED_TARGETS
  NAMESPACE z3::
  FILE "${CMAKE_BINARY_DIR}/Z3Targets.cmake"
)
set(Z3_FIRST_PACKAGE_INCLUDE_DIR "${CMAKE_BINARY_DIR}/src/api")
set(Z3_SECOND_PACKAGE_INCLUDE_DIR "${CMAKE_SOURCE_DIR}/src/api")
set(Z3_CXX_PACKAGE_INCLUDE_DIR "${CMAKE_SOURCE_DIR}/src/api/c++")
set(AUTO_GEN_MSG "Automatically generated. DO NOT EDIT")
set(CONFIG_FILE_TYPE "build tree")
configure_package_config_file("${CMAKE_SOURCE_DIR}/cmake/Z3Config.cmake.in"
  "Z3Config.cmake"
  INSTALL_DESTINATION "${CMAKE_BINARY_DIR}"
  PATH_VARS
    Z3_FIRST_PACKAGE_INCLUDE_DIR
    Z3_SECOND_PACKAGE_INCLUDE_DIR
    Z3_CXX_PACKAGE_INCLUDE_DIR
  INSTALL_PREFIX "${CMAKE_BINARY_DIR}"
)
unset(Z3_FIRST_PACKAGE_INCLUDE_DIR)
unset(Z3_SECOND_PACKAGE_INCLUDE_DIR)
unset(Z3_CXX_PACKAGE_INCLUDE_DIR)
unset(AUTO_GEN_MSG)
unset(CONFIG_FILE_TYPE)
# TODO: Provide a `Z3Version.cmake` file so that clients can specify the version
# of Z3 they want.

################################################################################
# Create `Z3Config.cmake` and related files for install tree so clients can use
# Z3 via CMake.
################################################################################
install(EXPORT
  Z3_EXPORTED_TARGETS
  FILE "Z3Targets.cmake"
  NAMESPACE z3::
  DESTINATION "${CMAKE_INSTALL_Z3_CMAKE_PACKAGE_DIR}"
)
set(Z3_INSTALL_TREE_CMAKE_CONFIG_FILE "${CMAKE_BINARY_DIR}/cmake/Z3Config.cmake")
set(Z3_FIRST_PACKAGE_INCLUDE_DIR "${CMAKE_INSTALL_INCLUDEDIR}")
set(Z3_SECOND_INCLUDE_DIR "")
set(Z3_CXX_PACKAGE_INCLUDE_DIR "")
set(AUTO_GEN_MSG "Automatically generated. DO NOT EDIT")
set(CONFIG_FILE_TYPE "install tree")
# We use `configure_package_config_file()` to try and create CMake files
# that are re-locatable so that it doesn't matter if the files aren't placed
# in the original install prefix.
configure_package_config_file("${CMAKE_SOURCE_DIR}/cmake/Z3Config.cmake.in"
  "${Z3_INSTALL_TREE_CMAKE_CONFIG_FILE}"
  INSTALL_DESTINATION "${CMAKE_INSTALL_Z3_CMAKE_PACKAGE_DIR}"
  PATH_VARS Z3_FIRST_PACKAGE_INCLUDE_DIR
)
unset(Z3_FIRST_PACKAGE_INCLUDE_DIR)
unset(Z3_SECOND_PACKAGE_INCLUDE_DIR)
unset(Z3_CXX_PACKAGE_INCLUDE_DIR)
unset(AUTO_GEN_MSG)
unset(CONFIG_FILE_TYPE)

# Add install rule to install ${Z3_INSTALL_TREE_CMAKE_CONFIG_FILE}
install(
  FILES "${Z3_INSTALL_TREE_CMAKE_CONFIG_FILE}"
  DESTINATION "${CMAKE_INSTALL_Z3_CMAKE_PACKAGE_DIR}"
)

# TODO: Provide a `Z3Version.cmake` file so that clients can specify the version
# of Z3 they want.

################################################################################
# Examples
################################################################################
option(ENABLE_EXAMPLE_TARGETS "Build Z3 api examples" ON)
if (ENABLE_EXAMPLE_TARGETS)
  add_subdirectory(examples)
endif()

################################################################################
# Documentation
################################################################################
option(BUILD_DOCUMENTATION "Build API documentation" OFF)
if (BUILD_DOCUMENTATION)
  message(STATUS "Building documentation enabled")
  add_subdirectory(doc)
else()
  message(STATUS "Building documentation disabled")
endif()
