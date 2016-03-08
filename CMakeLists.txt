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

# This overrides the default flags for the different CMAKE_BUILD_TYPEs
set(CMAKE_USER_MAKE_RULES_OVERRIDE "${CMAKE_CURRENT_SOURCE_DIR}/cmake/compiler_flags_override.cmake")
project(Z3 C CXX)

################################################################################
# Project version
################################################################################
set(Z3_VERSION_MAJOR 4)
set(Z3_VERSION_MINOR 4)
set(Z3_VERSION_PATCH 2)
set(Z3_VERSION_TWEAK 0)
set(Z3_VERSION "${Z3_VERSION_MAJOR}.${Z3_VERSION_MINOR}.${Z3_VERSION_PATCH}.${Z3_VERSION_TWEAK}")
message(STATUS "Z3 version ${Z3_VERSION}")

################################################################################
# Set various useful variables depending on CMake version
################################################################################
if (("${CMAKE_VERSION}" VERSION_EQUAL "3.2") OR ("${CMAKE_VERSION}" VERSION_GREATER "3.2"))
  # In CMake >= 3.2 add_custom_command() supports a ``USES_TERMINAL`` argument
  set(ADD_CUSTOM_COMMAND_USES_TERMINAL_ARG "USES_TERMINAL")
else()
  set(ADD_CUSTOM_COMMAND_USES_TERMINAL_ARG "")
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
set(Z3_DEPENDENT_EXTRA_C_LINK_FLAGS "")

################################################################################
# Build type
################################################################################
message(STATUS "CMake generator: ${CMAKE_GENERATOR}")
if (DEFINED CMAKE_CONFIGURATION_TYPES)
  # Multi-configuration build (e.g. Visual Studio and Xcode). Here
  # CMAKE_BUILD_TYPE doesn't matter
  message(STATUS "Available configurations: ${CMAKE_CONFIGURATION_TYPES}")
else()
  # Single configuration generator (e.g. Unix Makefiles, Ninja)
  set(available_build_types Debug Release RelWithDebInfo MinSizeRel)
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
endif()

# CMAKE_BUILD_TYPE has no meaning for multi-configuration generators
# (e.g. Visual Studio) so use generator expressions instead to add
# the right definitions when doing a particular build type.
#
# Note for some reason we have to leave off ``-D`` here otherwise
# we get ``-D-DZ3DEBUG`` passed to the compiler
list(APPEND Z3_COMPONENT_CXX_DEFINES $<$<CONFIG:Debug>:Z3DEBUG>)
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
# FOCI2 support
################################################################################
# FIXME: What is this?
option(USE_FOCI2 "Use FOCI2" OFF)
if (USE_FOCI2)
  message(FATAL_ERROR "TODO")
  message(STATUS "Using FOCI2")
else()
  message(STATUS "Not using FOCI2")
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
      list(APPEND Z3_DEPENDENT_EXTRA_CXX_LINK_FLAGS ${OpenMP_C_FLAGS})
    endif()
    if (("${CMAKE_C_COMPILER_ID}" MATCHES "Clang") OR
        ("${CMAKE_C_COMPILER_ID}" MATCHES "GNU"))
      list(APPEND Z3_DEPENDENT_EXTRA_C_LINK_FLAGS ${OpenMP_CXX_FLAGS})
    endif()
    unset(CMAKE_REQUIRED_FLAGS)
    message(STATUS "Using OpenMP")
else()
  list(APPEND Z3_COMPONENT_CXX_DEFINES "-D_NO_OMP_")
  message(STATUS "Not using OpenMP")
endif()

################################################################################
# FP math
################################################################################
# FIXME: Support ARM "-mfpu=vfp -mfloat-abi=hard"
if ("${TARGET_ARCHITECTURE}" STREQUAL "x86_64")
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
option(ENABLE_TRACING OFF "Enable tracing")
if (ENABLE_TRACING)
  list(APPEND Z3_COMPONENT_CXX_DEFINES "-D_TRACE")
endif()
# Should we always enable tracing when doing a debug build?
#list(APPEND Z3_COMPONENT_CXX_DEFINES $<$<CONFIG:Debug>:_TRACE>)

################################################################################
# Postion indepdent code
################################################################################
# This is required because code built in the components will end up in a shared
# library. If not building a shared library ``-fPIC`` isn't needed and would add
# unnecessary overhead.
if (BUILD_LIBZ3_SHARED)
  if (NOT MSVC)
    z3_add_cxx_flag("-fPIC" REQUIRED)
  endif()
endif()

################################################################################
# Report Z3_COMPONENT flags
################################################################################
message(STATUS "Z3_COMPONENT_CXX_DEFINES: ${Z3_COMPONENT_CXX_DEFINES}")
message(STATUS "Z3_COMPONENT_CXX_FLAGS: ${Z3_COMPONENT_CXX_FLAGS}")
message(STATUS "Z3_DEPENDENT_LIBS: ${Z3_DEPENDENT_LIBS}")
message(STATUS "Z3_COMPONENT_EXTRA_INCLUDE_DIRS: ${Z3_COMPONENT_EXTRA_INCLUDE_DIRS}")
message(STATUS "Z3_DEPENDENT_EXTRA_CXX_LINK_FLAGS: ${Z3_DEPENDENT_EXTRA_CXX_LINK_FLAGS}")
message(STATUS "Z3_DEPENDENT_EXTRA_C_LINK_FLAGS: ${Z3_DEPENDENT_EXTRA_C_LINK_FLAGS}")

################################################################################
# Z3 installation locations
################################################################################
set (Z3_INSTALL_LIB_DIR "lib")
set (Z3_INSTALL_BIN_DIR "bin")
set (Z3_INSTALL_INCLUDE_DIR "include")

################################################################################
# CMake build file locations
################################################################################
# To mimic the python build system output these into the root of the build
# directory
set(CMAKE_LIBRARY_OUTPUT_DIRECTORY "${CMAKE_BINARY_DIR}")
set(CMAKE_ARCHIVE_OUTPUT_DIRECTORY "${CMAKE_BINARY_DIR}")
set(CMAKE_RUNTIME_OUTPUT_DIRECTORY "${CMAKE_BINARY_DIR}")

################################################################################
# Z3 components, library and executables
################################################################################
include(${CMAKE_SOURCE_DIR}/cmake/z3_add_component.cmake)
include(${CMAKE_SOURCE_DIR}/cmake/z3_append_linker_flag_list_to_target.cmake)
add_subdirectory(src)

################################################################################
# Examples
################################################################################
option(ENABLE_EXAMPLE_TARGETS "Build Z3 api examples" ON)
if (ENABLE_EXAMPLE_TARGETS)
  add_subdirectory(examples)
endif()

################################################################################
# Uninstall rule
################################################################################
configure_file(
  "${CMAKE_SOURCE_DIR}/cmake/cmake_uninstall.cmake.in"
  "${CMAKE_CURRENT_BINARY_DIR}/cmake_uninstall.cmake"
  @ONLY
)

add_custom_target(uninstall
  COMMAND
  "${CMAKE_COMMAND}" -P "${CMAKE_CURRENT_BINARY_DIR}/cmake_uninstall.cmake"
  COMMENT "Uninstalling..."
  ${ADD_CUSTOM_COMMAND_USES_TERMINAL_ARG}
  VERBATIM
)
