# Enforce some CMake policies
cmake_minimum_required(VERSION 3.16)

set(CMAKE_USER_MAKE_RULES_OVERRIDE_CXX "${CMAKE_CURRENT_SOURCE_DIR}/cmake/cxx_compiler_flags_overrides.cmake")

# Read version from VERSION.txt file
file(READ "${CMAKE_CURRENT_SOURCE_DIR}/scripts/VERSION.txt" Z3_VERSION_FROM_FILE)
string(STRIP "${Z3_VERSION_FROM_FILE}" Z3_VERSION_FROM_FILE)

project(Z3 VERSION ${Z3_VERSION_FROM_FILE} LANGUAGES CXX)

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
macro(disable_git_describe)
  if(Z3_INCLUDE_GIT_DESCRIBE)
    message(WARNING "Disabling Z3_INCLUDE_GIT_DESCRIBE")
    set(Z3_INCLUDE_GIT_DESCRIBE OFF CACHE BOOL "Include git describe output in version output" FORCE)
  endif()
endmacro()
macro(disable_git_hash)
  if(Z3_INCLUDE_GIT_HASH)
    message(WARNING "Disabling Z3_INCLUDE_GIT_HASH")
    set(Z3_INCLUDE_GIT_HASH OFF CACHE BOOL "Include git hash in version output" FORCE)
  endif()
endmacro()
option(Z3_INCLUDE_GIT_HASH "Include git hash in version output" ON)
option(Z3_INCLUDE_GIT_DESCRIBE "Include git describe output in version output" ON)

set(GIT_DIR "${PROJECT_SOURCE_DIR}/.git")
if ((Z3_INCLUDE_GIT_HASH OR Z3_INCLUDE_GIT_HASH) AND EXISTS "${GIT_DIR}")
  # Try to make CMake configure depend on the current git HEAD so that
  # a re-configure is triggered when the HEAD changes.
  add_git_dir_dependency("${GIT_DIR}" ADD_GIT_DEP_SUCCESS)
  if (ADD_GIT_DEP_SUCCESS)
    if (Z3_INCLUDE_GIT_HASH)
      get_git_head_hash("${GIT_DIR}" Z3GITHASH)
      if (NOT Z3GITHASH)
        message(WARNING "Failed to get Git hash")
        disable_git_hash()
      else()
        message(STATUS "Using Git hash in version output: ${Z3GITHASH}")
        # This mimics the behaviour of the old build system.
        set(Z3_FULL_VERSION_STR "${Z3_FULL_VERSION_STR} ${Z3GITHASH}")
      endif()
    else()
      message(STATUS "Not using Git hash in version output")
    endif()
    if (Z3_INCLUDE_GIT_DESCRIBE)
      get_git_head_describe("${GIT_DIR}" Z3_GIT_DESCRIPTION)
      if (NOT Z3_GIT_DESCRIPTION)
        message(WARNING "Failed to get Git description")
        disable_git_describe()
      endif()
      message(STATUS "Using Git description in version output: ${Z3_GIT_DESCRIPTION}")
      # This mimics the behaviour of the old build system.
      set(Z3_FULL_VERSION_STR "${Z3_FULL_VERSION_STR} ${Z3_GIT_DESCRIPTION}")
    else()
      message(STATUS "Not including git description in version")
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
if(NOT Z3_INCLUDE_GIT_HASH)
  unset(Z3GITHASH) # Used in configure_file()
endif()

################################################################################
# Useful CMake functions/Macros
################################################################################
include(CheckCXXSourceCompiles)
include(CMakeDependentOption)

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
    set(CMAKE_BUILD_TYPE RelWithDebInfo CACHE STRING
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
list(APPEND Z3_COMPONENT_CXX_DEFINES $<$<CONFIG:Release>:_EXTERNAL_RELEASE>)
list(APPEND Z3_COMPONENT_CXX_DEFINES $<$<CONFIG:RelWithDebInfo>:_EXTERNAL_RELEASE>)

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

################################################################################
# C++ language version
################################################################################
set(CMAKE_CXX_STANDARD 20)
set(CMAKE_CXX_STANDARD_REQUIRED ON)

################################################################################
# Platform detection
################################################################################
if (CMAKE_SYSTEM_NAME STREQUAL "Darwin")
  if (TARGET_ARCHITECTURE STREQUAL "arm64")
    set(CMAKE_OSX_ARCHITECTURES "arm64")
  endif()
elseif (WIN32)
  message(STATUS "Platform: Windows")
  list(APPEND Z3_COMPONENT_CXX_DEFINES "-D_WINDOWS")
  # workaround for #7420
  list(APPEND Z3_COMPONENT_CXX_DEFINES "-D_DISABLE_CONSTEXPR_MUTEX_CONSTRUCTOR")  
elseif (EMSCRIPTEN)
  message(STATUS "Platform: Emscripten")
  list(APPEND Z3_DEPENDENT_EXTRA_CXX_LINK_FLAGS
    "-Os"
    "-s ALLOW_MEMORY_GROWTH=1"
    "-s ASSERTIONS=0"
    "-s DISABLE_EXCEPTION_CATCHING=0"
    "-s ERROR_ON_UNDEFINED_SYMBOLS=1"
  )
endif()

list(APPEND Z3_COMPONENT_EXTRA_INCLUDE_DIRS
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
  list(APPEND Z3_DEPENDENT_LIBS GMP::GMP)
  list(APPEND Z3_COMPONENT_CXX_DEFINES "-D_MP_GMP")
else()
  list(APPEND Z3_COMPONENT_CXX_DEFINES "-D_MP_INTERNAL")
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
  list(APPEND Z3_COMPONENT_CXX_DEFINES "-DZ3_LOG_SYNC")
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
  list(APPEND Z3_COMPONENT_CXX_DEFINES "-DSINGLE_THREAD")
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
  list(APPEND Z3_COMPONENT_CXX_DEFINES "-DPOLLING_TIMER")
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
    list(APPEND Z3_COMPONENT_CXX_FLAGS ${SSE_FLAGS})
  endif()
  unset(SSE_FLAGS)
endif()

################################################################################
# Threading support
################################################################################
set(THREADS_PREFER_PTHREAD_FLAG TRUE)
find_package(Threads)
list(APPEND Z3_DEPENDENT_LIBS Threads::Threads)

################################################################################
# Compiler warnings
################################################################################
include(${PROJECT_SOURCE_DIR}/cmake/compiler_warnings.cmake)


################################################################################
# Address sanitization
################################################################################
option(Z3_ADDRESS_SANITIZE "Set address sanitization." OFF)

if (Z3_ADDRESS_SANITIZE)
  z3_add_cxx_flag("-fsanitize=address" REQUIRED)
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
    set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -fcolor-diagnostics")
    set(CMAKE_C_FLAGS "${CMAKE_C_FLAGS} -fcolor-diagnostics")
  endif()
#  if (CMAKE_CXX_COMPILER_ID STREQUAL "GNU")
#    set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -fdiagnostics-color")
#    set(CMAKE_C_FLAGS "${CMAKE_C_FLAGS} -fdiagnostics-color")
#  endif()
endif()

################################################################################
# Option to control what type of library we build
################################################################################
option(Z3_BUILD_LIBZ3_SHARED "Build libz3 as a shared library if true, otherwise build a static library" ON)
option(Z3_BUILD_LIBZ3_MSVC_STATIC "Build libz3 as a statically-linked runtime library"                   OFF)


################################################################################
# Tracing
################################################################################
option(Z3_ENABLE_TRACING_FOR_NON_DEBUG "Enable tracing in non-debug builds." OFF)
if (Z3_ENABLE_TRACING_FOR_NON_DEBUG)
  list(APPEND Z3_COMPONENT_CXX_DEFINES "-D_TRACE")
else()
  # Tracing is always enabled in debug builds
  list(APPEND Z3_COMPONENT_CXX_DEFINES $<$<CONFIG:Debug>:_TRACE>)
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
  if (DEFINED CMAKE_CONFIGURATION_TYPES)
    # Multi configuration generator
    message(STATUS "Note CFI is only enabled for the following configurations: ${build_types_with_cfi}")
    # No need for else because this is the same as the set that LTO requires.
  endif()
  
  message(STATUS "Enabling Control Flow Integrity (CFI) for Clang")
  z3_add_cxx_flag("-fsanitize=cfi" REQUIRED)
  z3_add_cxx_flag("-fsanitize-cfi-cross-dso" REQUIRED)
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
    string(APPEND CMAKE_EXE_LINKER_FLAGS " /GUARD:CF /DYNAMICBASE")
    string(APPEND CMAKE_SHARED_LINKER_FLAGS " /GUARD:CF /DYNAMICBASE")
  endif()
else()
  if (CMAKE_CXX_COMPILER_ID STREQUAL "MSVC")
    # Explicitly disable Control Flow Guard when Z3_ENABLE_CFG is OFF
    message(STATUS "Disabling Control Flow Guard (/guard:cf-) for MSVC")
    z3_add_cxx_flag("/guard:cf-" REQUIRED)
    string(APPEND CMAKE_EXE_LINKER_FLAGS " /GUARD:NO")
    string(APPEND CMAKE_SHARED_LINKER_FLAGS " /GUARD:NO")
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
  string(APPEND CMAKE_EXE_LINKER_FLAGS " /RELEASE")
  string(APPEND CMAKE_SHARED_LINKER_FLAGS " /RELEASE")
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
  "${PROJECT_SOURCE_DIR}/cmake/cmake_uninstall.cmake.in"
  "${CMAKE_CURRENT_BINARY_DIR}/cmake_uninstall.cmake"
  @ONLY
)

# Target needs to be declared before the components so that they can add
# dependencies to this target so they can run their own custom uninstall rules.
add_custom_target(uninstall
  COMMAND
  "${CMAKE_COMMAND}" -P "${CMAKE_CURRENT_BINARY_DIR}/cmake_uninstall.cmake"
  COMMENT "Uninstalling..."
  USES_TERMINAL
  VERBATIM
)

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

option(Z3_BUILD_LIBZ3_CORE "Build the core libz3 library" ON)
# Only export targets if we built libz3
if (Z3_BUILD_LIBZ3_CORE)
  ################################################################################
  # Z3 components, library and executables
  ################################################################################
  include(${PROJECT_SOURCE_DIR}/cmake/z3_add_component.cmake)
  include(${PROJECT_SOURCE_DIR}/cmake/z3_append_linker_flag_list_to_target.cmake)
  add_subdirectory(src)

  export(EXPORT Z3_EXPORTED_TARGETS
     NAMESPACE z3::
     FILE "${PROJECT_BINARY_DIR}/Z3Targets.cmake"
  )
else()
  # When not building libz3, we need to find it
  message(STATUS "Not building libz3, will look for pre-installed library")
  find_library(Z3_LIBRARY NAMES z3 libz3
    HINTS ${CMAKE_INSTALL_PREFIX}/${CMAKE_INSTALL_LIBDIR}
    PATH_SUFFIXES lib lib64
  )
  if (NOT Z3_LIBRARY)
    message(FATAL_ERROR "Could not find pre-installed libz3. Please ensure libz3 is installed or set Z3_BUILD_LIBZ3_CORE=ON")
  endif()
  message(STATUS "Found libz3: ${Z3_LIBRARY}")

  # Create an imported target for the pre-installed libz3
  add_library(libz3 SHARED IMPORTED)
  set_target_properties(libz3 PROPERTIES
    IMPORTED_LOCATION "${Z3_LIBRARY}"
  )
  # Set include directories for the imported target
  target_include_directories(libz3 INTERFACE
    ${CMAKE_INSTALL_PREFIX}/${CMAKE_INSTALL_INCLUDEDIR}
  )
endif()

################################################################################
# Z3 API bindings
################################################################################
option(Z3_BUILD_PYTHON_BINDINGS "Build Python bindings for Z3" OFF)
if (Z3_BUILD_PYTHON_BINDINGS)
  # Validate configuration for Python bindings
  if (Z3_BUILD_LIBZ3_CORE)
    # Building libz3 together with Python bindings
    if (NOT Z3_BUILD_LIBZ3_SHARED)
      message(FATAL_ERROR "The python bindings will not work with a static libz3. "
              "You either need to disable Z3_BUILD_PYTHON_BINDINGS or enable Z3_BUILD_LIBZ3_SHARED")
    endif()
  else()
    # Using pre-installed libz3 for Python bindings
    message(STATUS "Building Python bindings with pre-installed libz3")
  endif()
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

configure_file("${CMAKE_CURRENT_SOURCE_DIR}/z3.pc.cmake.in"
	"${CMAKE_CURRENT_BINARY_DIR}/z3.pc" @ONLY)

################################################################################
# Create `Z3Config.cmake` and related files for install tree so clients can use
# Z3 via CMake.
################################################################################
# Only install targets if we built libz3
if (Z3_BUILD_LIBZ3_CORE)
  install(EXPORT
    Z3_EXPORTED_TARGETS
    FILE "Z3Targets.cmake"
    NAMESPACE z3::
    DESTINATION "${CMAKE_INSTALL_Z3_CMAKE_PACKAGE_DIR}"
  )
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

################################################################################
# Examples
################################################################################
cmake_dependent_option(Z3_ENABLE_EXAMPLE_TARGETS
    "Build Z3 api examples" ON
    "CMAKE_SOURCE_DIR STREQUAL PROJECT_SOURCE_DIR" OFF)
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
