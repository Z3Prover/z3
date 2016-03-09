# This file overrides the default compiler flags for CMake's built-in
# configurations (CMAKE_BUILD_TYPE). Most compiler flags should not be set here.
# The main purpose is to have very fine grained control of the compiler flags.
if (CMAKE_C_COMPILER_ID)
  set(_lang C)
elseif(CMAKE_CXX_COMPILER_ID)
  set(_lang CXX)
else()
  message(FATAL_ERROR "Unknown language")
endif()

# TODO: The value of doing this is debatable. The flags set here are pretty
# much the CMake defaults now (they didn't use to be) and makes extra work for
# us when supporting different compilers. Perhaps we should move the remaining
# code that sets non-default flags out into the CMakeLists.txt files and remove
# any overrides here?
if (("${CMAKE_${_lang}_COMPILER_ID}" MATCHES "Clang") OR ("${CMAKE_${_lang}_COMPILER_ID}" MATCHES "GNU"))
  # Taken from Modules/Compiler/GNU.cmake
  set(CMAKE_${_lang}_FLAGS_INIT "")
  set(CMAKE_${_lang}_FLAGS_DEBUG_INIT "-g -O0")
  set(CMAKE_${_lang}_FLAGS_MINSIZEREL_INIT "-Os -DNDEBUG")
  set(CMAKE_${_lang}_FLAGS_RELEASE_INIT "-O3 -DNDEBUG")
  set(CMAKE_${_lang}_FLAGS_RELWITHDEBINFO_INIT "-O2 -g -DNDEBUG")
  # FIXME: Remove "x.." when CMP0054 is set to NEW
elseif ("x${CMAKE_${_lang}_COMPILER_ID}" STREQUAL "xMSVC")
  # FIXME: Perhaps we should be using /MD instead?
  set(CMAKE_${_lang}_FLAGS_DEBUG_INIT "/MTd /Zi /Ob0 /Od /RTC1")
  set(CMAKE_${_lang}_FLAGS_MINSIZEREL_INIT     "/MT /O1 /Ob1 /D NDEBUG")
  set(CMAKE_${_lang}_FLAGS_RELEASE_INIT        "/MT /O2 /Ob2 /D NDEBUG")
  set(CMAKE_${_lang}_FLAGS_RELWITHDEBINFO_INIT "/MT /Zi /O2 /Ob1 /D NDEBUG")
  # Override linker flags (see Windows-MSVC.cmake for CMake's defaults)
  # The stack size comes from the Python build system.
  set(_msvc_stack_size "8388608")
  set(CMAKE_EXE_LINKER_FLAGS_DEBUG_INIT "/debug /INCREMENTAL:NO /STACK:${_msvc_stack_size}")
  set(CMAKE_EXE_LINKER_FLAGS_RELWITHDEBINFO_INIT "/debug /INCREMENTAL:NO /STACK:${_msvc_stack_size}")
  set(CMAKE_EXE_LINKER_FLAGS_MINSIZEREL_INIT "/INCREMENTAL:NO /STACK:${_msvc_stack_size}")
  set(CMAKE_EXE_LINKER_FLAGS_RELEASE_INIT "/INCREMENTAL:NO /STACK:${_msvc_stack_size}")
  unset(_msvc_stack_size)
else()
  message(FATAL_ERROR "Overrides not set for ${_lang} compiler \"${CMAKE_${_lang}_COMPILER_ID}\"")
endif()

unset(_lang)
