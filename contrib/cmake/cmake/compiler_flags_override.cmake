# This file overrides the default compiler flags for CMake's built-in
# configurations (CMAKE_BUILD_TYPE). Most compiler flags should not be set here.
# The main purpose is to make sure ``-DNDEBUG`` is never set by default.
if (CMAKE_C_COMPILER_ID)
  set(_lang C)
elseif(CMAKE_CXX_COMPILER_ID)
  set(_lang CXX)
else()
  message(FATAL_ERROR "Unknown language")
endif()

if (("${CMAKE_${_lang}_COMPILER_ID}" MATCHES "Clang") OR ("${CMAKE_${_lang}_COMPILER_ID}" MATCHES "GNU"))
  # Taken from Modules/Compiler/GNU.cmake but -DNDEBUG is removed
  set(CMAKE_${_lang}_FLAGS_INIT "")
  set(CMAKE_${_lang}_FLAGS_DEBUG_INIT "-g -O0")
  set(CMAKE_${_lang}_FLAGS_MINSIZEREL_INIT "-Os")
  set(CMAKE_${_lang}_FLAGS_RELEASE_INIT "-O3")
  set(CMAKE_${_lang}_FLAGS_RELWITHDEBINFO_INIT "-O2 -g")
  # FIXME: Remove "x.." when CMP0054 is set to NEW
elseif ("x${CMAKE_${_lang}_COMPILER_ID}" STREQUAL "xMSVC")
  set(CMAKE_${_lang}_FLAGS_DEBUG_INIT "/MTd /Zi /Ob0 /Od /RTC1")
  set(CMAKE_${_lang}_FLAGS_MINSIZEREL_INIT     "/MT /O1 /Ob1")
  set(CMAKE_${_lang}_FLAGS_RELEASE_INIT        "/MT /O2 /Ob2")
  set(CMAKE_${_lang}_FLAGS_RELWITHDEBINFO_INIT "/MT /Zi /O2 /Ob1")
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
