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
  # FIXME: should we have -D_DEBUG here to match MSVC build?
  set(CMAKE_${_lang}_FLAGS_DEBUG_INIT "-g -O0")
  set(CMAKE_${_lang}_FLAGS_MINSIZEREL_INIT "-Os")
  set(CMAKE_${_lang}_FLAGS_RELEASE_INIT "-O3")
  set(CMAKE_${_lang}_FLAGS_RELWITHDEBINFO_INIT "-O2 -g")
elseif ("${CMAKE_${_lang}_COMPILER_ID}" MATCHES "MSVC")
  # Not tested!
  set(CMAKE_${_lang}_FLAGS_DEBUG_INIT "/D_DEBUG /MTd /Zi /Ob0 /Od /RTC1")
  set(CMAKE_${_lang}_FLAGS_MINSIZEREL_INIT     "/MT /O1 /Ob1")
  set(CMAKE_${_lang}_FLAGS_RELEASE_INIT        "/MT /O2 /Ob2")
  set(CMAKE_${_lang}_FLAGS_RELWITHDEBINFO_INIT "/MT /Zi /O2 /Ob1")
else()
  message(FATAL_ERROR "Overrides not set for ${_lang} compiler \"${CMAKE_${_lang}_COMPILER_ID}\"")
endif()

unset(_lang)
