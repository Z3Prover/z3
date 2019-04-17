################################################################################
# Compiler warning flags
################################################################################
# These are passed to relevant compiler provided they are supported
set(GCC_AND_CLANG_WARNINGS
  "-Wall"
)
set(GCC_ONLY_WARNINGS "")
set(CLANG_ONLY_WARNINGS "")
set(MSVC_WARNINGS "/W3")

################################################################################
# Serious warnings
################################################################################
# This declares the flags that are passed to the compiler when
# `WARNINGS_AS_ERRORS` is set to `SERIOUS_ONLY`. Only flags that are supported
# by the compiler are used.
#
# In effect this a "whitelist" approach where we explicitly tell the compiler
# which warnings we want to be treated as errors. The alternative would be a
# "blacklist" approach where we ask the compiler to treat all warnings are
# treated as errors but then we explicitly list which warnings which should be
# allowed.
#
# The "whitelist" approach seems simpiler because we can incrementally add
# warnings we "think are serious".

# TODO: Add more warnings that are considered serious enough that we should
# treat them as errors.
set(GCC_AND_CLANG_WARNINGS_AS_ERRORS
  # https://clang.llvm.org/docs/DiagnosticsReference.html#wodr
  "-Werror=odr"
)
set(GCC_WARNINGS_AS_ERRORS
  ""
)
set(CLANG_WARNINGS_AS_ERRORS
  # https://clang.llvm.org/docs/DiagnosticsReference.html#wdelete-non-virtual-dtor
  "-Werror=delete-non-virtual-dtor"
  # https://clang.llvm.org/docs/DiagnosticsReference.html#woverloaded-virtual
  "-Werror=overloaded-virtual"
)

################################################################################
# Test warning/error flags
################################################################################
set(WARNING_FLAGS_TO_CHECK "")
set(WARNING_AS_ERROR_FLAGS_TO_CHECK "")
if ("${CMAKE_CXX_COMPILER_ID}" MATCHES "GNU")
  list(APPEND WARNING_FLAGS_TO_CHECK ${GCC_AND_CLANG_WARNINGS})
  list(APPEND WARNING_FLAGS_TO_CHECK ${GCC_ONLY_WARNINGS})
  list(APPEND WARNING_AS_ERROR_FLAGS_TO_CHECK ${GCC_AND_CLANG_WARNINGS_AS_ERRORS})
  list(APPEND WARNING_AS_ERROR_FLAGS_TO_CHECK ${GCC_WARNINGS_AS_ERRORS})
elseif ("${CMAKE_CXX_COMPILER_ID}" MATCHES "Clang")
  list(APPEND WARNING_FLAGS_TO_CHECK ${GCC_AND_CLANG_WARNINGS})
  list(APPEND WARNING_FLAGS_TO_CHECK ${CLANG_ONLY_WARNINGS})
  list(APPEND WARNING_AS_ERROR_FLAGS_TO_CHECK ${GCC_AND_CLANG_WARNINGS_AS_ERRORS})
  list(APPEND WARNING_AS_ERROR_FLAGS_TO_CHECK ${CLANG_WARNINGS_AS_ERRORS})
elseif ("${CMAKE_CXX_COMPILER_ID}" STREQUAL "MSVC")
  list(APPEND WARNING_FLAGS_TO_CHECK ${MSVC_WARNINGS})

  # CMake's default flags include /W3 already so remove them if
  # they already exist.
  if ("${CMAKE_CXX_FLAGS}" MATCHES "/W3")
    string(REPLACE "/W3" "" _cmake_cxx_flags_remove_w3 "${CMAKE_CXX_FLAGS}")
    set(CMAKE_CXX_FLAGS "${_cmake_cxx_flags_remove_w3}" CACHE STRING "" FORCE)
  endif()
else()
  message(AUTHOR_WARNING "Unknown compiler")
endif()

# Loop through flags and use the ones which the compiler supports
foreach (flag ${WARNING_FLAGS_TO_CHECK})
  z3_add_cxx_flag("${flag}")
endforeach()

# TODO: Remove this eventually.
# Detect legacy `WARNINGS_AS_ERRORS` boolean option and covert to new
# to new option type.
get_property(
  WARNINGS_AS_ERRORS_CACHE_VAR_TYPE
  CACHE
  WARNINGS_AS_ERRORS
  PROPERTY
  TYPE
)
if ("${WARNINGS_AS_ERRORS_CACHE_VAR_TYPE}" STREQUAL "BOOL")
  message(WARNING "Detected legacy WARNINGS_AS_ERRORS option. Upgrading")
  set(WARNINGS_AS_ERRORS_DEFAULT "${WARNINGS_AS_ERRORS}")
  # Delete old entry
  unset(WARNINGS_AS_ERRORS CACHE)
else()
  set(WARNINGS_AS_ERRORS_DEFAULT "SERIOUS_ONLY")
endif()

set(WARNINGS_AS_ERRORS
  ${WARNINGS_AS_ERRORS_DEFAULT}
  CACHE STRING
  "Treat warnings as errors. ON, OFF, or SERIOUS_ONLY"
)
 # Set GUI options
set_property(
  CACHE
  WARNINGS_AS_ERRORS
  PROPERTY STRINGS
  "ON;OFF;SERIOUS_ONLY"
)

if ("${WARNINGS_AS_ERRORS}" STREQUAL "ON")
  message(STATUS "Treating compiler warnings as errors")
  if (("${CMAKE_CXX_COMPILER_ID}" MATCHES "Clang") OR ("${CMAKE_CXX_COMPILER_ID}" MATCHES "GNU"))
    list(APPEND Z3_COMPONENT_CXX_FLAGS "-Werror")
  elseif ("${CMAKE_CXX_COMPILER_ID}" STREQUAL "MSVC")
    list(APPEND Z3_COMPONENT_CXX_FLAGS "/WX")
  else()
    message(AUTHOR_WARNING "Unknown compiler")
  endif()
elseif ("${WARNINGS_AS_ERRORS}" STREQUAL "SERIOUS_ONLY")
  message(STATUS "Treating only serious compiler warnings as errors")
  # Loop through the flags
  foreach (flag ${WARNING_AS_ERROR_FLAGS_TO_CHECK})
    # Add globally because some flags need to be passed at link time.
    z3_add_cxx_flag("${flag}" GLOBAL)
  endforeach()
elseif ("${WARNINGS_AS_ERRORS}" STREQUAL "OFF")
  message(STATUS "Not treating compiler warnings as errors")
  if ("${CMAKE_CXX_COMPILER_ID}" STREQUAL "MSVC")
    # Warnings as errors is off by default for MSVC so setting this
    # is not necessary but this duplicates the behaviour of the old
    # build system.
    list(APPEND Z3_COMPONENT_CXX_FLAGS "/WX-")
  endif()
else()
  message(FATAL_ERROR
    "WARNINGS_AS_ERRORS set to unsupported value \"${WARNINGS_AS_ERRORS}\""
  )
endif()
