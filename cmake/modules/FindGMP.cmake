# Tries to find an install of the GNU multiple precision library
#
# Once done this will define
#  GMP_FOUND - BOOL: System has the GMP library installed
#  GMP_INCLUDE_DIRS - LIST:The GMP include directories
#  GMP_C_LIBRARIES - LIST:The libraries needed to use GMP via it's C interface
#  GMP_CXX_LIBRARIES - LIST:The libraries needed to use GMP via it's C++ interface

include(FindPackageHandleStandardArgs)

# Try to find libraries
find_library(GMP_C_LIBRARIES
  NAMES gmp
  DOC "GMP C libraries"
)
if (GMP_C_LIBRARIES)
  message(STATUS "Found GMP C library: \"${GMP_C_LIBRARIES}\"")
else()
  message(STATUS "Could not find GMP C library")
endif()
find_library(GMP_CXX_LIBRARIES
  NAMES gmpxx
  DOC "GMP C++ libraries"
)
if (GMP_CXX_LIBRARIES)
  message(STATUS "Found GMP C++ library: \"${GMP_CXX_LIBRARIES}\"")
else()
  message(STATUS "Could not find GMP C++ library")
endif()

# Try to find headers
find_path(GMP_C_INCLUDES
  NAMES gmp.h
  DOC "GMP C header"
)
if (GMP_C_INCLUDES)
  message(STATUS "Found GMP C include path: \"${GMP_C_INCLUDES}\"")
else()
  message(STATUS "Could not find GMP C include path")
endif()

find_path(GMP_CXX_INCLUDES
  NAMES gmpxx.h
  DOC "GMP C++ header"
)
if (GMP_CXX_INCLUDES)
  message(STATUS "Found GMP C++ include path: \"${GMP_CXX_INCLUDES}\"")
else()
  message(STATUS "Could not find GMP C++ include path")
endif()

if (GMP_C_LIBRARIES AND GMP_CXX_LIBRARIES AND GMP_C_INCLUDES AND GMP_CXX_INCLUDES)
  set(GMP_INCLUDE_DIRS "${GMP_C_INCLUDES}" "${GMP_CXX_INCLUDES}")
  list(REMOVE_DUPLICATES GMP_INCLUDE_DIRS)
  message(STATUS "Found GMP")
else()
  message(STATUS "Could not find GMP")
endif()

# TODO: We should check we can link some simple code against libgmp and libgmpxx

# Handle QUIET and REQUIRED and check the necessary variables were set and if so
# set ``GMP_FOUND``
find_package_handle_standard_args(GMP DEFAULT_MSG GMP_INCLUDE_DIRS GMP_C_LIBRARIES GMP_CXX_LIBRARIES)
