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
find_library(GMP_CXX_LIBRARIES
  NAMES gmpxx
  DOC "GMP C++ libraries"
)

# Try to find headers
find_path(GMP_C_INCLUDES
  NAMES gmp.h
  DOC "GMP C header"
)

find_path(GMP_CXX_INCLUDES
  NAMES gmpxx.h
  DOC "GMP C++ header"
)

# TODO: We should check we can link some simple code against libgmp and libgmpxx

# Handle QUIET and REQUIRED and check the necessary variables were set and if so
# set ``GMP_FOUND``
find_package_handle_standard_args(GMP
	REQUIRED_VARS GMP_C_LIBRARIES GMP_C_INCLUDES GMP_CXX_LIBRARIES GMP_CXX_INCLUDES)

if (GMP_FOUND)
  set(GMP_INCLUDE_DIRS "${GMP_C_INCLUDES}" "${GMP_CXX_INCLUDES}")
  list(REMOVE_DUPLICATES GMP_INCLUDE_DIRS)

  if (NOT TARGET GMP::GMP)
    add_library(GMP::GMP UNKNOWN IMPORTED)
    set_target_properties(GMP::GMP PROPERTIES
      INTERFACE_INCLUDE_DIRECTORIES "${GMP_C_INCLUDES}"
      IMPORTED_LOCATION "${GMP_C_LIBRARIES}")
  endif()
endif()
