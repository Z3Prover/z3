# Tries to find an install of the GNU multiple precision library
#
# Once done this will define
#  GMP_FOUND - BOOL: System has the GMP library installed
#  GMP_INCLUDE_DIR - PATH: The directory containing gmp.h
#  GMP_LIBRARY - FILEPATH: The GMP C library
#  GMP_INCLUDE_DIRS - LIST: The GMP include directories
#  GMP_LIBRARIES - LIST: The libraries needed to use GMP
#  GMP::GMP - TARGET: The GMP C library

include(FindPackageHandleStandardArgs)

# Honor the variables accepted by the previous version of this module.
if (GMP_C_LIBRARIES AND NOT GMP_LIBRARY)
  set(GMP_LIBRARY "${GMP_C_LIBRARIES}")
endif()
if (GMP_C_INCLUDES AND NOT GMP_INCLUDE_DIR)
  set(GMP_INCLUDE_DIR "${GMP_C_INCLUDES}")
endif()

find_library(GMP_LIBRARY
  NAMES gmp
  DOC "GMP C library"
)
find_path(GMP_INCLUDE_DIR
  NAMES gmp.h
  DOC "GMP C header"
)

# Handle QUIET and REQUIRED and check the necessary variables were set and if so
# set ``GMP_FOUND``
find_package_handle_standard_args(GMP
  REQUIRED_VARS GMP_LIBRARY GMP_INCLUDE_DIR)

if (GMP_FOUND)
  set(GMP_INCLUDE_DIRS "${GMP_INCLUDE_DIR}")
  set(GMP_LIBRARIES "${GMP_LIBRARY}")
  set(GMP_C_INCLUDES "${GMP_INCLUDE_DIR}")
  set(GMP_C_LIBRARIES "${GMP_LIBRARY}")

  if (NOT TARGET GMP::GMP)
    add_library(GMP::GMP UNKNOWN IMPORTED)
    set_target_properties(GMP::GMP PROPERTIES
      INTERFACE_INCLUDE_DIRECTORIES "${GMP_INCLUDE_DIR}"
      IMPORTED_LOCATION "${GMP_LIBRARY}")
  endif()
endif()

mark_as_advanced(GMP_INCLUDE_DIR GMP_LIBRARY)
