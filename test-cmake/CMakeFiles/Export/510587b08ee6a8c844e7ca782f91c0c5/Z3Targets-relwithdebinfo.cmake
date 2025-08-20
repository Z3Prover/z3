#----------------------------------------------------------------
# Generated CMake target import file for configuration "RelWithDebInfo".
#----------------------------------------------------------------

# Commands may need to know the format version.
set(CMAKE_IMPORT_FILE_VERSION 1)

# Import target "z3::libz3" for configuration "RelWithDebInfo"
set_property(TARGET z3::libz3 APPEND PROPERTY IMPORTED_CONFIGURATIONS RELWITHDEBINFO)
set_target_properties(z3::libz3 PROPERTIES
  IMPORTED_LOCATION_RELWITHDEBINFO "${_IMPORT_PREFIX}/lib/libz3.so.4.15.4.0"
  IMPORTED_SONAME_RELWITHDEBINFO "libz3.so.4.15"
  )

list(APPEND _cmake_import_check_targets z3::libz3 )
list(APPEND _cmake_import_check_files_for_z3::libz3 "${_IMPORT_PREFIX}/lib/libz3.so.4.15.4.0" )

# Commands beyond this point should not need to know the version.
set(CMAKE_IMPORT_FILE_VERSION)
