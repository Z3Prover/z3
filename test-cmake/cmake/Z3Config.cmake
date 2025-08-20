################################################################################
# Automatically generated. DO NOT EDIT
#
# This file is intended to be consumed by clients who wish to use Z3 from CMake.
# It can be used by doing `find_package(Z3 config)` from within a
# `CMakeLists.txt` file. If CMake doesn't find this package automatically you
# can give it a hint by passing `-DZ3_DIR=<path>` to the CMake invocation where
# `<path>` is the path to the directory containing this file.
#
# This file was built for the install tree.
################################################################################


# Handle dependencies (necessary when compiling the static library)
if(NOT ON)
  include(CMakeFindDependencyMacro)

  # Threads::Threads
  set(THREADS_PREFER_PTHREAD_FLAG TRUE)
  find_dependency(Threads)

  # GMP::GMP
  if(OFF)
    find_dependency(GMP)
  endif()
endif()

# Exported targets
include("${CMAKE_CURRENT_LIST_DIR}/Z3Targets.cmake")


####### Expanded from @PACKAGE_INIT@ by configure_package_config_file() #######
####### Any changes to this file will be overwritten by the next CMake run ####
####### The input file was Z3Config.cmake.in                            ########

get_filename_component(PACKAGE_PREFIX_DIR "${CMAKE_CURRENT_LIST_DIR}/../../../" ABSOLUTE)

macro(set_and_check _var _file)
  set(${_var} "${_file}")
  if(NOT EXISTS "${_file}")
    message(FATAL_ERROR "File or directory ${_file} referenced by variable ${_var} does not exist !")
  endif()
endmacro()

macro(check_required_components _NAME)
  foreach(comp ${${_NAME}_FIND_COMPONENTS})
    if(NOT ${_NAME}_${comp}_FOUND)
      if(${_NAME}_FIND_REQUIRED_${comp})
        set(${_NAME}_FOUND FALSE)
      endif()
    endif()
  endforeach()
endmacro()

####################################################################################

# Version information
set(Z3_VERSION_MAJOR 4)
set(Z3_VERSION_MINOR 15)
set(Z3_VERSION_PATCH 4)
set(Z3_VERSION_TWEAK 0)
set(Z3_VERSION_STRING "${Z3_VERSION_MAJOR}.${Z3_VERSION_MINOR}.${Z3_VERSION_PATCH}.${Z3_VERSION_TWEAK}")

# NOTE: We can't use `set_and_check()` here because this a list of paths.
# List of include directories
set(Z3_C_INCLUDE_DIRS ${PACKAGE_PREFIX_DIR}/include )
set(Z3_CXX_INCLUDE_DIRS  ${Z3_C_INCLUDE_DIRS})
# List of libraries to link against
set(Z3_LIBRARIES "z3::libz3")
