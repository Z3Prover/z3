# add_git_dir_dependency(GIT_DIR SUCCESS_VAR)
#
# Adds a configure time dependency on the git directory such that if the HEAD
# of the git directory changes CMake will be forced to re-run. This useful
# for fetching the current git hash and including it in the build.
#
# `GIT_DIR` is the path to the git directory (i.e. the `.git` directory)
# `SUCCESS_VAR` is the name of the variable to set. It will be set to TRUE
# if the dependency was successfully added and FALSE otherwise.
function(add_git_dir_dependency GIT_DIR SUCCESS_VAR)
  if (NOT "${ARGC}" EQUAL 2)
    message(FATAL_ERROR "Invalid number (${ARGC}) of arguments")
  endif()

  if (NOT IS_ABSOLUTE "${GIT_DIR}")
    message(FATAL_ERROR "GIT_DIR (\"${GIT_DIR}\") is not an absolute path")
  endif()

  if (NOT IS_DIRECTORY "${GIT_DIR}")
    message(FATAL_ERROR "GIT_DIR (\"${GIT_DIR}\") is not a directory")
  endif()

  set(GIT_HEAD_FILE "${GIT_DIR}/HEAD")
  if (NOT EXISTS "${GIT_HEAD_FILE}")
    message(AUTHOR_WARNING "Git head file \"${GIT_HEAD_FILE}\" cannot be found")
    set(${SUCCESS_VAR} FALSE PARENT_SCOPE)
    return()
  endif()

  # List of files in the git tree that CMake configuration should depend on
  set(GIT_FILE_DEPS "${GIT_HEAD_FILE}")

  # Examine the HEAD and workout what additional dependencies there are.
  file(READ "${GIT_HEAD_FILE}" GIT_HEAD_DATA LIMIT 128)
  string(STRIP "${GIT_HEAD_DATA}" GIT_HEAD_DATA_STRIPPED)

  if ("${GIT_HEAD_DATA_STRIPPED}" MATCHES "^ref:[ ]*(.+)$")
    # HEAD points at a reference.
    set(GIT_REF "${CMAKE_MATCH_1}")
    if (EXISTS "${GIT_DIR}/${GIT_REF}")
      # Unpacked reference. The file contains the commit hash
      # so add a dependency on this file so that if we stay on this
      # reference (i.e. branch) but change commit CMake will be forced
      # to reconfigure.
      list(APPEND GIT_FILE_DEPS "${GIT_DIR}/${GIT_REF}")
    elseif(EXISTS "${GIT_DIR}/packed-refs")
      # The ref must be packed (see `man git-pack-refs`).
      list(APPEND GIT_FILE_DEPS "${GIT_DIR}/packed-refs")
    else()
      # Fail
      message(AUTHOR_WARNING "Unhandled git reference")
      set(${SUCCESS_VAR} FALSE PARENT_SCOPE)
      return()
    endif()
  else()
    # Detached HEAD.
    # No other dependencies needed
  endif()

  # FIXME:
  # This is the directory we will copy (via `configure_file()`) git files
  # into. This is a hack. It would be better to use the
  # `CMAKE_CONFIGURE_DEPENDS` directory property but that feature is not
  # available in CMake 2.8.12. So we use `configure_file()` to effectively
  # do the same thing. When the source file to `configure_file()` changes
  # it will trigger a re-run of CMake.
  set(GIT_CMAKE_FILES_DIR "${CMAKE_CURRENT_BINARY_DIR}/git_cmake_files")
  file(MAKE_DIRECTORY "${GIT_CMAKE_FILES_DIR}")

  foreach (git_dependency ${GIT_FILE_DEPS})
    message(STATUS "Adding git dependency \"${git_dependency}\"")
    configure_file(
      "${git_dependency}"
      "${GIT_CMAKE_FILES_DIR}"
      COPYONLY
    )
  endforeach()

  set(${SUCCESS_VAR} TRUE PARENT_SCOPE)
endfunction()

# get_git_head_hash(GIT_DIR OUTPUT_VAR)
#
# Retrieve the current commit hash for a git working directory where `GIT_DIR`
# is the `.git` directory in the root of the git working directory.
#
# `OUTPUT_VAR` should be the name of the variable to put the result in. If this
# function fails then either a fatal error will be raised or `OUTPUT_VAR` will
# contain a string with the suffix `NOTFOUND` which can be used in CMake `if()`
# commands.
function(get_git_head_hash GIT_DIR OUTPUT_VAR)
  if (NOT "${ARGC}" EQUAL 2)
    message(FATAL_ERROR "Invalid number of arguments")
  endif()
  if (NOT IS_DIRECTORY "${GIT_DIR}")
    message(FATAL_ERROR "\"${GIT_DIR}\" is not a directory")
  endif()
  if (NOT IS_ABSOLUTE "${GIT_DIR}")
    message(FATAL_ERROR \""${GIT_DIR}\" is not an absolute path")
  endif()
  find_package(Git)
  if (NOT Git_FOUND)
    set(${OUTPUT_VAR} "GIT-NOTFOUND" PARENT_SCOPE)
    return()
  endif()
  get_filename_component(GIT_WORKING_DIR "${GIT_DIR}" DIRECTORY)
  execute_process(
    COMMAND
      "${GIT_EXECUTABLE}"
      "rev-parse"
      "-q" # Quiet
      "HEAD"
    WORKING_DIRECTORY
      "${GIT_WORKING_DIR}"
    RESULT_VARIABLE
      GIT_EXIT_CODE
    OUTPUT_VARIABLE
      Z3_GIT_HASH
    OUTPUT_STRIP_TRAILING_WHITESPACE
  )
  if (NOT "${GIT_EXIT_CODE}" EQUAL 0)
    message(WARNING "Failed to execute git")
    set(${OUTPUT_VAR} NOTFOUND PARENT_SCOPE)
    return()
  endif()
  set(${OUTPUT_VAR} "${Z3_GIT_HASH}" PARENT_SCOPE)
endfunction()

# get_git_head_describe(GIT_DIR OUTPUT_VAR)
#
# Retrieve the output of `git describe` for a git working directory where
# `GIT_DIR` is the `.git` directory in the root of the git working directory.
#
# `OUTPUT_VAR` should be the name of the variable to put the result in. If this
# function fails then either a fatal error will be raised or `OUTPUT_VAR` will
# contain a string with the suffix `NOTFOUND` which can be used in CMake `if()`
# commands.
function(get_git_head_describe GIT_DIR OUTPUT_VAR)
  if (NOT "${ARGC}" EQUAL 2)
    message(FATAL_ERROR "Invalid number of arguments")
  endif()
  if (NOT IS_DIRECTORY "${GIT_DIR}")
    message(FATAL_ERROR "\"${GIT_DIR}\" is not a directory")
  endif()
  if (NOT IS_ABSOLUTE "${GIT_DIR}")
    message(FATAL_ERROR \""${GIT_DIR}\" is not an absolute path")
  endif()
  find_package(Git)
  if (NOT Git_FOUND)
    set(${OUTPUT_VAR} "GIT-NOTFOUND" PARENT_SCOPE)
    return()
  endif()
  get_filename_component(GIT_WORKING_DIR "${GIT_DIR}" DIRECTORY)
  execute_process(
    COMMAND
      "${GIT_EXECUTABLE}"
      "describe"
      "--long"
    WORKING_DIRECTORY
      "${GIT_WORKING_DIR}"
    RESULT_VARIABLE
      GIT_EXIT_CODE
    OUTPUT_VARIABLE
      Z3_GIT_DESCRIPTION
    OUTPUT_STRIP_TRAILING_WHITESPACE
  )
  if (NOT "${GIT_EXIT_CODE}" EQUAL 0)
    message(WARNING "Failed to execute git")
    set(${OUTPUT_VAR} NOTFOUND PARENT_SCOPE)
    return()
  endif()
  set(${OUTPUT_VAR} "${Z3_GIT_DESCRIPTION}" PARENT_SCOPE)
endfunction()
