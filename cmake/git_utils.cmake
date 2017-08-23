# add_git_dir_dependency(GIT_DIR SUCCESS_VAR)
#
# Adds a configure time dependency on the git directory such that if the HEAD
# of the git directory changes CMake will be forced to re-run. This useful
# for fetching the current git hash and including it in the build.
#
# `GIT_DOT_FILE` is the path to the git directory (i.e. the `.git` directory) or
# `.git` file used by a git worktree.
# `SUCCESS_VAR` is the name of the variable to set. It will be set to TRUE
# if the dependency was successfully added and FALSE otherwise.
function(add_git_dir_dependency GIT_DOT_FILE SUCCESS_VAR)
  if (NOT "${ARGC}" EQUAL 2)
    message(FATAL_ERROR "Invalid number (${ARGC}) of arguments")
  endif()

  if (NOT IS_ABSOLUTE "${GIT_DOT_FILE}")
    message(FATAL_ERROR "GIT_DOT_FILE (\"${GIT_DOT_FILE}\") is not an absolute path")
  endif()

  if (NOT EXISTS "${GIT_DOT_FILE}")
    message(FATAL_ERROR "GIT_DOT_FILE (\"${GIT_DOT_FILE}\") does not exist")
  endif()

  if (NOT IS_DIRECTORY "${GIT_DOT_FILE}")
    # Might be a git worktree. In this case we need parse out the worktree
    # git directory
    file(READ "${GIT_DOT_FILE}" GIT_DOT_FILE_DATA LIMIT 512)
    string(STRIP "${GIT_DOT_FILE_DATA}" GIT_DOT_FILE_DATA_STRIPPED)
    if ("${GIT_DOT_FILE_DATA_STRIPPED}" MATCHES "^gitdir:[ ]*(.+)$")
      # Git worktree
      message(STATUS "Found git worktree")
      set(GIT_WORKTREE_DIR "${CMAKE_MATCH_1}")
      set(GIT_HEAD_FILE "${GIT_WORKTREE_DIR}/HEAD")
      # Figure out where real git directory lives
      set(GIT_COMMON_DIR_FILE "${GIT_WORKTREE_DIR}/commondir")
      if (NOT EXISTS "${GIT_COMMON_DIR_FILE}")
        message(FATAL_ERROR "Found git worktree dir but could not find \"${GIT_COMMON_DIR_FILE}\"")
      endif()
      file(READ "${GIT_COMMON_DIR_FILE}" GIT_COMMON_DIR_FILE_DATA LIMIT 512)
      string(STRIP "${GIT_COMMON_DIR_FILE_DATA}" GIT_COMMON_DIR_FILE_DATA_STRIPPED)
      get_filename_component(GIT_DIR "${GIT_WORKTREE_DIR}/${GIT_COMMON_DIR_FILE_DATA_STRIPPED}" ABSOLUTE)
      if (NOT IS_DIRECTORY "${GIT_DIR}")
        message(FATAL_ERROR "Failed to compute path to git directory from git worktree")
      endif()
    else()
      message(FATAL_ERROR "GIT_DOT_FILE (\"${GIT_DOT_FILE}\") is not a directory or a pointer to git worktree directory")
    endif()
  else()
    # Just a normal `.git` directory
    message(STATUS "Found simple git working directory")
    set(GIT_HEAD_FILE "${GIT_DOT_FILE}/HEAD")
    set(GIT_DIR "${GIT_DOT_FILE}")
  endif()
  message(STATUS "Found git directory \"${GIT_DIR}\"")

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

# get_git_head_hash(GIT_DOT_FILE OUTPUT_VAR)
#
# Retrieve the current commit hash for a git working directory where
# `GIT_DOT_FILE` is the `.git` directory or `.git` pointer file in a git
# worktree in the root of the git working directory.
#
# `OUTPUT_VAR` should be the name of the variable to put the result in. If this
# function fails then either a fatal error will be raised or `OUTPUT_VAR` will
# contain a string with the suffix `NOTFOUND` which can be used in CMake `if()`
# commands.
function(get_git_head_hash GIT_DOT_FILE OUTPUT_VAR)
  if (NOT "${ARGC}" EQUAL 2)
    message(FATAL_ERROR "Invalid number of arguments")
  endif()
  if (NOT EXISTS "${GIT_DOT_FILE}")
    message(FATAL_ERROR "\"${GIT_DOT_FILE}\" does not exist")
  endif()
  if (NOT IS_ABSOLUTE "${GIT_DOT_FILE}")
    message(FATAL_ERROR \""${GIT_DOT_FILE}\" is not an absolute path")
  endif()
  find_package(Git)
  # NOTE: Use `GIT_FOUND` rather than `Git_FOUND` which was only
  # available in CMake >= 3.5
  if (NOT GIT_FOUND)
    set(${OUTPUT_VAR} "GIT-NOTFOUND" PARENT_SCOPE)
    return()
  endif()
  get_filename_component(GIT_WORKING_DIR "${GIT_DOT_FILE}" DIRECTORY)
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

# get_git_head_describe(GIT_DOT_FILE OUTPUT_VAR)
#
# Retrieve the output of `git describe` for a git working directory where
# `GIT_DOT_FILE` is the `.git` directory or `.git` pointer file in a git
# worktree in the root of the git working directory.
#
# `OUTPUT_VAR` should be the name of the variable to put the result in. If this
# function fails then either a fatal error will be raised or `OUTPUT_VAR` will
# contain a string with the suffix `NOTFOUND` which can be used in CMake `if()`
# commands.
function(get_git_head_describe GIT_DOT_FILE OUTPUT_VAR)
  if (NOT "${ARGC}" EQUAL 2)
    message(FATAL_ERROR "Invalid number of arguments")
  endif()
  if (NOT EXISTS "${GIT_DOT_FILE}")
    message(FATAL_ERROR "\"${GIT_DOT_FILE}\" does not exist")
  endif()
  if (NOT IS_ABSOLUTE "${GIT_DOT_FILE}")
    message(FATAL_ERROR \""${GIT_DOT_FILE}\" is not an absolute path")
  endif()
  find_package(Git)
  # NOTE: Use `GIT_FOUND` rather than `Git_FOUND` which was only
  # available in CMake >= 3.5
  if (NOT GIT_FOUND)
    set(${OUTPUT_VAR} "GIT-NOTFOUND" PARENT_SCOPE)
    return()
  endif()
  get_filename_component(GIT_WORKING_DIR "${GIT_DOT_FILE}" DIRECTORY)
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
