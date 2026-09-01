find_package(Git QUIET)

# call_git(OUTPUT_VAR arg1 [arg2 ...])
#
# Runs `git <args>` in `PROJECT_SOURCE_DIR` and stores its trimmed stdout in
# `OUTPUT_VAR`, or `NOTFOUND` if git isn't installed, `PROJECT_SOURCE_DIR`
# isn't a git repo, or the command otherwise failed.
function(call_git OUTPUT_VAR)
  set(${OUTPUT_VAR} NOTFOUND PARENT_SCOPE)
  if (NOT Git_FOUND)
    return()
  endif()
  execute_process(
    COMMAND "${GIT_EXECUTABLE}" ${ARGN}
    WORKING_DIRECTORY "${PROJECT_SOURCE_DIR}"
    RESULT_VARIABLE git_exit_code
    OUTPUT_VARIABLE git_output
    OUTPUT_STRIP_TRAILING_WHITESPACE
    ERROR_QUIET
  )
  if (git_exit_code EQUAL 0)
    set(${OUTPUT_VAR} "${git_output}" PARENT_SCOPE)
  endif()
endfunction()

# add_git_dir_dependency(SUCCESS_VAR)
#
# Makes the CMake configure step depend on the current git HEAD (i.e. the
# checked out branch and its commit) of `PROJECT_SOURCE_DIR` so that
# switching branches or making a new commit forces CMake to reconfigure.
#
# `SUCCESS_VAR` is set to TRUE if the dependency was added and FALSE
# otherwise (e.g. git isn't installed or `PROJECT_SOURCE_DIR` isn't a git
# repo).
function(add_git_dir_dependency SUCCESS_VAR)
  set(${SUCCESS_VAR} FALSE PARENT_SCOPE)
  # `HEAD` changes when checking out a different branch or, while detached,
  # a different commit. `logs/HEAD` (the reflog) additionally changes on
  # every commit, but only if reflogs are enabled (the default, but not
  # always the case). The ref that `HEAD` points at (e.g. `refs/heads/main`)
  # changes on every commit regardless of reflog settings, so track that
  # too when `HEAD` is not detached.
  set(git_paths HEAD logs/HEAD)
  call_git(git_head_ref rev-parse --symbolic-full-name HEAD)
  if (git_head_ref)
    list(APPEND git_paths "${git_head_ref}")
  endif()

  foreach (git_path ${git_paths})
    call_git(git_path_output rev-parse --git-path "${git_path}")
    if (git_path_output)
      # `--git-path` prints a path relative to PROJECT_SOURCE_DIR normally,
      # but an absolute path when the real git dir lives elsewhere (e.g. a
      # linked worktree's git dir lives under the main repo's `.git`).
      get_filename_component(git_abs_path "${git_path_output}" ABSOLUTE
                             BASE_DIR "${PROJECT_SOURCE_DIR}")
      if (EXISTS "${git_abs_path}")
        set_property(DIRECTORY "${PROJECT_SOURCE_DIR}"
                     APPEND PROPERTY CMAKE_CONFIGURE_DEPENDS "${git_abs_path}")
        set(${SUCCESS_VAR} TRUE PARENT_SCOPE)
      endif()
    endif()
  endforeach()
endfunction()
