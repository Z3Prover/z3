# The LINK_FLAGS property of a target in CMake is unfortunately a string and
# not a list. This function takes a list of linker flags and iterates through
# them to append them as strings to the ``LINK_FLAGS`` property of
# the specified target.
# E.g.
# z3_append_linker_flag_list_to_target(mytarget "-fopenmp" "-static")
function(z3_append_linker_flag_list_to_target target)
  if (NOT (TARGET "${target}"))
    message(FATAL_ERROR "Specified target \"${target}\" is not a target")
  endif()
  foreach(flag ${ARGN})
    #message(STATUS "Appending link flag \"${flag}\" to target ${target}")
    # Note that space inside the quoted string is required so that the flags
    # are space separated.
    set_property(TARGET ${target} APPEND_STRING PROPERTY LINK_FLAGS " ${flag}")
  endforeach()
endfunction()
